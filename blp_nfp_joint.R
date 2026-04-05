# Setup
rm(list = ls())
set.seed(1)

# Library
library(numDeriv)
library(R.matlab)
library(qrng)

# Constants
M <- 100                                  # Number of markets
J <- 3                                    # Number of products
R <- 500                                  # Number of consumers in each market
N <- M * J                                # Number of observations
theta1_true <- c(5, 1, 1, 1)              # True parameter values (beta1, beta2, beta3, alpha)
theta2_true <- c(2, 1, 1)                 # True parameter values (gamma0, gamma1, gamma2)
theta3_true <- 1                          # True parameter values (sigma_alpha)
W <- diag(12)                             # Identity weight matrix

# Data
data <- readMat("data/100markets3products.mat")            # Import data
X1 <- t(matrix(data[["x1"]][, 1], nrow = J, ncol = M))     # 1st product characteristics
X2 <- t(matrix(data[["x1"]][, 2], nrow = J, ncol = M))     # 2nd product characteristics
X3 <- t(matrix(data[["x1"]][, 3], nrow = J, ncol = M))     # 3rd product characteristics
price <- t(data[["P.opt"]])                                # Price
share <- t(data[["shares"]])                               # Share
share_outside <- 1 - rowSums(share)                        # Share of outside options
xi <- t(matrix(data[["xi.all"]], nrow = J, ncol = M))      # xi
w <- t(matrix(data[["w"]], nrow = J, ncol = M))            # Cost shifters
eta <- t(matrix(data[["eta"]], nrow = J, ncol = M))        # eta
Z <- t(matrix(data[["Z"]], nrow = J, ncol = M))            # Z
alphas <- data[["alphas"]]                                 # alphas
delta_true <- theta1_true[1] * X1 + theta1_true[2] * X2 + theta1_true[3] * X3 - theta1_true[4] * price + xi      # True delta
mc_true <- theta2_true[1] + theta2_true[2] * w + theta2_true[3] * Z + eta                                        # True mc

# Instruments
IV1 <- X1
IV2 <- X2
IV3 <- X3
IV4 <- rowSums(X2) - X2
IV5 <- rowSums(X3) - X3
IV6 <- w

# Simulate nu
# nu_sim <- alphas - 1
u_halton <- as.vector(ghalton(n = R, d = 1))
nu_sim <- matrix(qlnorm(u_halton, meanlog = 0, sdlog = 1), nrow = M, ncol = R, byrow = TRUE)

# Dataframe
df <- data.frame(
  market        = rep(1:M, each = J),
  product       = rep(1:J, times = M),
  share         = as.vector(t(share)),
  share_outside = rep(share_outside, each = J),
  price         = as.vector(t(price)),
  X1            = as.vector(t(X1)),
  X2            = as.vector(t(X2)),
  X3            = as.vector(t(X3)),
  xi            = as.vector(t(xi)),
  w             = as.vector(t(w)),
  eta           = as.vector(t(eta)),
  Z             = as.vector(t(Z)),
  IV1           = as.vector(t(IV1)),
  IV2           = as.vector(t(IV2)),
  IV3           = as.vector(t(IV3)),
  IV4           = as.vector(t(IV4)),
  IV5           = as.vector(t(IV5)),
  IV6           = as.vector(t(IV6)),
  delta_true    = as.vector(t(delta_true)),
  mc_true       = as.vector(t(mc_true))
)

# Correlation
cat(sprintf("Correlation between xi and IV1: %.5f\n", mean(df$xi * df$IV1)))
cat(sprintf("Correlation between xi and IV2: %.5f\n", mean(df$xi * df$IV2)))
cat(sprintf("Correlation between xi and IV3: %.5f\n", mean(df$xi * df$IV3)))
cat(sprintf("Correlation between xi and IV4: %.5f\n", mean(df$xi * df$IV4)))
cat(sprintf("Correlation between xi and IV5: %.5f\n", mean(df$xi * df$IV5)))
cat(sprintf("Correlation between xi and IV6: %.5f\n", mean(df$xi * df$IV6)))

cat(sprintf("Correlation between eta and IV1: %.5f\n", mean(df$eta * df$IV1)))
cat(sprintf("Correlation between eta and IV2: %.5f\n", mean(df$eta * df$IV2)))
cat(sprintf("Correlation between eta and IV3: %.5f\n", mean(df$eta * df$IV3)))
cat(sprintf("Correlation between eta and IV4: %.5f\n", mean(df$eta * df$IV4)))
cat(sprintf("Correlation between eta and IV5: %.5f\n", mean(df$eta * df$IV5)))
cat(sprintf("Correlation between eta and IV6: %.5f\n", mean(df$eta * df$IV6)))

# Compute shares given delta
compute_share <- function(theta3, df, delta, nu_sim) {
  
  # Shares
  share_hat <- numeric(nrow(df))
  
  for (m in unique(df$market)) {
    
    # Obtain delta and price for each market
    id <- which(df$market == m)
    delta_id <- delta[id]
    price_id <- df$price[id]
    
    # nu
    nu_id <- matrix(nu_sim[m, ], nrow = J, ncol = R, byrow = TRUE)
    
    # Compute utility (JxR matrix)
    util <- matrix(delta_id, nrow = J, ncol = R, byrow = FALSE) - theta3 * matrix(price_id, nrow = J, ncol = R, byrow = FALSE) * nu_id
    
    # Numerator and denominator
    numerator <- exp(util)
    denominator <- 1 + colSums(numerator)
    
    # Compute share in market m
    share_id <- numerator / matrix(denominator, nrow = J, ncol = R, byrow = TRUE)
    
    # Fill in share
    share_hat[id] <- rowMeans(share_id)
    
  }
  
  # Return
  return(share_hat)
}

# Difference between actual and predicted shares
max(abs(df$share - compute_share(theta3_true, df, df$delta_true, nu_sim)))

# Contraction mapping
solve_delta <- function(theta3, df, nu_sim) {
  
  # Initial value
  delta_old <- log(df$share) - log(df$share_outside)
  distance <- 100
  
  # Contraction mapping
  while (distance > 1e-12) {
    share_hat <- compute_share(theta3, df, delta_old, nu_sim)
    delta_new <- delta_old + log(df$share) - log(share_hat)
    distance <- max(abs(delta_new - delta_old))
    delta_old <- delta_new
  }
  
  # Return
  return(delta_new)
}

# Difference between actual and predicted delta
max(abs(df$delta_true - solve_delta(theta3_true, df, nu_sim)))

# Demand IV regression
regress_demand_iv <- function(df, delta) {
  
  # Y, X, and Z
  Y <- delta
  X <- cbind(df$X1, df$X2, df$X3, -df$price)
  IV <- cbind(df$IV1, df$IV2, df$IV3, df$IV4, df$IV5, df$IV6)
  
  # Inverse matrix
  inv_IV <- solve(t(IV) %*% IV)
  P_IV <- IV %*% inv_IV %*% t(IV)
  
  # Estimate
  theta1_hat <- solve(t(X) %*% P_IV %*% X) %*% (t(X) %*% P_IV %*% Y)
  theta1_hat <- as.vector(theta1_hat)
  
  # Return
  return(theta1_hat)
}

# Difference between actual and predicted parameters
max(abs(theta1_true - regress_demand_iv(df, df$delta_true)))
regress_demand_iv(df, df$delta_true)

# Compute xi
compute_xi <- function(theta3, df, nu_sim) {
  
  # Solve delta
  delta_hat <- solve_delta(theta3, df, nu_sim)
  
  # Estimate theta1
  theta1_hat <- regress_demand_iv(df, delta_hat)
  
  # Compute xi
  xi_hat <- delta_hat - theta1_hat[1] * df$X1 - theta1_hat[2] * df$X2 - theta1_hat[3] * df$X3 + theta1_hat[4] * df$price
  
  # Return
  list(delta_hat = delta_hat, theta1_hat = theta1_hat, xi_hat = xi_hat)
}

# Difference between actual and predicted xi
max(abs(df$xi - compute_xi(theta3_true, df, nu_sim)[["xi_hat"]]))

# Compute derivatives of share with respect to price in a given market to obtain marginal costs
compute_share_derivatives <- function(theta1, theta3, delta, price, nu) {
  
  # JxR matrices
  nu_mat <- matrix(nu, nrow = J, ncol = R, byrow = TRUE)
  delta_mat <- matrix(delta, nrow = J, ncol = R, byrow = FALSE)
  price_mat <- matrix(price, nrow = J, ncol = R, byrow = FALSE)
  
  # Utility
  util <- delta_mat - theta3 * price_mat * nu_mat
  
  # Numerator and denominator
  numerator <- exp(util)
  denominator <- 1 + colSums(numerator)
  
  # Share in a give market
  share_mat <- numerator / matrix(denominator, nrow = J, ncol = R, byrow = TRUE)
  
  # JxJ matrix
  deriv_mat <- matrix(0, nrow = J, ncol = J)
  
  # Fill in matrix
  for (r in 1:R) {
    share_r <- share_mat[, r]
    alpha_r <- theta1[4] + theta3 * nu[r]
    
    for (j in 1:J) {
      for (k in 1:J) {
        if (j == k) {
          deriv_mat[j, k] <- deriv_mat[j, k] - alpha_r * share_r[j] * (1 - share_r[j]) / R
        } else {
          deriv_mat[j, k] <- deriv_mat[j, k] + alpha_r * share_r[j] * share_r[k] / R
        }
      }
    }
  }
  
  # Return
  return(deriv_mat)
}

# Compute marginal costs
compute_mc <- function(theta3, df, nu_sim, conduct = c("pc", "oligopoly", "monopoly")) {
  
  # Conduct
  conduct <- match.arg(conduct)
  
  # Obtain delta_hat and theta1_hat
  out_compute_xi <- compute_xi(theta3, df, nu_sim)
  delta_hat <- out_compute_xi[["delta_hat"]]
  theta1_hat <- out_compute_xi[["theta1_hat"]]
  
  # Vector with length N
  mc_hat <- numeric(N)
  
  # Fill in vector
  for (m in unique(df$market)) {
    id <- which(df$market == m)
    delta_id <- delta_hat[id]
    price_id <- df$price[id]
    share_id <- df$share[id]
    nu_id <- nu_sim[m, ]
    
    # Compute share derivatives
    deriv_mat <- compute_share_derivatives(theta1_hat, theta3, delta_id, price_id, nu_id)
    
    if (conduct == "pc") {
      mc_hat[id] <- price_id
    } else if (conduct == "oligopoly") {
      markup_id <- share_id / diag(deriv_mat)
      mc_hat[id] <- price_id + markup_id
    } else if (conduct == "monopoly") {
      markup_id <- solve(deriv_mat, share_id)
      mc_hat[id] <- price_id + markup_id
    }
  }
  
  # Return
  return(mc_hat)
}

# Compute marginal costs
compute_mc(theta3_true, df, nu_sim, "pc")
compute_mc(theta3_true, df, nu_sim, "oligopoly")
compute_mc(theta3_true, df, nu_sim, "monopoly")
max(abs(df$mc_true - compute_mc(theta3_true, df, nu_sim, "oligopoly")))

# Supply IV regression
regress_supply_iv <- function(df, mc) {
  
  # Y, X, and IV
  Y <- mc
  X <- cbind(1, df$w, df$Z)
  IV <- cbind(df$IV1, df$IV2, df$IV3, df$IV4, df$IV5, df$IV6)
  
  # Inverse matrix
  inv_IV <- solve(t(IV) %*% IV)
  P_IV <- IV %*% inv_IV %*% t(IV)
  
  # Estimate
  theta2_hat <- solve(t(X) %*% P_IV %*% X) %*% (t(X) %*% P_IV %*% Y)
  theta2_hat <- as.vector(theta2_hat)
  
  # Return
  return(theta2_hat)
}

# Predicted parameters
max(abs(theta2_true - regress_supply_iv(df, df$mc_true)))
regress_supply_iv(df, df$mc_true)

# Compute eta
compute_eta <- function(theta3, df, nu_sim, conduct = c("pc", "oligopoly", "monopoly")) {
  
  # Conduct
  conduct <- match.arg(conduct)
  
  # Compute marginal costs
  mc_hat <- compute_mc(theta3, df, nu_sim, conduct)
  
  # Compute theta2_hat
  theta2_hat <- regress_supply_iv(df, mc_hat)
  
  # Compute eta_hat
  eta_hat <- mc_hat - theta2_hat[1] - theta2_hat[2] * df$w - theta2_hat[3] * df$Z
  
  # Return
  list(mc_hat = mc_hat, theta2_hat = theta2_hat, eta_hat = eta_hat)
}

# Difference between actual and predicted eta
max(abs(df$eta - compute_eta(theta3_true, df, nu_sim, "oligopoly")[["eta_hat"]]))

# Compute moment
compute_moment <- function(theta3, df, nu_sim, conduct = c("pc", "oligopoly", "monopoly")) {
  
  # Conduct
  conduct <- match.arg(conduct)
  
  # Compute xi_hat
  xi_hat <- compute_xi(theta3, df, nu_sim)[["xi_hat"]]
  
  # Compute eta_hat
  eta_hat <- compute_eta(theta3, df, nu_sim, conduct)[["eta_hat"]]
  
  # Instruments
  IV <- cbind(df$IV1, df$IV2, df$IV3, df$IV4, df$IV5, df$IV6)
  
  # Compute moments
  moment_demand <- (t(IV) %*% xi_hat) / N
  moment_supply <- (t(IV) %*% eta_hat) / N
  
  # Return
  rbind(moment_demand, moment_supply)
}

# Difference between actual and predicted moments
max(abs(c(mean(df$xi * df$IV1), mean(df$xi * df$IV2), mean(df$xi * df$IV3), mean(df$xi * df$IV4), mean(df$xi * df$IV5), mean(df$xi * df$IV6),
          mean(df$eta * df$IV1), mean(df$eta * df$IV2), mean(df$eta * df$IV3), mean(df$eta * df$IV4), mean(df$eta * df$IV5), mean(df$eta * df$IV6)) - compute_moment(theta3_true, df, nu_sim, "oligopoly")))

# Compute GMM objective function
GMM_obj <- function(theta3, df, nu_sim, W, conduct = c("pc", "oligopoly", "monopoly")) {
  
  # Conduct
  conduct <- match.arg(conduct)
  
  # Compute moments
  moment <- compute_moment(theta3, df, nu_sim, conduct)
  
  # Objective
  as.numeric(t(moment) %*% W %*% moment)
}

# GMM objective function at true values
GMM_obj(theta3_true, df, nu_sim, W, "oligopoly")

# Perfect competition: optimization with identity weighting matrix
gmm_fit_pc <- optim(par=5, GMM_obj, method="L-BFGS-B", lower=0, upper=Inf,
                    df=df, nu_sim=nu_sim, W=W, conduct="pc",
                    control=list(fnscale = 1, maxit  = 200000, trace = 1, REPORT = 1), 
                    hessian=FALSE)

# Perfect competition: estimated parameters
gmm_fit_pc$par
compute_xi(gmm_fit_pc$par, df, nu_sim)[["theta1_hat"]]
compute_eta(gmm_fit_pc$par, df, nu_sim, "pc")[["theta2_hat"]]

# Oligopoly: optimization with identity weighting matrix
gmm_fit_oligopoly <- optim(par=5, GMM_obj, method="L-BFGS-B", lower=0, upper=Inf,
                           df=df, nu_sim=nu_sim, W=W, conduct="oligopoly",
                           control=list(fnscale = 1, maxit  = 200000, trace = 1, REPORT = 1), 
                           hessian=FALSE)

# Oligopoly: estimated parameters
gmm_fit_oligopoly$par
compute_xi(gmm_fit_oligopoly$par, df, nu_sim)[["theta1_hat"]]
compute_eta(gmm_fit_oligopoly$par, df, nu_sim, "oligopoly")[["theta2_hat"]]

# Monopoly: optimization with identity weighting matrix
gmm_fit_monopoly <- optim(par=5, GMM_obj, method="L-BFGS-B", lower=0, upper=Inf,
                          df=df, nu_sim=nu_sim, W=W, conduct="monopoly",
                          control=list(fnscale = 1, maxit  = 200000, trace = 1, REPORT = 1), 
                          hessian=FALSE)

# Monopoly: estimated parameters
gmm_fit_monopoly$par
compute_xi(gmm_fit_monopoly$par, df, nu_sim)[["theta1_hat"]]
compute_eta(gmm_fit_monopoly$par, df, nu_sim, "monopoly")[["theta2_hat"]]

# Compute optimal weighting matrix
compute_optimal_weight <- function(theta3, df, nu_sim, conduct = c("pc", "oligopoly", "monopoly")) {
  
  # Conduct
  conduct <- match.arg(conduct)
  
  # Compute xi_hat
  xi_hat <- compute_xi(theta3, df, nu_sim)[["xi_hat"]]
  
  # Compute eta_hat
  eta_hat <- compute_eta(theta3, df, nu_sim, conduct)[["eta_hat"]]
  
  # Instruments
  IV <- cbind(df$IV1, df$IV2, df$IV3, df$IV4, df$IV5, df$IV6)

  # Return
  solve(crossprod(cbind(IV * xi_hat, IV * eta_hat)) / N)
}

# Compute optimal weighting matrix
W_opt_pc <- compute_optimal_weight(gmm_fit_pc$par, df, nu_sim, "pc")
W_opt_oligopoly <- compute_optimal_weight(gmm_fit_oligopoly$par, df, nu_sim, "oligopoly")
W_opt_monopoly <- compute_optimal_weight(gmm_fit_monopoly$par, df, nu_sim, "monopoly")

# Perfect competition: optimization with optimal weighting matrix
gmm_fit_opt_pc <- optim(par=gmm_fit_pc$par, GMM_obj, method="L-BFGS-B", lower=0, upper=Inf,
                        df=df, nu_sim=nu_sim, W=W_opt_pc, conduct="pc",
                        control=list(fnscale = 1, maxit  = 200000, trace = 1, REPORT = 1), 
                        hessian=FALSE)

# Perfect competition: estimated parameters
gmm_fit_opt_pc$par
compute_xi(gmm_fit_opt_pc$par, df, nu_sim)[["theta1_hat"]]
compute_eta(gmm_fit_opt_pc$par, df, nu_sim, "pc")[["theta2_hat"]]

# Oligopoly: optimization with optimal weighting matrix
gmm_fit_opt_oligopoly <- optim(par=gmm_fit_oligopoly$par, GMM_obj, method="L-BFGS-B", lower=0, upper=Inf,
                               df=df, nu_sim=nu_sim, W=W_opt_oligopoly, conduct="oligopoly",
                               control=list(fnscale = 1, maxit  = 200000, trace = 1, REPORT = 1), 
                               hessian=FALSE)

# Oligopoly: estimated parameters
theta3_hat <- gmm_fit_opt_oligopoly$par
out_compute_xi <- compute_xi(gmm_fit_opt_oligopoly$par, df, nu_sim)
out_compute_eta <- compute_eta(gmm_fit_opt_oligopoly$par, df, nu_sim, "oligopoly")
theta3_hat
out_compute_xi[["theta1_hat"]]
out_compute_eta[["theta2_hat"]]

# Save estimates
saveRDS(list(theta1_hat = out_compute_xi[["theta1_hat"]], theta2_hat = out_compute_eta[["theta2_hat"]], theta3_hat = theta3_hat,
             xi_hat = out_compute_xi[["xi_hat"]], mc_hat = out_compute_eta[["mc_hat"]]), file = "output/estimates.rds")

# Monopoly: optimization with optimal weighting matrix
gmm_fit_opt_monopoly <- optim(par=gmm_fit_monopoly$par, GMM_obj, method="L-BFGS-B", lower=0, upper=Inf,
                              df=df, nu_sim=nu_sim, W=W_opt_monopoly, conduct="monopoly",
                              control=list(fnscale = 1, maxit  = 200000, trace = 1, REPORT = 1), 
                              hessian=FALSE)

# Monopoly: estimated parameters
gmm_fit_opt_monopoly$par
compute_xi(gmm_fit_opt_monopoly$par, df, nu_sim)[["theta1_hat"]]
compute_eta(gmm_fit_opt_monopoly$par, df, nu_sim, "monopoly")[["theta2_hat"]]

# Compute SE of sigma_alpha
compute_se_sigma_alpha <- function(theta3, df, nu_sim, W_opt, conduct = c("pc", "oligopoly", "monopoly")) {
  
  # Conduct
  conduct <- match.arg(conduct)
  
  # Jacobian of moment
  G <- numDeriv::jacobian(func = compute_moment, x = theta3, df = df, nu_sim = nu_sim, conduct = conduct)
  
  # Asymptotic variance-covariance matrix
  V_sigma <- solve(t(G) %*% W_opt %*% G) / N
  
  # Return
  list(se_sigma = sqrt(diag(V_sigma)), V_sigma = V_sigma)
}

# Compute SE of sigma_alpha
compute_se_sigma_alpha(gmm_fit_opt_pc$par, df, nu_sim, W_opt_pc, "pc")[["se_sigma"]]
compute_se_sigma_alpha(gmm_fit_opt_oligopoly$par, df, nu_sim, W_opt_oligopoly, "oligopoly")[["se_sigma"]]
compute_se_sigma_alpha(gmm_fit_opt_monopoly$par, df, nu_sim, W_opt_monopoly, "monopoly")[["se_sigma"]]

# Write theta1 and theta2 as a function of sigma_alpha
theta12_of_sigma <- function(theta3, df, nu_sim, conduct = c("pc", "oligopoly", "monopoly")) {
  
  # Conduct
  conduct <- match.arg(conduct)
  
  # theta1_hat
  theta1_hat <- compute_xi(theta3, df, nu_sim)[["theta1_hat"]]
  
  # theta2_hat
  theta2_hat <- compute_eta(theta3, df, nu_sim, conduct)[["theta2_hat"]]
  
  # Return
  c(theta1_hat, theta2_hat)
}

# Compute SE of theta1 and theta2
compute_se_theta12 <- function(theta3, df, nu_sim, W_opt, conduct = c("pc", "oligopoly", "monopoly")) {
  
  # Conduct
  conduct <- match.arg(conduct)
  
  # Obtain Var of sigma_alpha
  V_sigma <- compute_se_sigma_alpha(theta3, df, nu_sim, W_opt, conduct)[["V_sigma"]]
  
  # Jacobian
  H <- numDeriv::jacobian(func = theta12_of_sigma, x = theta3, df = df, nu_sim = nu_sim, conduct = conduct)
  
  # Delta method
  V_theta12 <- H %*% V_sigma %*% t(H)
  se_theta12 <- sqrt(diag(V_theta12))
  
  # Return
  return(se_theta12)
}

# Compute SE of theta1 and theta2 (needs to be fixed)
compute_se_theta12(gmm_fit_opt_pc$par, df, nu_sim, W_opt_pc, "pc")
compute_se_theta12(gmm_fit_opt_oligopoly$par, df, nu_sim, W_opt_oligopoly, "oligopoly")
compute_se_theta12(gmm_fit_opt_monopoly$par, df, nu_sim, W_opt_monopoly, "monopoly")







