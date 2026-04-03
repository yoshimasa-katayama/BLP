# Setup
rm(list = ls())
set.seed(1)
setwd("/Users/yoshimasa/Dropbox/Replication/Katayama/BLP")

# Library
library(numDeriv)
library(R.matlab)
library(qrng)

# Constants
M <- 100                          # Number of markets
J <- 3                            # Number of products
R <- 500                          # Number of consumers in each market
N <- M * J                        # Number of observations
nparams <- 5                      # Number of parameters    
params1_true <- c(5, 1, 1, 1)     # True parameter values (beta1, beta2, beta3, alpha)
params2_true <- 1                 # True parameter values (sigma_alpha)
W <- diag(5)                      # Identity weight matrix

# Data
data <- readMat("data/100markets3products.mat")            # Import data
X1 <- t(matrix(data[["x1"]][, 1], nrow = J, ncol = M))     # 1st product characteristics
X2 <- t(matrix(data[["x1"]][, 2], nrow = J, ncol = M))     # 2nd product characteristics
X3 <- t(matrix(data[["x1"]][, 3], nrow = J, ncol = M))     # 3rd product characteristics
price <- t(data[["P.opt"]])                                # Price
share <- t(data[["shares"]])                               # Share
share_outside <- 1 - rowSums(share)                        # Share of outside options
xi <- t(matrix(data[["xi.all"]], nrow = J, ncol = M))      # xi
alphas <- data[["alphas"]]                                 # alphas
Z4 <- rowSums(X2) - X2                                     # Instruments
Z5 <- rowSums(X3) - X3                                     # Instruments
delta_true <- params1_true[1] * X1 + params1_true[2] * X2 + params1_true[3] * X3 - params1_true[4] * price + xi      # True delta

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
  Z1            = as.vector(t(X1)),
  Z2            = as.vector(t(X2)),
  Z3            = as.vector(t(X3)),
  Z4            = as.vector(t(Z4)),
  Z5            = as.vector(t(Z5)),
  xi            = as.vector(t(xi)),
  delta_true    = as.vector(t(delta_true))
)

# Correlation
cat(sprintf("Correlation between xi and Z1: %.5f\n", mean(df$xi * df$Z1)))
cat(sprintf("Correlation between xi and Z2: %.5f\n", mean(df$xi * df$Z2)))
cat(sprintf("Correlation between xi and Z3: %.5f\n", mean(df$xi * df$Z3)))
cat(sprintf("Correlation between xi and Z4: %.5f\n", mean(df$xi * df$Z4)))
cat(sprintf("Correlation between xi and Z5: %.5f\n", mean(df$xi * df$Z5)))
cat(sprintf("Correlation between xi and price: %.5f\n", mean(df$xi * df$price)))

# Compute shares given delta
compute_share <- function(params2, df, delta, nu_sim) {
  
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
    util <- matrix(delta_id, nrow = J, ncol = R, byrow = FALSE) - params2 * matrix(price_id, nrow = J, ncol = R, byrow = FALSE) * nu_id
    
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
max(abs(df$share - compute_share(params2_true, df, df$delta_true, nu_sim)))

# Contraction mapping
solve_delta <- function(params2, df, nu_sim) {
  
  # Initial value
  delta_old <- log(df$share) - log(df$share_outside)
  distance <- 100
  
  # Contraction mapping
  while (distance > 1e-12) {
    share_hat <- compute_share(params2, df, delta_old, nu_sim)
    delta_new <- delta_old + log(df$share) - log(share_hat)
    distance <- max(abs(delta_new - delta_old))
    delta_old <- delta_new
  }
  
  # Return
  return(delta_new)
}

# Difference between actual and predicted delta
max(abs(df$delta_true - solve_delta(params2_true, df, nu_sim)))

# IV regression
regress_iv <- function(df, delta) {
  
  # Y, X, and Z
  Y <- delta
  X <- cbind(df$X1, df$X2, df$X3, -df$price)
  Z <- cbind(df$Z1, df$Z2, df$Z3, df$Z4, df$Z5)
  
  # Inverse matrix
  inv_Z <- solve(t(Z) %*% Z)
  P_Z <- Z %*% inv_Z %*% t(Z)
  
  # Estimate
  theta_hat <- solve(t(X) %*% P_Z %*% X) %*% (t(X) %*% P_Z %*% Y)
  theta_hat <- as.vector(theta_hat)
  
  # Return
  return(theta_hat)
}

# Difference between actual and predicted parameters
max(abs(params1_true - regress_iv(df, df$delta_true)))

# Compute xi
compute_xi <- function(params2, df, nu_sim) {
  
  # Solve delta
  delta_hat <- solve_delta(params2, df, nu_sim)
  
  # Esimate theta1
  theta1_hat <- regress_iv(df, delta_hat)
  
  # Compute xi
  xi_hat <- delta_hat - theta1_hat[1] * df$X1 - theta1_hat[2] * df$X2 - theta1_hat[3] * df$X3 + theta1_hat[4] * df$price
    
  # Return
  list(delta_hat = delta_hat, theta1_hat = theta1_hat, xi_hat = xi_hat)
}

# Difference between actual and predicted xi
max(abs(df$xi - compute_xi(params2_true, df, nu_sim)[["xi_hat"]]))

# Compute moments
compute_moment <- function(params2, df, nu_sim) {
  
  # Compute xi
  xi_hat <- compute_xi(params2, df, nu_sim)[["xi_hat"]]
  
  # Instruments
  Z <- cbind(df$Z1, df$Z2, df$Z3, df$Z4, df$Z5)
  
  # Compute moments
  (t(Z) %*% xi_hat) / N
}

# Difference between actual and predicted moments
max(abs(c(mean(df$xi * df$Z1), mean(df$xi * df$Z2), mean(df$xi * df$Z3), mean(df$xi * df$Z4), mean(df$xi * df$Z5)) - compute_moment(params2_true, df, nu_sim)))

# Compute GMM objective function
GMM_obj <- function(params2, df, nu_sim, W) {
  
  # Compute moments
  moment <- compute_moment(params2, df, nu_sim)
  
  # Objective
  as.numeric(t(moment) %*% W %*% moment)
}

# GMM objective function at true values
GMM_obj(params2_true, df, nu_sim, W)

# Optimization with identity weighting matrix
gmm_fit <- optim(par=5, GMM_obj, method="L-BFGS-B", lower=0, upper=Inf,
                 df=df, nu_sim=nu_sim, W=W,
                 control=list(fnscale = 1, maxit  = 200000, trace = 1, REPORT = 1), 
                 hessian=FALSE)

# Estimated parameters
gmm_fit$par
compute_xi(gmm_fit$par, df, nu_sim)[["theta1_hat"]]

# Compute optimal weighting matrix
compute_optimal_weight <- function(params2, df, nu_sim) {
   
  # Compute xi
  xi_hat <- compute_xi(params2, df, nu_sim)[["xi_hat"]]
  
  # Instruments
  Z <- cbind(df$Z1, df$Z2, df$Z3, df$Z4, df$Z5)
  
  # Optimal weighting matrix
  solve(crossprod(Z * xi_hat) / N)
}

# Compute optimal weighting matrix
W_opt <- compute_optimal_weight(gmm_fit$par, df, nu_sim)

# Optimization with optimal weighting matrix
gmm_fit_opt <- optim(par=gmm_fit$par, GMM_obj, method="L-BFGS-B", lower=0, upper=Inf,
                 df=df, nu_sim=nu_sim, W=W_opt,
                 control=list(fnscale = 1, maxit  = 200000, trace = 1, REPORT = 1), 
                 hessian=FALSE)

# Estimated parameters
gmm_fit_opt$par
compute_xi(gmm_fit_opt$par, df, nu_sim)[["theta1_hat"]]

# Compute SE of sigma_alpha
compute_se_sigma_alpha <- function(params2, df, nu_sim, W_opt) {
  
  # Jacobian of moment
  G <- numDeriv::jacobian(func = compute_moment, x = params2, df = df, nu_sim = nu_sim)
  
  # Asymptotic variance
  V_sigma <- solve(t(G) %*% W_opt %*% G) / N
  
  # Return
  list(se_sigma = sqrt(diag(V_sigma)), V_sigma = V_sigma)
}

# Compute SE of sigma_alpha
compute_se_sigma_alpha(gmm_fit_opt$par, df, nu_sim, W_opt)[["se_sigma"]]

# Write theta1 as a function of sigma_alpha
theta1_of_sigma <- function(params2, df, nu_sim) {
  compute_xi(params2, df, nu_sim)[["theta1_hat"]]
}

# Compute SE of theta1
compute_se_theta1 <- function(params2, df, nu_sim, W_opt) {
  
  # Obtain Var of sigma_alpha
  V_sigma <- compute_se_sigma_alpha(params2, df, nu_sim, W_opt)[["V_sigma"]]
  
  # Jacobian
  H <- numDeriv::jacobian(func = theta1_of_sigma, x = params2, df = df, nu_sim = nu_sim)
  
  # Delta method
  V_theta1 <- H %*% V_sigma %*% t(H)
  se_theta1 <- sqrt(diag(V_theta1))
  
  # Return
  return(se_theta1)
}

# Compute SE of theta1
compute_se_theta1(gmm_fit_opt$par, df, nu_sim, W_opt)
