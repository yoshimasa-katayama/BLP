# Setup
rm(list = ls())
set.seed(1)
setwd("/Users/yoshimasa/Dropbox/Replication/Katayama/BLP")

# Library
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

# Data
data <- readMat("data/100markets3products.mat")                # Import data
X1_mat <- t(matrix(data[["x1"]][, 1], nrow = J, ncol = M))     # 1st product characteristics
X2_mat <- t(matrix(data[["x1"]][, 2], nrow = J, ncol = M))     # 2nd product characteristics
X3_mat <- t(matrix(data[["x1"]][, 3], nrow = J, ncol = M))     # 3rd product characteristics
price_mat <- t(data[["P.opt"]])                                # Price
share_mat <- t(data[["shares"]])                               # Share
share_outside_mat <- 1 - rowSums(share_mat)                    # Share of outside options
xi_mat <- t(matrix(data[["xi.all"]], nrow = J, ncol = M))      # xi
w_mat <- t(matrix(data[["w"]], nrow = J, ncol = M))            # Cost shifters
eta_mat <- t(matrix(data[["eta"]], nrow = J, ncol = M))        # eta
Z_mat <- t(matrix(data[["Z"]], nrow = J, ncol = M))            # Z
alphas_mat <- data[["alphas"]]                                 # alphas
delta_true_mat <- theta1_true[1] * X1_mat + theta1_true[2] * X2_mat + theta1_true[3] * X3_mat - theta1_true[4] * price_mat + xi_mat      # True delta
mc_true_mat <- theta2_true[1] + theta2_true[2] * w_mat + theta2_true[3] * Z_mat + eta_mat                                                # True mc

# Simulate nu
# nu_sim <- alphas - 1
u_halton <- as.vector(ghalton(n = R, d = 1))
nu_sim <- matrix(qlnorm(u_halton, meanlog = 0, sdlog = 1), nrow = M, ncol = R, byrow = TRUE)

# Import estimates
estimates <- readRDS("output/estimates.rds")
theta1_hat <- estimates[["theta1_hat"]]
theta2_hat <- estimates[["theta2_hat"]]
theta3_hat <- estimates[["theta3_hat"]]
xi_mat_hat <- t(matrix(estimates[["xi_hat"]], nrow = J, ncol = M)) 
mc_mat_hat <- t(matrix(estimates[["mc_hat"]], nrow = J, ncol = M)) 

# Compute delta
compute_delta <- function(theta1, x1, x2, x3, price, xi) {
  theta1[1] * x1 + theta1[2] * x2 + theta1[3] * x3 - theta1[4] * price + xi
}

# Compute share
compute_share <- function(theta1, theta3, x1, x2, x3, price, xi, nu) {
  
  # nu, delta, price
  nu_mat <- matrix(nu, nrow = J, ncol = R, byrow = TRUE)
  delta_mat <- matrix(compute_delta(theta1, x1, x2, x3, price, xi), nrow = J, ncol = R, byrow = FALSE)
  price_mat <- matrix(price, nrow = J, ncol = R, byrow = FALSE)
  
  # Utility
  util <- delta_mat - theta3 * price_mat * nu_mat
  
  # Numerator and denominator
  numerator <- exp(util)
  denominator <- 1 + colSums(numerator)
  
  # Share
  share_mat <- numerator / matrix(denominator, nrow = J, ncol = R, byrow = TRUE)
  
  # Return
  rowMeans(share_mat)
}

# Compute derivatives of share with respect to price
compute_share_derivative <- function(theta1, theta3, x1, x2, x3, price, xi, nu) {
  
  # nu, delta, price
  nu_mat <- matrix(nu, nrow = J, ncol = R, byrow = TRUE)
  delta_mat <- matrix(compute_delta(theta1, x1, x2, x3, price, xi), nrow = J, ncol = R, byrow = FALSE)
  price_mat <- matrix(price, nrow = J, ncol = R, byrow = FALSE)
  
  # Utility
  util <- delta_mat - theta3 * price_mat * nu_mat
  
  # Numerator and denominator
  numerator <- exp(util)
  denominator <- 1 + colSums(numerator)
  
  # Share
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

# FOCs when firm 3 price is fixed
foc_fixed <- function(p12, theta1, theta3, x1, x2, x3, p3, xi, mc, nu) {
  
  # Counterfactual prices
  price_cf <- c(p12, p3)
  
  # Counterfactual shares
  share_cf <- compute_share(theta1, theta3, x1, x2, x3, price_cf, xi, nu)
  
  # Counterfactual share derivatives
  deriv_cf <- compute_share_derivative(theta1, theta3, x1, x2, x3, price_cf, xi, nu)
  
  # FOCs
  as.vector(share_cf[1:2] + deriv_cf[1:2, 1:2] %*% (p12 - mc[1:2]))
  
}

# FOCs when firm 3 adjusts prices
foc_variable <- function(p, theta1, theta3, x1, x2, x3, xi, mc, nu) {
  
  # Counterfactual shares and share derivatives
  share_cf <- compute_share(theta1, theta3, x1, x2, x3, p, xi, nu)
  deriv_cf <- compute_share_derivative(theta1, theta3, x1, x2, x3, p, xi, nu)
  
  # FOCs for merged firm
  foc1 <- share_cf[1] + deriv_cf[1,1] * (p[1] - mc[1]) + deriv_cf[1,2] * (p[2] - mc[2])
  foc2 <- share_cf[2] + deriv_cf[2,1] * (p[1] - mc[1]) + deriv_cf[2,2] * (p[2] - mc[2])
  
  # FOCs for firm 3
  foc3 <- share_cf[3] + deriv_cf[3,3] * (p[3] - mc[3])
  
  # Return
  c(foc1, foc2, foc3)
}

# Solve counterfactual prices market by market
solve_merger_price <- function(theta1, theta3, X1_mat, X2_mat, X3_mat, price_mat, xi_mat, mc_mat, nu_sim) {
  
  # Counterfactual prices and shares
  price_mat_fixed <- matrix(NA, nrow = M, ncol = J)
  price_mat_variable <- matrix(NA, nrow = M, ncol = J)
  share_mat_fixed <- matrix(NA, nrow = M, ncol = J)
  share_mat_variable <- matrix(NA, nrow = M, ncol = J)
  
  # Fill in matrix
  for (m in 1:M) {
    
    # Product characteristics, price, xi, mc, nu in market m
    x1 <- X1_mat[m, ]
    x2 <- X2_mat[m, ]
    x3 <- X3_mat[m, ]
    price <- price_mat[m, ]
    xi <- xi_mat[m, ]
    mc <- mc_mat[m, ]
    nu <- nu_sim[m, ]
    
    # Objective function when firm 3 price is fixed
    obj_fixed <- function(p12) {
      foc <- foc_fixed(p12, theta1, theta3, x1, x2, x3, price[3], xi, mc, nu)
      sum(foc^2)
    }
    
    # Solve FOCs
    solve_fixed <- optim(par=price[1:2], fn=obj_fixed, method="L-BFGS-B", lower=c(0, 0), upper=c(Inf, Inf), control=list(fnscale=1, maxit=200000))
    
    # Price and shares
    price_mat_fixed[m, ] <- c(solve_fixed$par[1], solve_fixed$par[2], price[3])
    share_mat_fixed[m, ] <- compute_share(theta1, theta3, x1, x2, x3, c(solve_fixed$par[1], solve_fixed$par[2], price[3]), xi, nu)
    
    # Objective function when firm 3 adjusts prices
    obj_variable <- function(p) {
      foc <- foc_variable(p, theta1, theta3, x1, x2, x3, xi, mc, nu)
      sum(foc^2)
    }
    
    # Solve FOCs
    solve_variable <- optim(par=price, fn=obj_variable, method="L-BFGS-B", lower=c(0, 0, 0), upper=c(Inf, Inf, Inf), control=list(fnscale=1, maxit=200000))
    
    # Prices and shares
    price_mat_variable[m, ] <- solve_variable$par
    share_mat_variable[m, ] <- compute_share(theta1, theta3, x1, x2, x3, solve_variable$par, xi, nu)
  }
  
  # Return
  list(price_mat_fixed = price_mat_fixed, share_mat_fixed = share_mat_fixed, price_mat_variable = price_mat_variable, share_mat_variable = share_mat_variable)
}

# Compute expected CS
compute_cs <- function(theta1, theta3, x1, x2, x3, price, xi, nu) {
  
  delta_mat <- matrix(compute_delta(theta1, x1, x2, x3, price, xi), nrow = J, ncol = R, byrow = FALSE)
  price_mat <- matrix(price, nrow = J, ncol = R, byrow = FALSE)
  nu_mat    <- matrix(nu, nrow = J, ncol = R, byrow = TRUE)
  
  util <- delta_mat - theta3 * price_mat * nu_mat
  
  # expected CS conditional on simulated nu draws
  mean(log(1 + colSums(exp(util))))
}

# Summarize outcomes
summarize_outcome <- function(theta1, theta3, X1_mat, X2_mat, X3_mat, price_mat, xi_mat, mc_mat, nu_sim, share_mat) {
  
  # Markups and profits
  markup_mat <- price_mat - mc_mat
  profit_mat <- markup_mat * share_mat
  
  # CS
  cs <- numeric(M)
  for (m in 1:M) {
    cs[m] <- compute_cs(theta1, theta3, X1_mat[m, ], X2_mat[m, ], X3_mat[m, ], price_mat[m, ], xi_mat[m, ], nu_sim[m, ])
  }
  
  # Return
  list(mean_price = colMeans(price_mat), mean_share = colMeans(share_mat), mean_mc = colMeans(mc_mat), mean_markup = colMeans(markup_mat), total_profit = colSums(profit_mat), total_cs = sum(cs))
}

# Post-merger prices and shares
out_solve_merger_price <- solve_merger_price(theta1_hat, theta3_hat, X1_mat, X2_mat, X3_mat, price_mat, xi_mat_hat, mc_mat_hat, nu_sim)

# Pre-merger summary
summarize_pre <- summarize_outcome(theta1_hat, theta3_hat, X1_mat, X2_mat, X3_mat, price_mat, xi_mat_hat, mc_mat_hat, nu_sim, share_mat)

# Post-merger summary when firm 3 price is fixed
summarize_post_fixed <- summarize_outcome(theta1_hat, theta3_hat, X1_mat, X2_mat, X3_mat, out_solve_merger_price[["price_mat_fixed"]], xi_mat_hat, mc_mat_hat, nu_sim, out_solve_merger_price[["share_mat_fixed"]])

# Post-merger summary when firm 3 adjusts prices
summarize_post_variable <- summarize_outcome(theta1_hat, theta3_hat, X1_mat, X2_mat, X3_mat, out_solve_merger_price[["price_mat_variable"]], xi_mat_hat, mc_mat_hat, nu_sim, out_solve_merger_price[["share_mat_variable"]])

# Output: mean price
cat(sprintf("Mean price (pre-merger): %s\n", paste(sprintf("%.5f", summarize_pre[["mean_price"]]), collapse = ", ")))
cat(sprintf("Mean price (post-merger, fixed): %s\n", paste(sprintf("%.5f", summarize_post_fixed[["mean_price"]]), collapse = ", ")))
cat(sprintf("Mean price (post-merger, variable): %s\n", paste(sprintf("%.5f", summarize_post_variable[["mean_price"]]), collapse = ", ")))

# Output: mean markup
cat(sprintf("Mean markup (pre-merger): %s\n", paste(sprintf("%.5f", summarize_pre[["mean_markup"]]), collapse = ", ")))
cat(sprintf("Mean markup (post-merger, fixed): %s\n", paste(sprintf("%.5f", summarize_post_fixed[["mean_markup"]]), collapse = ", ")))
cat(sprintf("Mean markup (post-merger, variable): %s\n", paste(sprintf("%.5f", summarize_post_variable[["mean_markup"]]), collapse = ", ")))

# Output: mean share
cat(sprintf("Mean share (pre-merger): %s\n", paste(sprintf("%.5f", summarize_pre[["mean_share"]]), collapse = ", ")))
cat(sprintf("Mean share (post-merger, fixed): %s\n", paste(sprintf("%.5f", summarize_post_fixed[["mean_share"]]), collapse = ", ")))
cat(sprintf("Mean share (post-merger, variable): %s\n", paste(sprintf("%.5f", summarize_post_variable[["mean_share"]]), collapse = ", ")))

# Output: total profit
cat(sprintf("Total profits (pre-merger): %s\n", paste(sprintf("%.5f", summarize_pre[["total_profit"]]), collapse = ", ")))
cat(sprintf("Total profits (post-merger, fixed): %s\n", paste(sprintf("%.5f", summarize_post_fixed[["total_profit"]]), collapse = ", ")))
cat(sprintf("Total profits (post-merger, variable): %s\n", paste(sprintf("%.5f", summarize_post_variable[["total_profit"]]), collapse = ", ")))

# Output: total CS
cat(sprintf("Total CS (pre-merger): %.5f\n", summarize_pre[["total_cs"]]))
cat(sprintf("Total CS (post-merger, fixed): %.5f\n", summarize_post_fixed[["total_cs"]]))
cat(sprintf("Total CS (post-merger, variable): %.5f\n", summarize_post_variable[["total_cs"]]))











