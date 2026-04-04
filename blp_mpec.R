# References:
# Dube, Fox, and Su (2012) “Supplement to ‘Improving the Numerical Performance of Static and Dynamic Aggregate Discrete Choice Random Coefficients Demand Estimation’,” Econometrica Supplemental Material.
# https://www.jp-dube.com/research/MPECcode.html

# Setup
rm(list = ls())
set.seed(1)

# Library
library(ipoptr)
library(R.matlab)
library(qrng)

# Constants
M <- 100              # Number of markets
J <- 3                # Number of products
R <- 500              # Number of consumers in each market
N <- M * J            # Number of observations
K <- 5                # Number of structural parameters (beta1, beta2, beta3, alpha, sigma_alpha)
L <- 5                # Number of instruments
sigma_alpha0 <- 3     # Initial guess of sigma_alpha

# Data
data <- readMat("data/100markets3products.mat")              # Import data
X1   <- t(matrix(data[["x1"]][, 1], nrow = J, ncol = M))     # 1st product characteristics
X2   <- t(matrix(data[["x1"]][, 2], nrow = J, ncol = M))     # 2nd product characteristics
X3   <- t(matrix(data[["x1"]][, 3], nrow = J, ncol = M))     # 3rd product characteristics
P    <- t(data[["P.opt"]])                                   # Price
S    <- t(data[["shares"]])                                  # Share
S0   <- 1 - rowSums(S)                                       # Share of outside options

# Instruments
IV4 <- rowSums(X2) - X2
IV5 <- rowSums(X3) - X3

# Vectorization
market  <- rep(1:M, each = J)
product <- rep(1:J, times = M)
x1      <- as.vector(t(X1))
x2      <- as.vector(t(X2))
x3      <- as.vector(t(X3))
p       <- as.vector(t(P))
s       <- as.vector(t(S))
s0      <- rep(S0, each = J)
iv4     <- as.vector(t(IV4))
iv5     <- as.vector(t(IV5))

# Instruments
IV <- cbind(x1, x2, x3, iv4, iv5)

# Quasi-random draws for lognormal individual price taste
u_halton <- as.vector(ghalton(n = R, d = 1))
nu_sim   <- matrix(qlnorm(u_halton, meanlog = 0, sdlog = 1), nrow = M, ncol = R, byrow = TRUE)

# Minimize objective function over x = (theta, xi, g)
index_theta <- 1:K
index_xi    <- (K + 1):(K + N)
index_g     <- (K + N + 1):(K + N + L)

# ipoptr does not take Jacobian and Hessian as matrices
# It takes a vector of nonzero elements for Jacobian and a vectorized lower triangular matrix for Hessian
# Convert symmetric matrix to a vectorized lower triangular matrix
matrix_to_lower_triangular_vector <- function(M) {
  unlist(lapply(seq_len(nrow(M)), function(i) M[i, seq_len(i)]), use.names = FALSE)
}

# Compute shares and jacobians w.r.t theta and xi
compute_share_and_jacobian <- function(theta, xi) {
  
  # Shares
  s_hat <- numeric(N)
  
  # Jacobian of shares w.r.t. theta and xi, and individual choice probability
  jac_theta_list <- vector("list", M)     # J x K x M
  jac_xi_list    <- vector("list", M)     # J x J x M
  T_list         <- vector("list", M)     # J x R x M
  
  # Compute shares and jacobians in each market
  for (m in unique(market)) {
    
    id   <- which(market == m)
    x1_m <- x1[id]
    x2_m <- x2[id]
    x3_m <- x3[id]
    p_m  <- p[id]
    xi_m <- xi[id]
    nu_m <- nu_sim[m, ]
    
    # Compute mean utility
    delta_m <- as.vector(theta[1] * x1_m + theta[2] * x2_m + theta[3] * x3_m - theta[4] * p_m + xi_m)
    
    # Compute individual utility
    util <- matrix(delta_m, nrow = J, ncol = R, byrow = FALSE) - theta[5] * matrix(p_m, nrow = J, ncol = R, byrow = FALSE) * matrix(nu_m, nrow = J, ncol = R, byrow = TRUE)
    
    # Compute individual choice probability
    numerator   <- exp(util)
    denominator <- 1 + colSums(numerator)
    T_m <- numerator / matrix(denominator, nrow = J, ncol = R, byrow = TRUE)
    
    # Fill
    s_hat[id]   <- rowMeans(T_m)
    T_list[[m]] <- T_m
    
    # Compute jacobians
    jac_theta_m <- matrix(0, nrow = J, ncol = K)
    jac_xi_m    <- matrix(0, nrow = J, ncol = J)
    
    for (r in 1:R) {
      # Jacobian of individual choice probability w.r.t. individual utility
      T_r <- T_m[, r]
      A_r <- diag(T_r) - tcrossprod(T_r, T_r)
      
      # Jacobian of individual utility w.r.t theta and xi
      D_r <- cbind(x1_m, x2_m, x3_m, -p_m, -p_m * nu_m[r], diag(J))
      
      # Jacobian of individual choice probability w.r.t. theta and xi
      jac_r       <- A_r %*% D_r
      jac_theta_m <- jac_theta_m + jac_r[, 1:K, drop = FALSE] / R
      jac_xi_m    <- jac_xi_m + jac_r[, (K + 1):(K + J), drop = FALSE] / R
    }
    
    # Fill
    jac_theta_list[[m]] <- jac_theta_m
    jac_xi_list[[m]]    <- jac_xi_m
  }
  
  # Return
  list(s_hat = s_hat, jac_theta_list = jac_theta_list, jac_xi_list = jac_xi_list, T_list = T_list)
}

# Objective function
eval_f <- function(x) {
  g <- x[index_g]
  as.numeric(t(g) %*% W %*% g)
}

# Gradient of objective function
eval_grad_f <- function(x) {
  g <- x[index_g]
  c(rep(0, K + N), as.vector(2 * W %*% g))
}

# Constraints
eval_g <- function(x) {
  
  # Arguments
  theta <- x[index_theta]
  xi    <- x[index_xi]
  g     <- x[index_g]
  
  # Shares
  s_hat <- compute_share_and_jacobian(theta, xi)[["s_hat"]]
  
  # Constraints
  c(s_hat - s, g - as.vector((t(IV) %*% xi) / N))
}

# Sparsity structures of constraint jacobian
jac_structure <- vector("list", N + L)     # Column numbers with nonzero element for (N + L) rows, (N + L) is the number of constraints

# Shares in a market depends on theta and xi in the market, but not depend on xi in the other markets nor g
for (m in unique(market)) {
  id <- which(market == m)
  for (j in 1:J) {
    row_index <- id[j]
    jac_structure[[row_index]] <- c(index_theta, K + id)
  }
}

# l-th moment condition depends on g[l] and all xi, but not depends on theta nor g[k] for k \neq l
for (l in 1:L) {
  jac_structure[[N + l]] <- c(index_xi, K + N + l)
}

# Jacobian of constraints
eval_jac_g <- function(x) {
  
  # Arguments
  theta <- x[index_theta]
  xi    <- x[index_xi]
  
  # Jacobian of shares w.r.t. theta and xi
  out_compute_share_and_jacobian <- compute_share_and_jacobian(theta, xi)
  
  # Nonzero values for each row
  jac_g_list <- vector("list", N + L)
  
  # Jacobian of shares
  for (m in unique(market)) {
    id <- which(market == m)
    jac_theta_m <- out_compute_share_and_jacobian$jac_theta_list[[m]]
    jac_xi_m    <- out_compute_share_and_jacobian$jac_xi_list[[m]]
    
    for (j in 1:J) {
      row_index <- id[j]
      jac_g_list[[row_index]] <- c(jac_theta_m[j, ], jac_xi_m[j, ])
    }
  }
  
  # Jacobian of moment conditions
  for (l in 1:L) {
    jac_g_list[[N + l]] <- c(-IV[, l] / N, 1)
  }
  
  # Return
  unlist(jac_g_list, use.names = FALSE)
}

# Sparsity patters of Lagrangian hessian (lower triangular matrix since hessian is symmetric)
hess_structure <- lapply(1:(K + N + L), function(i) seq_len(i))

# Hessian of Lagrangian
eval_h <- function(x, obj_factor, hessian_lambda) {
  
  # Arguments
  theta <- x[index_theta]
  xi    <- x[index_xi]
  
  # Only share constraints have nonzero values since moment constraints are linear in xi and g
  lambda_share <- hessian_lambda[1:N]
  
  # Hessian matrix
  H <- matrix(0, nrow = (K + N + L), ncol = (K + N + L))
  
  # Individual choice probabilities
  T_list <- compute_share_and_jacobian(theta, xi)[["T_list"]]
  
  # Compute hessian in each market given independence across markets
  for (m in unique(market)) {
    id       <- which(market == m)
    x1_m     <- x1[id]
    x2_m     <- x2[id]
    x3_m     <- x3[id]
    p_m      <- p[id]
    nu_m     <- nu_sim[m, ]
    T_m      <- T_list[[m]]
    lambda_m <- lambda_share[id]
    
    index_m  <- c(index_theta, K + id)
    H_m      <- matrix(0, nrow = K + J, ncol = K + J)
    
    # Compute second-order derivatives for each consumer
    for (r in 1:R) {
      T_r   <- T_m[, r]
      phi_r <- sum(lambda_m * T_r)
      q_r   <- T_r * (lambda_m - phi_r)
      
      H_U_r <- diag(q_r) - tcrossprod(T_r, q_r) - tcrossprod(q_r, T_r)
      
      D_r <- cbind(x1_m, x2_m, x3_m, -p_m, -p_m * nu_m[r], diag(J))
      
      H_m <- H_m + t(D_r) %*% H_U_r %*% D_r / R
    }
    
    H[index_m, index_m] <- H[index_m, index_m] + H_m
  }
  
  H[index_g, index_g] <- H[index_g, index_g] + obj_factor * (2 * W)
  
  matrix_to_lower_triangular_vector(H)
}

# Contraction mapping and IV regression to obtain internally consistent start values given sigma_alpha
# Compute shares given sigma_alpha and delta
x0_compute_share <- function(sigma_alpha, delta) {
  
  # Shares
  s_hat <- numeric(N)
  
  # Compute shares in each markes
  for (m in unique(market)) {
    id      <- which(market == m)
    delta_m <- delta[id]
    p_m     <- p[id]
    nu_m    <- nu_sim[m, ]
    
    # individual utility
    util <- matrix(delta_m, nrow = J, ncol = R, byrow = FALSE) - sigma_alpha * matrix(p_m, nrow = J, ncol = R, byrow = FALSE) * matrix(nu_m, nrow = J, ncol = R, byrow = TRUE)
    
    # Individual choice probability
    numerator <- exp(util)
    denominator <- 1 + colSums(numerator)
    s_hat[id] <- rowMeans(numerator / matrix(denominator, nrow = J, ncol = R, byrow = TRUE))
  }
  
  # Return
  s_hat
}

# Contraction mapping to obtain delta given sigma_alpha
x0_solve_delta <- function(sigma_alpha, tol = 1e-12, maxit = 200000) {
  
  # Initial guess of delta
  delta_old <- log(s) - log(s0)
  distance  <- Inf
  iter      <- 0
  
  # Contraction mapping
  while (distance > tol && iter < maxit) {
    s_hat     <- x0_compute_share(sigma_alpha, delta_old)
    delta_new <- delta_old + log(s) - log(s_hat)
    distance  <- max(abs(delta_new - delta_old))
    delta_old <- delta_new
    iter      <- iter + 1
  }
  
  # Return
  return(delta_old)
}

# IV regression to obtain theta_hat given delta
x0_IV_regression <- function(delta) {
  X <- cbind(x1, x2, x3, -p)
  inv_IV <- solve(t(IV) %*% IV)
  P_IV <- IV %*% inv_IV %*% t(IV)
  theta_hat <- solve(t(X) %*% P_IV %*% X) %*% (t(X) %*% P_IV %*% delta)
  theta_hat <- as.vector(theta_hat)
  return(theta_hat)
}

# Start values for x = (theta, xi, g) given sigma_alpha
x0_start_value <- function(sigma_alpha) {
  
  # Compute delta_hat
  delta_hat <- x0_solve_delta(sigma_alpha)
  
  # Compute theta_hat
  theta_hat <- x0_IV_regression(delta_hat)
  
  # Compute xi_hat
  xi_hat <- delta_hat - theta_hat[1] * x1 - theta_hat[2] * x2 - theta_hat[3] * x3 + theta_hat[4] * p
  
  # Compute g_hat
  g_hat <- as.vector((t(IV) %*% xi_hat) / N)
  
  # Return
  c(theta_hat, sigma_alpha, xi_hat, g_hat)
}

# Initial guess of x
x0 <- x0_start_value(sigma_alpha0)

# Weighting matrix
W <- solve(t(IV) %*% IV)

# Solve optimization problem
solve_mpec <- ipoptr(x0 = x0, eval_f = eval_f, eval_grad_f = eval_grad_f, lb = rep(-1.0e19, K + N + L), ub = rep(1.0e19, K + N + L),
                     eval_g = eval_g, eval_jac_g = eval_jac_g, eval_jac_g_structure = jac_structure,
                     constraint_lb = rep(0, N + L), constraint_ub = rep(0, N + L),
                     eval_h = eval_h, eval_h_structure = hess_structure,
                     opts = list(print_level = 5, max_iter = 200000, tol = 1e-8, constr_viol_tol = 1e-8, compl_inf_tol = 1e-8, dual_inf_tol = 1e-8, linear_solver = "mumps"))

# Solution
solve_mpec$solution[index_theta]

# Compute SEs
# Compute jacobian of delta w.r.t sigma_alpha
compute_jacobian_delta_sigma_alpha <- function(sigma_alpha, delta) {
  
  # Jacobian of share w.r.t delta and sigma_alpha
  jac_sigma_alpha <- numeric(N)
  jac_delta       <- matrix(0, nrow = N, ncol = N)
  
  for (m in unique(market)) {
    id <- which(market == m)
    p_m <- p[id]
    delta_m <- delta[id]
    nu_m <- nu_sim[m, ]
    
    # Individual utility
    util <- matrix(delta_m, nrow = J, ncol = R, byrow = FALSE) - sigma_alpha * matrix(p_m, nrow = J, ncol = R, byrow = FALSE) * matrix(nu_m, nrow = J, ncol = R, byrow = TRUE)
    
    # Individual choice probability
    numerator <- exp(util)
    denominator <- 1 + colSums(numerator)
    T_m <- numerator / matrix(denominator, nrow = J, ncol = R, byrow = TRUE)
    
    # Jacobian
    jac_sigma_alpha_m <- numeric(J)
    jac_delta_m <- matrix(0, nrow = J, ncol = J)
    
    for (r in 1:R) {
      T_r <- T_m[, r]
      A_r <- diag(T_r) - (T_r %*% t(T_r))
      jac_sigma_alpha_m <- jac_sigma_alpha_m + as.vector(A_r %*% (-p_m * nu_m[r])) / R
      jac_delta_m <- jac_delta_m + A_r / R
    }
    
    jac_sigma_alpha[id] <- jac_sigma_alpha_m
    jac_delta[id, id] <- jac_delta_m
  }
  
  # Return
  -solve(jac_delta, jac_sigma_alpha)
}

# Estimated parameters
theta1_hat <- solve_mpec$solution[1:(K - 1)]
sigma_alpha_hat <- solve_mpec$solution[K]
xi_hat <- solve_mpec$solution[index_xi]

# Compute delta given sigma_alpha_hat
delta_se <- x0_solve_delta(sigma_alpha_hat)

# Compute xi given delta_se and theta1_hat
resid_se <- delta_se - theta1_hat[1] * x1 - theta1_hat[2] * x2 - theta1_hat[3] * x3 + theta1_hat[4] * p

# Jacobian of delta w.r.t. sigma_alpha
jac_delta <- compute_jacobian_delta_sigma_alpha(sigma_alpha_hat, delta_se)

# VC matrix for MPEC structual parameters
covg <- matrix(0, nrow = L, ncol = L)
for (i in 1:N) {
  IV_i <- matrix(IV[i, ], ncol = 1)
  covg <- covg + (IV_i %*% t(IV_i)) * (resid_se[i]^2)
}

DX <- cbind(x1, x2, x3, -p, jac_delta)
Dg <- t(DX) %*% IV

cov_theta <- solve(Dg %*% W %*% t(Dg)) %*% Dg %*% W %*% covg %*% W %*% t(Dg) %*% solve(Dg %*% W %*% t(Dg))

se_theta <- sqrt(diag(cov_theta))

# Results
results <- data.frame(
  parameter = c("beta1", "beta2", "beta3", "alpha", "sigma_alpha"),
  estimate  = solve_mpec$solution[index_theta],
  true      = c(5, 1, 1, 1, 1),
  bias      = solve_mpec$solution[index_theta] - c(5, 1, 1, 1, 1),
  se        = se_theta
)

print(results, row.names = FALSE)





