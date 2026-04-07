# References:
# Dube, Fox, and Su (2012) “Supplement to ‘Improving the Numerical Performance of Static and Dynamic Aggregate Discrete Choice Random Coefficients Demand Estimation’,” Econometrica Supplemental Material.
# https://www.jp-dube.com/research/MPECcode.html

# Estimate demand parameters (beta1, beta2, beta3, alpha, sigma_alpha) and supply parameters (gamma0, gamma1, gamma2)
#
# Conducts: 1) perfect competition, 2) oligopoly, 3) monopoly
#
# Variables: x = (beta1, beta2, beta3, alpha, sigma_alpha, delta, gamma0, gamma1, gamma2, mc, gd, gs)
# - length of x: KD + N + KS + N + LD + LS
#
# Objective function: min_x t(g) %*% W %*% g, where g = c(gd, gs)
#
# Constraints:
# - share constraint: s(sigma_alpha, delta) = s
# - demand moment:    gd = t(IV) %*% xi / N, where xi = delta - beta1 * x1 - beta2 * x2 - beta3 * x3 + alpha * p
# - supply FOC:       mc = p - markup(alpha, sigma_alpha, delta; conduct)
# - supply moment:    gs = t(IV) %*% eta / N, where eta = mc - gamma0 - gamma1 * w - gamma2 * z

# Setup
rm(list = ls())
set.seed(1)

# Library
library(ipoptr)
library(R.matlab)
library(qrng)

# Constants
M  <- 100                           # Number of markets
J  <- 3                             # Number of products
R  <- 500                           # Number of consumers in each market
N  <- M * J                         # Number of observations
KD <- 5                             # Number of demand parameters
KS <- 3                             # Number of supply parameters
LD <- 6                             # Number of demand instruments
LS <- 6                             # Number of supply instruments
NC <- N + LD + N + LS               # Number of constraints
NX <- KD + N + KS + N + LD + LS     # Length of x = (beta1, beta2, beta3, alpha, sigma_alpha, delta, gamma0, gamma1, gamma2, mc, gd, gs)
sigma_alpha0 <- 5                   # Initial guess of sigma_alpha

# Data
data <- readMat("data/100markets3products.mat")              # Import data
X1   <- t(matrix(data[["x1"]][, 1], nrow = J, ncol = M))     # 1st product characteristics
X2   <- t(matrix(data[["x1"]][, 2], nrow = J, ncol = M))     # 2nd product characteristics
X3   <- t(matrix(data[["x1"]][, 3], nrow = J, ncol = M))     # 3rd product characteristics
P    <- t(data[["P.opt"]])                                   # Price
S    <- t(data[["shares"]])                                  # Share
S0   <- 1 - rowSums(S)                                       # Share of outside options
W    <- t(matrix(data[["w"]], nrow = J, ncol = M))           # Cost shifters
Z    <- t(matrix(data[["Z"]], nrow = J, ncol = M))           # Cost shifters

# Instruments
IV4 <- rowSums(X2) - X2
IV5 <- rowSums(X3) - X3
IV6 <- W

# Vectorization
market  <- rep(1:M, each = J)
product <- rep(1:J, times = M)
x1      <- as.vector(t(X1))
x2      <- as.vector(t(X2))
x3      <- as.vector(t(X3))
p       <- as.vector(t(P))
s       <- as.vector(t(S))
s0      <- rep(S0, each = J)
w       <- as.vector(t(W))
z       <- as.vector(t(Z))
iv4     <- as.vector(t(IV4))
iv5     <- as.vector(t(IV5))
iv6     <- as.vector(t(IV6))

# Instruments and regressors
IV <- cbind(x1, x2, x3, iv4, iv5, iv6)
XD <- cbind(x1, x2, x3, -p)
XS <- cbind(1, w, z)

# Quasi-random draws for lognormal individual price taste
u_halton <- as.vector(ghalton(n = R, d = 1))
nu_sim   <- matrix(qlnorm(u_halton, meanlog = 0, sdlog = 1), nrow = M, ncol = R, byrow = TRUE)

# Shares and derivatives in one market
# v = (alpha, sigma_alpha, delta1,...,deltaJ)
compute_share_and_derivative <- function(alpha, sigma_alpha, delta_m, p_m, nu_m) {
  
  "
  This function computes shares and derivatives in one market which are used to compute Jacobian and Hessian.
  
  Arguments:
  * alpha: scalar
  * sigma_alpha: alpha
  * delta_m: vector with length J (mean utility)
  * p_m: vector with length J (prices)
  * nu_m: vector with length R (individual price taste)
  
  Returns:
  * share: vector with length J (share)
  * share1: list with length 2 + J (1st-order derivative of share w.r.t. (alpha, sigma_alpha, delta))
  * share2: list with length 2 + J (2nd-order derivative of share w.r.t.(alpha, sigma_alpha, delta))
  * D: J x J matrix (1st-order derivative of shares w.r.t. prices)
  # D1: list with length 2 + J (1st-order derivative of D w.r.t. (alpha, sigma_alpha, delta))
  # D2: list with length 2 + J (2nd-order derivative of D w.r.t. (alpha, sigma_alpha, delta))
  "
  
  # Number of local variables (alpha, sigma_alpha, delta)
  nvar_local <- J + 2
  
  # share[a] = share of product a
  share <- rep(0, J)
  
  # D[a, b] = 1-st order derivative of share of product a w.r.t. price of product b
  D     <- matrix(0, J, J)
  
  # share1[[a]] = 1-st order derivative of share w.r.t. a-th element of (alpha, sigma_alpha, delta)
  share1 <- vector("list", nvar_local)
  
  # D1[[a]] = 1-st order derivative of D w.r.t. a-th element of (alpha, sigma_alpha, delta)
  D1     <- vector("list", nvar_local)
  for (a in seq_len(nvar_local)) {
    share1[[a]] <- rep(0, J)
    D1[[a]]     <- matrix(0, J, J)
  }
  
  # share2[[a]][[b]] = 2nd-order derivative of share w.r.t. a-th and b-th elements of (alpha, sigma_alpha, delta)
  share2 <- vector("list", nvar_local)
  
  # D2[[a]][[b]] = 2nd-order derivative of D w.r.t. a-th and b-th elements of (alpha, sigma_alpha, delta)
  D2     <- vector("list", nvar_local)
  
  # Lower-triangular part since Hessian is symmentric
  for (a in seq_len(nvar_local)) {
    share2[[a]] <- vector("list", a)
    D2[[a]]     <- vector("list", a)
    for (b in seq_len(a)) {
      share2[[a]][[b]] <- rep(0, J)
      D2[[a]][[b]]     <- matrix(0, J, J)
    }
  }
  
  # J-dimensional standard basis vectors
  e_list <- lapply(seq_len(J), function(j) { e <- rep(0, J); e[j] <- 1; e })
  
  # 1-st order derivative of individual utility (delta_m - sigma_alpha * p_m * nu_r) w.r.t. (alpha, sigma_alpha, delta)
  u_deriv <- function(index, nu_r) {
    if (index == 1) {
      rep(0, J)
    } else if (index == 2) {
      -p_m * nu_r
    } else {
      e_list[[index - 2]]
    }
  }
  
  # 1st-order derivative of individual price sensitivity (alpha + sigma_alpha * nu_r) w.r.t. (alpha, sigma_alpha, delta)
  a_deriv <- function(index, nu_r) {
    if (index == 1) {
      1
    } else if (index == 2) {
      nu_r
    } else {
      0
    }
  }
  
  # Loop over each consumer
  for (r in seq_len(R)) {
    nu_r <- nu_m[r]
    a_r  <- alpha + sigma_alpha * nu_r
    
    # Individual utility
    util <- delta_m - sigma_alpha * p_m * nu_r
    num  <- exp(util)
    den  <- 1 + sum(num)
    
    # Individual choice probability
    T    <- num / den
    
    # Jacobian of individual choice probability w.r.t. individual utility
    B    <- diag(T) - tcrossprod(T, T)
    
    # Update share and D
    share <- share + T / R
    D     <- D + (-a_r * B) / R
    
    # T1[[a]] = 1-st order derivative of individual choice probability (T) w.r.t. a-th element of (alpha, sigma_alpha, delta)
    T1 <- vector("list", nvar_local)
    
    # B1[[a]] = 1-st order derivative of B w.r.t. a-th element of (alpha, sigma_alpha, delta)
    B1 <- vector("list", nvar_local)
    
    # Fill in share 1 and D1
    for (a in seq_len(nvar_local)) {
      ua <- u_deriv(a, nu_r)
      Ta <- as.vector(B %*% ua)
      Ba <- diag(Ta) - tcrossprod(Ta, T) - tcrossprod(T, Ta)
      T1[[a]] <- Ta
      B1[[a]] <- Ba
      share1[[a]] <- share1[[a]] + Ta / R
      D1[[a]] <- D1[[a]] + (-(a_deriv(a, nu_r) * B + a_r * Ba)) / R
    }
    
    # Fill in share2 and D2
    for (a in seq_len(nvar_local)) {
      for (b in seq_len(a)) {
        ub  <- u_deriv(b, nu_r)
        Tab <- as.vector(B1[[a]] %*% ub)
        Bab <- diag(Tab) - tcrossprod(Tab, T) - tcrossprod(T, Tab) - tcrossprod(T1[[a]], T1[[b]]) - tcrossprod(T1[[b]], T1[[a]])
        share2[[a]][[b]] <- share2[[a]][[b]] + Tab / R
        D2[[a]][[b]] <- D2[[a]][[b]] + (-(a_deriv(a, nu_r) * B1[[b]] + a_deriv(b, nu_r) * B1[[a]] + a_r * Bab)) / R
      }
    }
  }
  
  # Return
  list(share = share, D = D, share1 = share1, D1 = D1, share2 = share2, D2 = D2)
}

# Share given sigma_alpha and delta
compute_share <- function(sigma_alpha, delta) {
  
  "
  This function compute shares in all markets given sigma_alpha and delta.
  
  Arguments:
  * sigma_alpha: scalar
  * delta: vector with length N
  
  Returns:
  * share_hat: vector with length N (shares in all markets)
  "
  
  # Prepare
  share_hat <- numeric(N)
  
  # Compute shares in each market
  for (m in unique(market)) {
    id <- which(market == m)
    delta_m <- delta[id]
    p_m <- p[id]
    nu_m <- nu_sim[m, ]
    util <- matrix(delta_m, nrow = J, ncol = R, byrow = FALSE) - sigma_alpha * matrix(p_m, nrow = J, ncol = R, byrow = FALSE) * matrix(nu_m, nrow = J, ncol = R, byrow = TRUE)
    num <- exp(util)
    den <- 1 + colSums(num)
    share_hat[id] <- rowMeans(num / matrix(den, nrow = J, ncol = R, byrow = TRUE))
  }
  
  # Return
  share_hat
}

# Contraction mapping to solve for delta given sigma_alpha
solve_delta <- function(sigma_alpha, tol = 1e-12, maxit = 200000) {
  
  "
  This function solves for delta given sigma_alpha by contraction mapping.
  
  Arguments:
  * sigma_alpha: scalar
  
  Returns:
  * delta: vector with length N (mean utility)
  "
  
  # Prepare
  delta_old <- log(s) - log(s0)
  dist <- Inf
  iter <- 0
  
  # Contraction mapping
  while (dist > tol && iter < maxit) {
    share_hat <- compute_share(sigma_alpha, delta_old)
    delta_new <- delta_old + log(s) - log(share_hat)
    dist <- max(abs(delta_new - delta_old))
    delta_old <- delta_new
    iter <- iter + 1
  }
  
  # Return
  delta_old
}

# Compute markup in one market
compute_markup <- function(D_m, s_m, conduct) {
  
  "
  This function computes markups in one market given Jacobian of shares w.r.t. prices, shares, and conduct.
  
  Arguments:
  * D_m: J x J matrix (Jacobian of shares w.r.t. prices)
  * s_m: vector with length J (shares)
  * conduct: character
  
  Returns:
  * markup: vector with length J (depends on conduct)
  "
  
  if (conduct == "pc") {
    rep(0, J)
  } else if (conduct == "oligopoly") {
    -solve(diag(diag(D_m)), s_m)
  } else if (conduct == "monopoly") {
    -solve(D_m, s_m)
  } else {
    stop("Unknown conduct")
  }
}

# Compute markup in all markets
compute_markup_all <- function(alpha, sigma_alpha, delta, conduct) {
  
  "
  This function computes markups in all markets.
  
  Arguments:
  * alpha: scalar
  * sigma_alpha: scalar
  * conduct: character
  
  Returns:
  * markup: vector with length N
  "
  
  # Prepare
  markup <- numeric(N)
  
  # Loop over markets
  for (m in unique(market)) {
    id <- which(market == m)
    out <- compute_share_and_derivative(alpha, sigma_alpha, delta[id], p[id], nu_sim[m, ])
    markup[id] <- compute_markup(out[["D"]], out[["share"]], conduct)
  }
  
  # Return
  markup
}

# Internally consistent start value
start_value <- function(sigma_alpha, conduct = "oligopoly") {
  
  "
  This function computes internally consistent start values.
  
  Arguments:
  * sigma_alpha: scalar
  * conduct: character
  
  Returns:
  * start_value: vector with length (KD + N + KS + N + LD + LS)
  "
  
  # Solve for delta given sigma_alpha by contraction mapping
  delta0 <- solve_delta(sigma_alpha)
  
  # Compute (beta1, beta2, beta3, alpha) given delta by IV regression
  P_IV <- IV %*% solve(crossprod(IV)) %*% t(IV)
  thetad0 <- as.vector(solve(t(XD) %*% P_IV %*% XD, t(XD) %*% P_IV %*% delta0))
  
  # Compute xi give delta and (beta1, beta2, beta3, alpha)
  xi0 <- as.vector(delta0 - XD %*% thetad0)
  
  # Compute demand-side moment conditions given xi
  gd0 <- as.vector(crossprod(IV, xi0) / N)
  
  # Compute markup given alpha, sigma_alpha, delta, and conduct
  alpha0 <- thetad0[4]
  markup0 <- compute_markup_all(alpha0, sigma_alpha, delta0, conduct)
  
  # Compute mc given markup
  mc0 <- p - markup0
  
  # Compute (gamma0, gamma1, gamma2) given mc by IV regression
  thetas0 <- as.vector(solve(t(XS) %*% P_IV %*% XS, t(XS) %*% P_IV %*% mc0))
  
  # COmpute eta given mc and (gamma0, gamma1, gamma2)
  eta0 <- as.vector(mc0 - XS %*% thetas0)
  
  # Compute supply-side moment conditions given eta
  gs0 <- as.vector(crossprod(IV, eta0) / N)
  
  # Return internally consistent start values
  c(thetad0[1:4], sigma_alpha, delta0, thetas0, mc0, gd0, gs0)
}

# Index of variables
index_beta        <- 1:(KD - 2)
index_alpha       <- KD - 1
index_sigma_alpha <- KD
index_delta       <- (KD + 1):(KD + N)
index_gamma       <- (KD + N + 1):(KD + N + KS)
index_mc          <- (KD + N + KS + 1):(KD + N + KS + N)
index_gd          <- (KD + N + KS + N + 1):(KD + N + KS + N + LD)
index_gs          <- (KD + N + KS + N + LD + 1):NX

# Index of constraints
index_con_share <- 1:N
index_con_gd    <- (N + 1):(N + LD)
index_con_foc   <- (N + LD + 1):(N + LD + N)
index_con_gs    <- (N + LD + N + 1):NC


# MPEC
MPEC <- function(conduct = c("pc", "oligopoly", "monopoly"), Wmat) {
  
  "
  This function computes everything for optimization problem.
  
  Arguments:
  * conduct: character
  * Wmat: (LD + LS) x (LD + LS) matrix
  
  Returns:
  conduct: character
  W: (LD + LS) x (LD + LS) matrix (weight matrix)
  eval_f: scalar (objective function)
  eval_grad_f: vector with length NX (gradient of objective function w.r.t. x = (beta1, beta2, beta3, alpha, sigma_alpha, delta, gamma0, gamma1, gamma2, mc, gd, gs))
  eval_g: vector with length NC (constraints)
  eval_jac_g: vector (nonzero entries of constraint Jacobian, constraint Jacobian is NC x NX matrix)
  eval_jac_g_structure: list with length NC (column positions of nonzero entries of constraint Jacobian)
  eval_h: vector (nonzero entries of the lower triangular part of the Hessian of the Lagrangian, Hessian is NX x NX matrix)
  eval_h_structure: list with length NX (column positions of nonzero entries in each row of the lower triangular part of the Hessian of the Lagrangian)
  "
  
  # Conduct
  conduct <- match.arg(conduct)
  
  # Prepare linear parts to compute constraint Jacobian
  IVXD1 <- as.vector(crossprod(IV, XD[, 1]) / N)
  IVXD2 <- as.vector(crossprod(IV, XD[, 2]) / N)
  IVXD3 <- as.vector(crossprod(IV, XD[, 3]) / N)
  IVXD4 <- as.vector(crossprod(IV, XD[, 4]) / N)
  IVXS1 <- as.vector(crossprod(IV, XS[, 1]) / N)
  IVXS2 <- as.vector(crossprod(IV, XS[, 2]) / N)
  IVXS3 <- as.vector(crossprod(IV, XS[, 3]) / N)
  
  # Sparsity patters of constraint Jacobian
  jac_structure <- vector("list", NC)
  
  # Sparsity patters of share constraint Jacobian
  # Share constrain depends on (sigma_alpha, delta_m)
  for (m in unique(market)) {
    id <- which(market == m)
    for (j in seq_len(J)) jac_structure[[index_con_share[id[j]]]] <- c(index_sigma_alpha, index_delta[id])
  }
  
  # Demand-side moment constraint Jacobian
  # Demand-side moment constraint depends on (beta1, beta2, beta3, alpha, delta, gd_l)
  for (l in seq_len(LD)) jac_structure[[index_con_gd[l]]] <- c(index_beta, index_alpha, index_delta, index_gd[l])
  
  # FOC constraint Jacobian
  # FOC constraint Jacobian depends on (alpha, sigma_alpha, delta_m, mc_m)
  for (m in unique(market)) {
    id <- which(market == m)
    for (j in seq_len(J)) jac_structure[[index_con_foc[id[j]]]] <- c(index_alpha, index_sigma_alpha, index_delta[id], index_mc[id[j]])
  }
  
  # Supply-side moment constraint Jacobian
  # Supply-side moment constraint Jacobian depends on (gamma, mc, gs_l)
  for (l in seq_len(LS)) jac_structure[[index_con_gs[l]]] <- c(index_gamma, index_mc, index_gs[l])
  
  # Sparsity patterns of Hessian of Lagrangian
  h_structure <- vector("list", NX)
  
  # Empty list with length NX
  for (i in seq_len(NX)) h_structure[[i]] <- integer(0)
  
  # Function that returns nonzero entries of lower triangular part
  add_h_nz <- function(rows, cols = rows) {
    for (i in rows) {
      cand <- cols[cols <= i]
      if (length(cand)) h_structure[[i]] <<- union(h_structure[[i]], cand)
    }
  }
  
  # Hessian of objective function depends on (gd, gs)
  add_h_nz(c(index_gd, index_gs), c(index_gd, index_gs))
  
  # Hessian of share constraint depends on (sigma_alpha, delta_m)
  for (m in unique(market)) {
    id <- which(market == m)
    blk <- c(index_sigma_alpha, index_delta[id])
    add_h_nz(blk, blk)
  }
  
  # Hessian of FOC constraint depends on (alpha, sigma_alpha, delta_m)
  if (conduct != "pc") {
    for (m in unique(market)) {
      id <- which(market == m)
      blk <- c(index_alpha, index_sigma_alpha, index_delta[id])
      add_h_nz(blk, blk)
    }
  }
  
  # Hessian of demand and supply moment constraints is 0
  
  # Sort
  h_structure <- lapply(h_structure, sort)
  
  # Objective function
  eval_f <- function(x) {
    
    "
    This function compute an objective function.
    
    Arguments:
    * x: vector with length NX (beta1, beta2, beta3, alpha, sigma_alpha, delta, gamma0, gamma1, gamma2, mc, gd, gs)
    
    Returns:
    * obejctive: scalar
    "
    
    # Prepare
    g <- c(x[index_gd], x[index_gs])
    
    # Return objective
    as.numeric(crossprod(g, Wmat %*% g))
  }
  
  # Gradient of objective function
  eval_grad_f <- function(x) {
    
    "
    This function computes gradient of objective function w.r.t. x
    
    Arguments:
    x: vector with length NX (beta1, beta2, beta3, alpha, sigma_alpha, delta, gamma0, gamma1, gamma2, mc, gd, gs)
    
    Returns:
    grad_f: vector with length x (gradient of objective function w.r.t. x)
    "
    
    # Prepare
    grad_f <- rep(0, NX)
    g <- c(x[index_gd], x[index_gs])
    
    # Gradient
    grad_f[c(index_gd, index_gs)] <- as.vector(2 * Wmat %*% g)
    
    # Return
    grad_f
  }
  
  # Constraints
  eval_g <- function(x) {
    
    "
    This function computes constraints.
    
    Arguments:
    * x: vector with length NX (beta1, beta2, beta3, alpha, sigma_alpha, delta, gamma0, gamma1, gamma2, mc, gd, gs)
    
    Returns:
    * constraints: vector with length NC (share constraint, demand moment constraint, FOC constraint, supply moment constraint)
    "
    
    # Prepare
    beta        <- x[index_beta]
    alpha       <- x[index_alpha]
    sigma_alpha <- x[index_sigma_alpha]
    delta       <- x[index_delta]
    gamma       <- x[index_gamma]
    mc          <- x[index_mc]
    gd          <- x[index_gd]
    gs          <- x[index_gs]
    
    # Share and FOC constraints
    con_share <- numeric(N)
    con_foc   <- numeric(N)
    
    for (m in unique(market)) {
      id <- which(market == m)
      out <- compute_share_and_derivative(alpha, sigma_alpha, delta[id], p[id], nu_sim[m, ])
      markup_m <- compute_markup(out[["D"]], out[["share"]], conduct)
      con_share[id] <- out[["share"]] - s[id]
      con_foc[id]   <- mc[id] - p[id] + markup_m
    }
    
    # Demand-side moment constraint
    xi    <- as.vector(delta - XD %*% c(beta, alpha))
    gd_eq <- gd - as.vector(crossprod(IV, xi) / N)
    
    # Supply-side moment constraint
    eta   <- as.vector(mc - XS %*% gamma)
    gs_eq <- gs - as.vector(crossprod(IV, eta) / N)
    
    # Return all constraints
    c(con_share, gd_eq, con_foc, gs_eq)
  }
  
  # Jacobian of constraints w.r.t. x
  eval_jac_g <- function(x) {
    
    "
    This function computes Jacobian of constraints w.r.t. x.
    
    Arguments:
    * x: vector with length NX (beta1, beta2, beta3, alpha, sigma_alpha, delta, gamma0, gamma1, gamma2, mc, gd, gs)
    
    Returns:
    * vector of nonzero entries of constraint Jacobian
    "
    
    # Prepare
    values <- vector("list", NC)
    alpha       <- x[index_alpha]
    sigma_alpha <- x[index_sigma_alpha]
    delta       <- x[index_delta]
    
    # Share constraint depends on (sigma_alpha, delta_m)
    for (m in unique(market)) {
      id <- which(market == m)
      out <- compute_share_and_derivative(alpha, sigma_alpha, delta[id], p[id], nu_sim[m, ])
      ds_dsigma <- out$share1[[2]]
      ds_ddelta <- do.call(cbind, lapply(seq_len(J), function(j) out$share1[[j + 2]]))
      for (j in seq_len(J)) {
        values[[index_con_share[id[j]]]] <- c(ds_dsigma[j], ds_ddelta[j, ])
      }
    }
    
    # Demand-side moment depends on (beta1, beta2, beta3, alpha, delta, gd_l)
    for (l in seq_len(LD)) {
      values[[index_con_gd[l]]] <- c(IVXD1[l], IVXD2[l], IVXD3[l], IVXD4[l], -IV[, l] / N, 1)
    }
    
    # FOC constraint depends on (alpha, sigma_alpgh, delta_m)
    for (m in unique(market)) {
      id <- which(market == m)
      out <- compute_share_and_derivative(alpha, sigma_alpha, delta[id], p[id], nu_sim[m, ])
      share_m <- out$share
      D_m     <- out$D
      nvar_local <- J + 2
      
      if (conduct == "pc") {
        m1 <- vector("list", nvar_local)
        for (a in seq_len(nvar_local)) m1[[a]] <- rep(0, J)
      } else {
        if (conduct == "oligopoly") {
          D_use  <- diag(diag(D_m))
          D1_use <- vector("list", nvar_local)
          for (a in seq_len(nvar_local)) D1_use[[a]] <- diag(diag(out$D1[[a]]))
        } else {
          D_use  <- D_m
          D1_use <- out$D1
        }
        markup_m <- -solve(D_use, share_m)
        m1 <- vector("list", nvar_local)
        for (a in seq_len(nvar_local)) {
          qa <- out$share1[[a]] + D1_use[[a]] %*% markup_m
          m1[[a]] <- -solve(D_use, qa)
        }
      }
      
      for (j in seq_len(J)) {
        values[[index_con_foc[id[j]]]] <- c(m1[[1]][j], m1[[2]][j], sapply(3:(J + 2), function(a) m1[[a]][j]), 1)
      }
    }
    
    # Supply-side moment depends on (gamma0, gamma1, gamma2, mc, gs_l)
    for (l in seq_len(LS)) {
      values[[index_con_gs[l]]] <- c(IVXS1[l], IVXS2[l], IVXS3[l], -IV[, l] / N, 1)
    }
    
    # Return
    unlist(values, use.names = FALSE)
  }
  
  # Hessian of Lagrangian
  eval_h <- function(x, obj_factor, hessian_lambda) {
    
    "
    This function computes Hessian of Lagrangian w.r.t. x.
    
    Arguments:
    * x: vector with length NX (beta1, beta2, beta3, alpha, sigma_alpha, delta, gamma0, gamma1, gamma2, mc, gd, gs)
    
    Returns:
    * vector of nonzero entries of Hessian of Lagrangian
    "
    
    # Prepare
    alpha       <- x[index_alpha]
    sigma_alpha <- x[index_sigma_alpha]
    delta       <- x[index_delta]
    H           <- matrix(0, NX, NX)
    
    # Objective function
    H[c(index_gd, index_gs), c(index_gd, index_gs)] <- obj_factor * (2 * Wmat)
    
    # Share constraint
    lambda_share <- hessian_lambda[index_con_share]
    for (m in unique(market)) {
      id <- which(market == m)
      lambda_m <- lambda_share[id]
      if (all(abs(lambda_m) < 1e-16)) next
      out <- compute_share_and_derivative(alpha, sigma_alpha, delta[id], p[id], nu_sim[m, ])
      idx_m <- c(index_sigma_alpha, index_delta[id])
      Hm <- matrix(0, J + 1, J + 1)
      map_m <- c(2, 3:(J + 2))
      for (a_small in seq_along(map_m)) {
        a <- map_m[a_small]
        for (b_small in seq_len(a_small)) {
          b <- map_m[b_small]
          val <- sum(lambda_m * out$share2[[a]][[b]])
          Hm[a_small, b_small] <- Hm[a_small, b_small] + val
          if (a_small != b_small) Hm[b_small, a_small] <- Hm[b_small, a_small] + val
        }
      }
      H[idx_m, idx_m] <- H[idx_m, idx_m] + Hm
    }
    
    # FOC constraint
    lambda_foc <- hessian_lambda[index_con_foc]
    for (m in unique(market)) {
      id <- which(market == m)
      lambda_m <- lambda_foc[id]
      if (all(abs(lambda_m) < 1e-16) || conduct == "pc") next
      
      out <- compute_share_and_derivative(alpha, sigma_alpha, delta[id], p[id], nu_sim[m, ])
      share_m <- out$share
      D_m     <- out$D
      nvar_local <- J + 2
      
      if (conduct == "oligopoly") {
        D_use  <- diag(diag(D_m))
        D1_use <- vector("list", nvar_local)
        D2_use <- vector("list", nvar_local)
        for (a in seq_len(nvar_local)) {
          D1_use[[a]] <- diag(diag(out$D1[[a]]))
          D2_use[[a]] <- vector("list", a)
          for (b in seq_len(a)) D2_use[[a]][[b]] <- diag(diag(out$D2[[a]][[b]]))
        }
      } else {
        D_use  <- D_m
        D1_use <- out$D1
        D2_use <- out$D2
      }
      
      markup_m <- -solve(D_use, share_m)
      m1 <- vector("list", nvar_local)
      for (a in seq_len(nvar_local)) {
        qa <- out$share1[[a]] + D1_use[[a]] %*% markup_m
        m1[[a]] <- -solve(D_use, qa)
      }
      
      Hm <- matrix(0, nvar_local, nvar_local)
      for (a in seq_len(nvar_local)) {
        for (b in seq_len(a)) {
          qab <- out$share2[[a]][[b]] + D2_use[[a]][[b]] %*% markup_m +
            D1_use[[a]] %*% m1[[b]] + D1_use[[b]] %*% m1[[a]]
          mab <- -solve(D_use, qab)
          val <- sum(lambda_m * mab)
          Hm[a, b] <- Hm[a, b] + val
          if (a != b) Hm[b, a] <- Hm[b, a] + val
        }
      }
      
      idx_m <- c(index_alpha, index_sigma_alpha, index_delta[id])
      H[idx_m, idx_m] <- H[idx_m, idx_m] + Hm
    }
    
    # Return vectorized nonzero entries of lower triangular part of Hessian matrix
    unlist(lapply(seq_len(NX), function(i) H[i, h_structure[[i]]]), use.names = FALSE)
  }
  
  # Return
  list(
    conduct = conduct,
    W = Wmat,
    eval_f = eval_f,
    eval_grad_f = eval_grad_f,
    eval_g = eval_g,
    eval_jac_g = eval_jac_g,
    eval_jac_g_structure = jac_structure,
    eval_h = eval_h,
    eval_h_structure = h_structure
  )
}

# Start value
x0 <- start_value(sigma_alpha0)

# Weight matrix
W_gmm <- diag(LD + LS)

# Solve optimization problem
solve_mpec <- function(conduct = c("pc", "oligopoly", "monopoly"), W_mat) {
  
  conduct <- match.arg(conduct)
  
  model <- MPEC(conduct, W_mat)
  
  result <- ipoptr(
    x0 = x0,
    eval_f = model$eval_f,
    eval_grad_f = model$eval_grad_f,
    lb = rep(-1.0e19, NX),
    ub = rep(1.0e19, NX),
    eval_g = model$eval_g,
    eval_jac_g = model$eval_jac_g,
    eval_jac_g_structure = model$eval_jac_g_structure,
    constraint_lb = rep(0, NC),
    constraint_ub = rep(0, NC),
    eval_h = model$eval_h,
    eval_h_structure = model$eval_h_structure,
    opts = list(
      print_level = 5,
      max_iter = 200000,
      tol = 1e-8,
      constr_viol_tol = 1e-8,
      compl_inf_tol = 1e-8,
      dual_inf_tol = 1e-8,
      linear_solver = "mumps"
      #derivative_test = "first-order",
      #derivative_test_print_all = "no"
      #derivative_test = "second-order",
      #derivative_test_print_all = "no"
    )
  )
  
  # Return
  return(result)
}


# Oligopoly
solve_mpec("oligopoly", W_gmm)$solution[c(index_beta, index_alpha, index_sigma_alpha, index_gamma)]

# Perfect competition
solve_mpec("pc", W_gmm)$solution[c(index_beta, index_alpha, index_sigma_alpha, index_gamma)]

# Monopoly
solve_mpec("monopoly", W_gmm)$solution[c(index_beta, index_alpha, index_sigma_alpha, index_gamma)]





