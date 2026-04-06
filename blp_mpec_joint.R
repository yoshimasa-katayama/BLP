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
# Objective function: min_x t(g) %*% W %*% g, where g = rbind(gd, gs)
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
sigma_alpha0 <- 3                   # Initial guess of sigma_alpha

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

# Convert matrix to vectorized lower triangular matrix
matrix_to_lower_triangular_vector <- function(A) {
  unlist(lapply(seq_len(nrow(A)), function(i) A[i, seq_len(i)]), use.names = FALSE)
}

# Shares and derivatives in one market
# v = (alpha, sigma_alpha, delta1,...,deltaJ)
compute_share_and_derivative <- function(alpha, sigma_alpha, delta_m, p_m, nu_m) {
  nvar_local <- J + 2
  
  share <- rep(0, J)
  D     <- matrix(0, J, J)
  
  share1 <- vector("list", nvar_local)
  D1     <- vector("list", nvar_local)
  for (a in seq_len(nvar_local)) {
    share1[[a]] <- rep(0, J)
    D1[[a]]     <- matrix(0, J, J)
  }
  
  share2 <- vector("list", nvar_local)
  D2     <- vector("list", nvar_local)
  for (a in seq_len(nvar_local)) {
    share2[[a]] <- vector("list", a)
    D2[[a]]     <- vector("list", a)
    for (b in seq_len(a)) {
      share2[[a]][[b]] <- rep(0, J)
      D2[[a]][[b]]     <- matrix(0, J, J)
    }
  }
  
  e_list <- lapply(seq_len(J), function(j) { e <- rep(0, J); e[j] <- 1; e })
  
  u_deriv <- function(index, nu_r) {
    if (index == 1) {
      rep(0, J)
    } else if (index == 2) {
      -p_m * nu_r
    } else {
      e_list[[index - 2]]
    }
  }
  
  a_deriv <- function(index, nu_r) {
    if (index == 1) {
      1
    } else if (index == 2) {
      nu_r
    } else {
      0
    }
  }
  
  for (r in seq_len(R)) {
    nu_r <- nu_m[r]
    a_r  <- alpha + sigma_alpha * nu_r
    
    util <- delta_m - sigma_alpha * p_m * nu_r
    num  <- exp(util)
    den  <- 1 + sum(num)
    T    <- num / den
    B    <- diag(T) - tcrossprod(T, T)
    
    share <- share + T / R
    D     <- D + (-a_r * B) / R
    
    T1 <- vector("list", nvar_local)
    B1 <- vector("list", nvar_local)
    for (a in seq_len(nvar_local)) {
      ua <- u_deriv(a, nu_r)
      Ta <- as.vector(B %*% ua)
      Ba <- diag(Ta) - tcrossprod(Ta, T) - tcrossprod(T, Ta)
      T1[[a]] <- Ta
      B1[[a]] <- Ba
      share1[[a]] <- share1[[a]] + Ta / R
      D1[[a]] <- D1[[a]] + (-(a_deriv(a, nu_r) * B + a_r * Ba)) / R
    }
    
    for (a in seq_len(nvar_local)) {
      for (b in seq_len(a)) {
        ub  <- u_deriv(b, nu_r)
        Tab <- as.vector(B1[[a]] %*% ub)
        Bab <- diag(Tab) - tcrossprod(Tab, T) - tcrossprod(T, Tab) -
          tcrossprod(T1[[a]], T1[[b]]) - tcrossprod(T1[[b]], T1[[a]])
        share2[[a]][[b]] <- share2[[a]][[b]] + Tab / R
        D2[[a]][[b]] <- D2[[a]][[b]] +
          (-(a_deriv(a, nu_r) * B1[[b]] + a_deriv(b, nu_r) * B1[[a]] + a_r * Bab)) / R
      }
    }
  }
  
  list(share = share, D = D, share1 = share1, D1 = D1, share2 = share2, D2 = D2)
}

# Share given sigma_alpha and delta
compute_share <- function(sigma_alpha, delta) {
  share_hat <- numeric(N)
  for (m in unique(market)) {
    id <- which(market == m)
    delta_m <- delta[id]
    p_m <- p[id]
    nu_m <- nu_sim[m, ]
    util <- matrix(delta_m, nrow = J, ncol = R, byrow = FALSE) -
      sigma_alpha * matrix(p_m, nrow = J, ncol = R, byrow = FALSE) *
      matrix(nu_m, nrow = J, ncol = R, byrow = TRUE)
    num <- exp(util)
    den <- 1 + colSums(num)
    share_hat[id] <- rowMeans(num / matrix(den, nrow = J, ncol = R, byrow = TRUE))
  }
  share_hat
}

# Contraction mapping to solve for delta given sigma_alpha
solve_delta <- function(sigma_alpha, tol = 1e-12, maxit = 200000) {
  delta_old <- log(s) - log(s0)
  dist <- Inf
  iter <- 0
  while (dist > tol && iter < maxit) {
    share_hat <- compute_share(sigma_alpha, delta_old)
    delta_new <- delta_old + log(s) - log(share_hat)
    dist <- max(abs(delta_new - delta_old))
    delta_old <- delta_new
    iter <- iter + 1
  }
  delta_old
}

# Compute markup in one market
compute_markup <- function(D_m, s_m, conduct) {
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
  markup <- numeric(N)
  for (m in unique(market)) {
    id <- which(market == m)
    out <- compute_share_and_derivative(alpha, sigma_alpha, delta[id], p[id], nu_sim[m, ])
    markup[id] <- compute_markup(out[["D"]], out[["share"]], conduct)
  }
  markup
}

# Internally consistent start value
start_value <- function(sigma_alpha, conduct = "oligopoly") {
  delta0 <- solve_delta(sigma_alpha)
  
  P_IV <- IV %*% solve(crossprod(IV)) %*% t(IV)
  thetad0 <- as.vector(solve(t(XD) %*% P_IV %*% XD, t(XD) %*% P_IV %*% delta0))
  
  xi0 <- as.vector(delta0 - XD %*% thetad0)
  gd0 <- as.vector(crossprod(IV, xi0) / N)
  
  alpha0 <- thetad0[4]
  markup0 <- compute_markup_all(alpha0, sigma_alpha, delta0, conduct)
  mc0 <- p - markup0
  
  thetas0 <- as.vector(solve(t(XS) %*% P_IV %*% XS, t(XS) %*% P_IV %*% mc0))
  eta0 <- as.vector(mc0 - XS %*% thetas0)
  gs0 <- as.vector(crossprod(IV, eta0) / N)
  
  c(thetad0[1:4], sigma_alpha, delta0, thetas0, mc0, gd0, gs0)
}

# Index
index_beta        <- 1:(KD - 2)
index_alpha       <- KD - 1
index_sigma_alpha <- KD
index_delta       <- (KD + 1):(KD + N)
index_gamma       <- (KD + N + 1):(KD + N + KS)
index_mc          <- (KD + N + KS + 1):(KD + N + KS + N)
index_gd          <- (KD + N + KS + N + 1):(KD + N + KS + N + LD)
index_gs          <- (KD + N + KS + N + LD + 1):NX

index_con_share <- 1:N
index_con_gd    <- (N + 1):(N + LD)
index_con_foc   <- (N + LD + 1):(N + LD + N)
index_con_gs    <- (N + LD + N + 1):NC


# MPEC
MPEC <- function(conduct = c("pc", "oligopoly", "monopoly"), Wmat) {
  conduct <- match.arg(conduct)
  
  # Compute linear parts for Jacobian values
  IVXD1 <- as.vector(crossprod(IV, XD[, 1]) / N)
  IVXD2 <- as.vector(crossprod(IV, XD[, 2]) / N)
  IVXD3 <- as.vector(crossprod(IV, XD[, 3]) / N)
  IVXD4 <- as.vector(crossprod(IV, XD[, 4]) / N)
  IVXS1 <- as.vector(crossprod(IV, XS[, 1]) / N)
  IVXS2 <- as.vector(crossprod(IV, XS[, 2]) / N)
  IVXS3 <- as.vector(crossprod(IV, XS[, 3]) / N)
  
  # Sparse Jacobian structure as list of nonzero columns for each constraint row
  jac_structure <- vector("list", NC)
  for (m in unique(market)) {
    id <- which(market == m)
    for (j in seq_len(J)) jac_structure[[index_con_share[id[j]]]] <- c(index_sigma_alpha, index_delta[id])
  }
  for (l in seq_len(LD)) jac_structure[[index_con_gd[l]]] <- c(index_beta, index_alpha, index_delta, index_gd[l])
  for (m in unique(market)) {
    id <- which(market == m)
    for (j in seq_len(J)) jac_structure[[index_con_foc[id[j]]]] <- c(index_alpha, index_sigma_alpha, index_delta[id], index_mc[id[j]])
  }
  for (l in seq_len(LS)) jac_structure[[index_con_gs[l]]] <- c(index_gamma, index_mc, index_gs[l])
  
  # Sparse Hessian structure as list of lower-triangular nonzero columns for each row
  # Nonzero blocks:
  # - Objective: (gd,gs)x(gd,gs)
  # - Share constraints: (sigma_alpha, delta_m)x(sigma_alpha, delta_m)
  # - FOC constraints: (alpha, sigma_alpha, delta_m)x(alpha, sigma_alpha, delta_m)
  h_structure <- vector("list", NX)
  for (i in seq_len(NX)) h_structure[[i]] <- integer(0)
  
  add_h_nz <- function(rows, cols = rows) {
    for (i in rows) {
      cand <- cols[cols <= i]
      if (length(cand)) h_structure[[i]] <<- union(h_structure[[i]], cand)
    }
  }
  
  # Objective block: g = (gd, gs)
  add_h_nz(c(index_gd, index_gs), c(index_gd, index_gs))
  
  # Share block: (sigma_alpha, delta_m)
  for (m in unique(market)) {
    id <- which(market == m)
    blk <- c(index_sigma_alpha, index_delta[id])
    add_h_nz(blk, blk)
  }
  
  # FPC block: (alpha, sigma_alpha, delta_m)
  if (conduct != "pc") {
    for (m in unique(market)) {
      id <- which(market == m)
      blk <- c(index_alpha, index_sigma_alpha, index_delta[id])
      add_h_nz(blk, blk)
    }
  }
  
  # Sort
  h_structure <- lapply(h_structure, sort)
  
  # Objective function
  eval_f <- function(x) {
    g <- c(x[index_gd], x[index_gs])
    as.numeric(crossprod(g, Wmat %*% g))
  }
  
  # Gradient of objective function
  eval_grad_f <- function(x) {
    grad_f <- rep(0, NX)
    g <- c(x[index_gd], x[index_gs])
    grad_f[c(index_gd, index_gs)] <- as.vector(2 * Wmat %*% g)
    grad_f
  }
  
  # Constraints
  eval_g <- function(x) {
    beta        <- x[index_beta]
    alpha       <- x[index_alpha]
    sigma_alpha <- x[index_sigma_alpha]
    delta       <- x[index_delta]
    gamma       <- x[index_gamma]
    mc          <- x[index_mc]
    gd          <- x[index_gd]
    gs          <- x[index_gs]
    
    con_share <- numeric(N)
    con_foc   <- numeric(N)
    
    for (m in unique(market)) {
      id <- which(market == m)
      out <- compute_share_and_derivative(alpha, sigma_alpha, delta[id], p[id], nu_sim[m, ])
      markup_m <- compute_markup(out[["D"]], out[["share"]], conduct)
      con_share[id] <- out[["share"]] - s[id]
      con_foc[id]   <- mc[id] - p[id] + markup_m
    }
    
    xi    <- as.vector(delta - XD %*% c(beta, alpha))
    eta   <- as.vector(mc - XS %*% gamma)
    gd_eq <- gd - as.vector(crossprod(IV, xi) / N)
    gs_eq <- gs - as.vector(crossprod(IV, eta) / N)
    
    c(con_share, gd_eq, con_foc, gs_eq)
  }
  
  # Jacobian of constraints
  eval_jac_g <- function(x) {
    values <- vector("list", NC)
    alpha       <- x[index_alpha]
    sigma_alpha <- x[index_sigma_alpha]
    delta       <- x[index_delta]
    
    # Share constraint
    for (m in unique(market)) {
      id <- which(market == m)
      out <- compute_share_and_derivative(alpha, sigma_alpha, delta[id], p[id], nu_sim[m, ])
      ds_dsigma <- out$share1[[2]]
      ds_ddelta <- do.call(cbind, lapply(seq_len(J), function(j) out$share1[[j + 2]]))
      for (j in seq_len(J)) {
        values[[index_con_share[id[j]]]] <- c(ds_dsigma[j], ds_ddelta[j, ])
      }
    }
    
    # Demand moment
    for (l in seq_len(LD)) {
      values[[index_con_gd[l]]] <- c(
        IVXD1[l], IVXD2[l], IVXD3[l], IVXD4[l],
        -IV[, l] / N,
        1
      )
    }
    
    # FOC constraint
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
    
    # Supply moments
    for (l in seq_len(LS)) {
      values[[index_con_gs[l]]] <- c(
        IVXS1[l], IVXS2[l], IVXS3[l],
        -IV[, l] / N,
        1
      )
    }
    
    # Return
    unlist(values, use.names = FALSE)
  }
  
  # Hessian of Lagrangian
  eval_h <- function(x, obj_factor, hessian_lambda) {
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
    
    # Return
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
      linear_solver = "mumps",
      #derivative_test = "first-order",
      #derivative_test_print_all = "no"
      derivative_test = "second-order",
      derivative_test_print_all = "no"
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





