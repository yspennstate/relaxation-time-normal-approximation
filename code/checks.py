"""Checks for "The relaxation time does not control the normal approximation of stationary additive functionals".

For b >= 1 and s >= 2b the chain X = (Y, V) of Theorem 1 has
  Y on {0, 1}:  rate eps from 0 to 1, rate 1 - eps from 1 to 0, eps = s^-2,
  V on {-1, 1}: rate R(1+m)/2 from 1 to -1, rate R(1-m)/2 from -1 to 1, R = s^4,
  g(y, v) = alpha (1 - y) v + b y,  alpha^2 = (1 - b^2 eps)/(1 - eps),  m = b eps/(alpha (1 - eps)).
Part S checks the algebra symbolically (SymPy), for symbolic b and s.
Part A checks it again in 50-digit arithmetic at given (b, s) (and exactly in rational arithmetic when b = 1).
Part B checks the two ingredients of the proof (the probability of H and the variance of the fast integral) against
matrix computations, and sigma^2 against the Poisson equation.
Part C evaluates the bound of the proof on a grid of (b, s).
Part D estimates P(S_s <= 0) at small s in two independent ways: Fourier inversion of the characteristic function
pi^T exp(s(Q + i theta G)) 1, and simulation of the chain.
Requires Python 3 with SymPy, mpmath, NumPy and SciPy."""
from fractions import Fraction

import mpmath as mp
import numpy as np
import sympy as sp
from scipy.linalg import expm

mp.mp.dps = 50
TOL = mp.mpf(10) ** -40
FAILS = []
NCHECK = [0]


def check(name, ok, detail=""):
    NCHECK[0] += 1
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILS.append(name)


STATES = [(0, -1), (0, 1), (1, -1), (1, 1)]


def params(b, s):
    b, s = mp.mpf(b), mp.mpf(s)
    eps = 1 / s ** 2
    R = s ** 4
    alpha = mp.sqrt((1 - b ** 2 * eps) / (1 - eps))
    m = b * eps / (alpha * (1 - eps))
    return b, s, eps, R, alpha, m


def chain(b, s):
    b, s, eps, R, alpha, m = params(b, s)
    rate_y = {(0, 1): eps, (1, 0): 1 - eps}
    rate_v = {(1, -1): R * (1 + m) / 2, (-1, 1): R * (1 - m) / 2}
    Q = mp.zeros(4, 4)
    for i, (y, v) in enumerate(STATES):
        for j, (y2, v2) in enumerate(STATES):
            if i == j:
                continue
            if v == v2 and y != y2:
                Q[i, j] = rate_y[(y, y2)]
            elif y == y2 and v != v2:
                Q[i, j] = rate_v[(v, v2)]
        Q[i, i] = -sum(Q[i, j] for j in range(4) if j != i)
    piy = {0: 1 - eps, 1: eps}
    piv = {1: (1 - m) / 2, -1: (1 + m) / 2}
    pi = [piy[y] * piv[v] for (y, v) in STATES]
    g = [alpha * (1 - y) * v + b * y for (y, v) in STATES]
    return Q, pi, g, (b, s, eps, R, alpha, m)


def part_s():
    b, s = sp.symbols("b s", positive=True)
    eps = 1 / s ** 2
    R = s ** 4
    alpha = sp.sqrt((1 - b ** 2 * eps) / (1 - eps))
    m = b * eps / (alpha * (1 - eps))
    rate_y = {(0, 1): eps, (1, 0): 1 - eps}
    rate_v = {(1, -1): R * (1 + m) / 2, (-1, 1): R * (1 - m) / 2}
    Q = sp.zeros(4, 4)
    for i, (y, v) in enumerate(STATES):
        for j, (y2, v2) in enumerate(STATES):
            if i != j and v == v2 and y != y2:
                Q[i, j] = rate_y[(y, y2)]
            elif i != j and y == y2 and v != v2:
                Q[i, j] = rate_v[(v, v2)]
        Q[i, i] = -sum(Q[i, j] for j in range(4) if j != i)
    piy = {0: 1 - eps, 1: eps}
    piv = {1: (1 - m) / 2, -1: (1 + m) / 2}
    pi = sp.Matrix([[piy[y] * piv[v] for (y, v) in STATES]])
    g = sp.Matrix([alpha * (1 - y) * v + b * y for (y, v) in STATES])
    z = lambda e: sp.simplify(e) == 0
    check("S1 detailed balance (symbolic b, s)", all(z(pi[i] * Q[i, j] - pi[j] * Q[j, i]) for i in range(4) for j in range(4)))
    check("S2 pi Q = 0 and pi sums to 1", all(z(x) for x in pi * Q) and z(sum(pi) - 1))
    u = sp.Matrix([y - eps for (y, v) in STATES])
    w = sp.Matrix([v + m for (y, v) in STATES])
    uw = sp.Matrix([u[i] * w[i] for i in range(4)])
    check("S3 -Q u = u, -Q w = R w, -Q uw = (R+1) uw (spectrum 0, 1, R, R+1)",
          all(z(x) for x in (-Q * u - u)) and all(z(x) for x in (-Q * w - R * w))
          and all(z(x) for x in (-Q * uw - (R + 1) * uw)))
    check("S4 pi(g) = 0 and pi(g^2) = 1", z((pi * g)[0]) and z(sum(pi[i] * g[i] ** 2 for i in range(4)) - 1))
    c1, c2, c3 = b + alpha * m, alpha * (1 - eps), -alpha
    check("S5 g = (b + alpha m) u + alpha (1 - eps) w - alpha u w", all(z(x) for x in (g - c1 * u - c2 * w - c3 * uw)))
    h = c1 * u + (c2 / R) * w + (c3 / (R + 1)) * uw
    sig2 = 2 * sum(pi[i] * g[i] * h[i] for i in range(4))
    sig2_closed = (2 * (b + alpha * m) ** 2 * eps * (1 - eps)
                   + 2 * alpha ** 2 * (1 - m ** 2) * (1 - eps) * ((1 - eps) / R + eps / (R + 1)))
    check("S6 h solves -Q h = g with pi(h) = 0, and 2 pi(g h) is the closed form of sigma^2",
          all(z(x) for x in (-Q * h - g)) and z((pi * h)[0]) and z(sig2 - sig2_closed))
    check("S7 alpha m (1 - eps) = b eps and alpha^2 (1 - eps) + b^2 eps = 1",
          z(alpha * m * (1 - eps) - b * eps) and z(alpha ** 2 * (1 - eps) + b ** 2 * eps - 1))


def part_a(b, s):
    Q, pi, g, (b_, s_, eps, R, alpha, m) = chain(b, s)
    tag = "b=%s s=%s" % (b, s)
    check("A1 rows of Q sum to 0, " + tag, max(abs(sum(Q[i, j] for j in range(4))) for i in range(4)) < TOL * R)
    db = max(abs(pi[i] * Q[i, j] - pi[j] * Q[j, i]) for i in range(4) for j in range(4))
    check("A2 detailed balance, " + tag, db < TOL * R)
    check("A3 pi sums to 1, " + tag, abs(sum(pi) - 1) < TOL)
    # eigenfunctions of -Q: 1, y - eps, v + m, (y - eps)(v + m) with eigenvalues 0, 1, R, R + 1
    efs = [([1] * 4, 0), ([y - eps for (y, v) in STATES], 1), ([v + m for (y, v) in STATES], R),
           ([(y - eps) * (v + m) for (y, v) in STATES], R + 1)]
    worst = 0
    for f, lam in efs:
        for i in range(4):
            lhs = -sum(Q[i, j] * f[j] for j in range(4))
            worst = max(worst, abs(lhs - lam * f[i]))
    check("A4 -Q has eigenvalues 0, 1, R, R+1 (eigenfunctions), " + tag, worst < TOL * R)
    ev = sorted([mp.re(x) for x in mp.eig(-Q)[0]])
    check("A5 spectrum by mp.eig = [0, 1, R, R+1], " + tag,
          max(abs(ev[k] - [0, 1, R, R + 1][k]) for k in range(4)) < mp.mpf(10) ** -30 * R, "lambda_2=%s" % mp.nstr(ev[1], 12))
    Eg = sum(p * x for p, x in zip(pi, g))
    Eg2 = sum(p * x * x for p, x in zip(pi, g))
    check("A6 pi(g) = 0 and pi(g^2) = 1, " + tag, abs(Eg) < TOL and abs(Eg2 - 1) < TOL)
    check("A7 max|g| = b, " + tag, abs(max(abs(x) for x in g) - b_) < TOL)
    check("A8 3/4 <= alpha^2 <= 1 and b eps <= m < 1/2 (here m < 0.39), " + tag,
          mp.mpf(3) / 4 <= alpha ** 2 <= 1 and b_ * eps <= m < mp.mpf("0.39"),
          "alpha=%s m=%s b*eps=%s" % (mp.nstr(alpha, 8), mp.nstr(m, 8), mp.nstr(b_ * eps, 8)))
    return Q, pi, g, (b_, s_, eps, R, alpha, m)


def part_a_exact():
    # b = 1: alpha = 1 and m = eps/(1 - eps); every quantity is rational
    for s in (2, 3, 7, 50):
        s = Fraction(s)
        eps = 1 / s ** 2
        m = eps / (1 - eps)
        piy = {0: 1 - eps, 1: eps}
        piv = {1: (1 - m) / 2, -1: (1 + m) / 2}
        pi = [piy[y] * piv[v] for (y, v) in STATES]
        g = [(1 - y) * v + y for (y, v) in STATES]
        Eg = sum(p * x for p, x in zip(pi, g))
        Eg2 = sum(p * x * x for p, x in zip(pi, g))
        check("A9 exact rational b=1 s=%s: pi(g)=0, pi(g^2)=1, max|g|=1" % s,
              Eg == 0 and Eg2 == 1 and max(abs(x) for x in g) == 1 and sum(pi) == 1)


def sub_generator_no_y_jump(Q):
    # Q restricted to the states with y = 0 (indices 0, 1): V moves, a jump of Y kills
    return mp.matrix([[Q[0, 0], Q[0, 1]], [Q[1, 0], Q[1, 1]]])


def part_b(b, s, Q, pi, g, prm, quad):
    b_, s_, eps, R, alpha, m = prm
    tag = "b=%s s=%s" % (b, s)
    E = mp.expm(s_ * sub_generator_no_y_jump(Q))
    pH = sum(pi[i] * (E[i, 0] + E[i, 1]) for i in range(2))
    check("B1 P(H) = (1-eps) e^{-eps s} (sub-generator exponential), " + tag,
          abs(pH - (1 - eps) * mp.e ** (-eps * s_)) < mp.mpf(10) ** -20, "P(H)=%s" % mp.nstr(pH, 15))
    check("B2 P(H^c) <= eps (1 + s), " + tag, 1 - pH <= eps * (1 + s_))
    var_closed = 2 * (1 - m ** 2) * (s_ / R - (1 - mp.e ** (-R * s_)) / R ** 2)
    check("B3 var of int_0^s V du <= 2 (1 - m^2) s / R, " + tag, var_closed <= 2 * (1 - m ** 2) * s_ / R)
    if quad:
        # covariance of V from the 2x2 matrix exponential, integrated numerically
        QV = mp.matrix([[-R * (1 - m) / 2, R * (1 - m) / 2], [R * (1 + m) / 2, -R * (1 + m) / 2]])  # order (-1, 1)
        vv = [mp.mpf(-1), mp.mpf(1)]
        pv = [(1 + m) / 2, (1 - m) / 2]

        def cov(w):
            P = mp.expm(w * QV)
            return sum(pv[a] * vv[a] * P[a, c] * vv[c] for a in range(2) for c in range(2)) - m ** 2

        old = mp.mp.dps
        mp.mp.dps = 30
        var_quad = 2 * mp.quad(lambda w: (s_ - w) * cov(w), [0, 1 / R, 10 / R, 40 / R, s_])
        mp.mp.dps = old
        check("B4 var of int_0^s V du: closed form = quadrature of the matrix covariance, " + tag,
              abs(var_quad - var_closed) < mp.mpf(10) ** -18 * (1 + var_closed), "var=%s" % mp.nstr(var_closed, 12))
    # sigma^2 = 2 pi(g h), -Q h = g, pi(h) = 0, against the closed form; three rows of -Q h = g (the fourth is
    # implied, since pi(g) = 0) and the row pi(h) = 0
    M = mp.matrix(4, 4)
    rhs = mp.matrix(4, 1)
    for i in range(3):
        for j in range(4):
            M[i, j] = -Q[i, j]
        rhs[i] = g[i]
    for j in range(4):
        M[3, j] = pi[j]
    h = mp.lu_solve(M, rhs)
    resid = max(abs(-sum(Q[i, j] * h[j] for j in range(4)) - g[i]) for i in range(4))
    sig2_poisson = 2 * sum(pi[i] * g[i] * h[i] for i in range(4))
    sig2_closed = (2 * (b_ + alpha * m) ** 2 * eps * (1 - eps)
                   + 2 * alpha ** 2 * (1 - m ** 2) * (1 - eps) * ((1 - eps) / R + eps / (R + 1)))
    check("B5 sigma^2: Poisson equation = closed form, " + tag,
          resid < mp.mpf(10) ** -25 and abs(sig2_poisson - sig2_closed) < mp.mpf(10) ** -25 * sig2_closed,
          "sigma^2=%s s^2 sigma^2=%s" % (mp.nstr(sig2_closed, 12), mp.nstr(s_ ** 2 * sig2_closed, 12)))
    check("B6 b^2 eps <= sigma^2 <= 2 (b+1)^2 eps, " + tag, b_ ** 2 * eps <= sig2_closed <= 2 * (b_ + 1) ** 2 * eps)
    return sig2_closed


def bound(b, s):
    b_, s_, eps, R, alpha, m = params(b, s)
    return 1 - eps * (1 + s_) - 2 * (1 - m ** 2) / (R * m ** 2 * s_)


def part_c():
    worst = None
    for b in (1, mp.mpf("1.5"), 2, 3, 5, 10, 100):
        for s in sorted(set([2 * b, 2 * b + mp.mpf("0.5"), 3 * b, 10 * b, 100 * b, 1000 * b])):
            bd = bound(b, s)
            ok = bd >= 1 - 4 / mp.mpf(s)
            check("C1 1 - eps(1+s) - 2(1-m^2)/(R m^2 s) >= 1 - 4/s, b=%s s=%s" % (mp.nstr(b, 6), mp.nstr(s, 6)), ok,
                  "bound=%s 1-4/s=%s" % (mp.nstr(bd, 10), mp.nstr(1 - 4 / mp.mpf(s), 10)))
            gap = bd - (1 - 4 / mp.mpf(s))
            worst = gap if worst is None else min(worst, gap)
    print("     smallest margin over the grid: %s" % mp.nstr(worst, 10))


def numeric_chain(b, s):
    Q, pi, g, prm = chain(b, s)
    Qn = np.array([[float(Q[i, j]) for j in range(4)] for i in range(4)])
    return Qn, np.array([float(x) for x in pi]), np.array([float(x) for x in g]), [float(x) for x in prm]


def fourier_cdf0(b, s, theta_max=2000.0, h=0.004, chunk=20000):
    """P(S_s <= 0) by Gil-Pelaez: 1/2 - (1/pi) int_0^inf Im phi(theta)/theta dtheta, phi(theta) = pi^T exp(s(Q + i theta G)) 1.
    S_s has no atom at 0 (g never vanishes), so 0 is a continuity point. Midpoint rule; the cut at theta_max costs at most
    w/(pi b s theta_max) + O(theta_max^-2), w = P(Y = 1 on [0, s]), the weight of the atom of S_s at b s."""
    Qn, pin, gn, prm = numeric_chain(b, s)
    s = float(s)
    G = np.diag(gn)
    ths = np.arange(h / 2, theta_max, h)
    total = 0.0
    for k in range(0, len(ths), chunk):
        th = ths[k:k + chunk]
        E = expm(s * (Qn[None, :, :] + 1j * th[:, None, None] * G[None, :, :]))
        phi = E.sum(axis=2) @ pin
        total += (phi.imag / th).sum()
    return 0.5 - total * h / np.pi


def simulate_cdf0(b, s, n, seed):
    """P(S_s <= 0) by simulating Y and V independently from their rates."""
    Qn, pin, gn, prm = numeric_chain(b, s)
    b_, s_, eps, R, alpha, m = prm
    rng = np.random.default_rng(seed)
    neg = 0
    for _ in range(n):
        # Y path: list of intervals [a, c) on which Y = 1
        y = 1 if rng.random() < eps else 0
        t, ones = 0.0, []
        while t < s_:
            hold = rng.exponential(1 / ((1 - eps) if y == 1 else eps))
            if y == 1:
                ones.append((t, min(t + hold, s_)))
            t += hold
            y = 1 - y
        # V path: alternating holding times
        v = 1 if rng.random() < (1 - m) / 2 else -1
        rate = {1: R * (1 + m) / 2, -1: R * (1 - m) / 2}
        k = int(R * s_ * 1.2) + 1000
        times, vals = [0.0], [v]
        while times[-1] < s_:
            hold = rng.exponential(1.0, size=k)
            # alternate rates starting from the current value
            seq = np.empty(k)
            cur = vals[-1]
            seq[0::2] = 1 / rate[cur]
            seq[1::2] = 1 / rate[-cur]
            jumps = times[-1] + np.cumsum(hold * seq)
            times.extend(jumps.tolist())
            vals.extend([(-cur if i % 2 == 0 else cur) for i in range(k)])
        times = np.array(times)
        vals = np.array(vals, dtype=float)
        # integral of V over [0, s] and over the Y = 1 intervals
        edges = np.minimum(times, s_)
        seg = np.diff(edges) * vals[:-1]
        cum = np.concatenate([[0.0], np.cumsum(seg)])

        def int_v(x):
            i = np.searchsorted(edges, x, side="right") - 1
            return cum[i] + (x - edges[i]) * vals[i]

        total_v = int_v(s_)
        on_ones_v = sum(int_v(c) - int_v(a) for a, c in ones)
        time_ones = sum(c - a for a, c in ones)
        S = alpha * (total_v - on_ones_v) + b_ * time_ones
        neg += S <= 0
    return neg / n


def part_d():
    for b, s, n in ((1, 4, 20000), (2, 4, 20000), (1, 6, 10000), (3, 6, 10000), (2, 8, 5000)):
        f = fourier_cdf0(b, s)
        sim = simulate_cdf0(b, s, n, seed=1000 * b + s)
        se = (sim * (1 - sim) / n) ** 0.5
        lb = float(bound(b, s))
        check("D1 P(S_s <= 0) >= proof bound >= 1 - 4/s (Fourier), b=%s s=%s" % (b, s), f >= lb - 1e-3 and lb >= 1 - 4 / s,
              "Fourier=%.5f bound=%.5f 1-4/s=%.3f" % (f, lb, 1 - 4 / s))
        check("D2 simulation agrees with Fourier within 4 standard errors, b=%s s=%s" % (b, s), abs(sim - f) <= 4 * se + 1e-3,
              "simulated=%.4f (n=%d, se=%.4f)" % (sim, n, se))


def main():
    print("Part S: algebra, symbolic")
    part_s()
    print("Part A: algebra, 50 digits")
    part_a_exact()
    sig = {}
    for b in (1, mp.mpf("1.5"), 2, 3, 10):
        for s in (2 * b, 3 * b, 10 * b, 1000 * b):
            Q, pi, g, prm = part_a(b, s)
            print("Part B, b=%s s=%s" % (mp.nstr(b, 6), mp.nstr(s, 6)))
            sig[(b, s)] = part_b(b, s, Q, pi, g, prm, quad=(s <= 6))
    print("Part C: the bound of the proof")
    part_c()
    print("Part D: P(S_s <= 0) by Fourier inversion and by simulation")
    part_d()
    print()
    print("%d checks, %d failures" % (NCHECK[0], len(FAILS)))
    if FAILS:
        print("FAILED:", FAILS)


if __name__ == "__main__":
    main()
