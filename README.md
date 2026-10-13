# The relaxation time does not control the normal approximation of stationary additive functionals

Companion material for the paper of the same title (Y. Shmalo, October 2026). [Read the paper](paper/main.pdf).

Let X be a finite irreducible reversible Markov chain in continuous time with stationary distribution π and relaxation
time τ₂, and let g be a function on its states with E_π g = 0 and E_π g² = 1. Write S_t = ∫₀ᵗ g(X_u) du for the chain
started from π, and σ² for the asymptotic variance rate of S_t. Open Problem 4.30 of D. Aldous and J. A. Fill,
*Reversible Markov Chains and Random Walks on Graphs*, asks whether there is an explicit function ψ(b, s) → 0 as s → ∞,
not depending on the chain, such that

    sup_x | P_π( S_t / (σ t^{1/2}) ≤ x ) − P(Z ≤ x) | ≤ ψ(‖g‖_∞, t/τ₂)

for a standard normal variable Z. The paper shows that no such function exists.

**Theorem 1.** For every b ≥ 1 and s ≥ 2b there are an irreducible reversible chain on four states with τ₂ = 1 and a
function g with E_π g = 0, E_π g² = 1 and ‖g‖_∞ = b such that P_π(S_s ≤ 0) ≥ 1 − 4/s. So at t = s the distance above
is at least 1/2 − 4/s, and this stays true when σ s^{1/2} is replaced by any positive constant.

The chain is a pair of independent two-state chains: a slow one that sits at 0 except for rare visits to 1, where g = b,
and a fast sign that gives g = ±α a small negative drift while the slow chain is at 0. In these examples σ² is of order
s⁻² while τ₂ = 1. A Berry–Esseen bound of Lezaud (2001) gives the distance at most
26 b (τ₂/σ²)^{1/2} (t/τ₂)^{−1/2} + e^{−t/τ₂}, so the requested bound holds once σ²/τ₂ is bounded below; the examples show
that this dependence cannot be dropped, even for chains with four states.

## Contents

- `paper/main.tex`, `paper/main.pdf`: the paper.
- `code/checks.py`: symbolic checks of the identities (SymPy), the same checks and the bounds of the proof in 50-digit
  arithmetic (mpmath), and P_π(S_s ≤ 0) at five parameter pairs by Fourier inversion and by simulation (NumPy, SciPy).
  It needs Python 3 with SymPy, mpmath, NumPy and SciPy, and runs in about seven minutes. `code/checks_output.txt` is
  its output.
- `code/Bounds.lean`: the real-variable inequalities of the proof, checked with Lean 4.33.1 and Mathlib (commit
  0df444a360eaa60ab8c11dca51a86af692955474). `code/lean_output.txt` is the output of the check.
- `SHA256SUMS.txt`: checksums of the files above.

## Running the checks

    python code/checks.py > code/checks_output.txt

For the Lean file, in a Lake project that depends on Mathlib at the commit above:

    lake env lean Bounds.lean

## Citation

Y. Shmalo, The relaxation time does not control the normal approximation of stationary additive functionals, 2026,
https://github.com/yspennstate/relaxation-time-normal-approximation
