# The relaxation time does not control the normal approximation of stationary additive functionals

Companion material for the paper of the same title (Y. Shmalo, October 2026). [Read the paper](paper/main.pdf).

Let X be a finite irreducible reversible Markov chain in continuous time with stationary distribution π and relaxation
time τ₂, and let g be a function on its states with E_π g = 0 and E_π g² = 1. Write S_t = ∫₀ᵗ g(X_u) du for the chain
started from π, and σ² for the asymptotic variance rate of S_t. Open Problem 4.30 of D. Aldous and J. A. Fill,
*Reversible Markov Chains and Random Walks on Graphs*, asks whether there is an explicit function ψ(b, s) → 0 as s → ∞,
not depending on the chain, such that

    sup_x | P_π( S_t / (σ t^{1/2}) ≤ x ) − P(Z ≤ x) | ≤ ψ(‖g‖_∞, t/τ₂)

for a standard normal variable Z. The paper shows that no such function exists.

- Theorem 1. For every s ≥ 2 there are a reversible chain on four states with τ₂ = 1 and a function g with
  E_π g = 0, E_π g² = 1 and ‖g‖_∞ = 2 such that P_π(S_s ≤ 0) ≥ 1 − 6/s. So at t = s the distance above is at least
  1/2 − 6/s, and this stays true when σ s^{1/2} is replaced by any positive constant.
- Theorem 2. For every b ≥ 1 and s > b there are a reversible chain on eight states with τ₂ = 1 and a function g with
  E_π g = 0, E_π g² = 1 and ‖g‖_∞ = b such that at t = s the distance above is at least 1/2 − 5 s^{−2/3}.

In these examples σ² is of order s⁻² while τ₂ = 1. A Berry–Esseen bound of Lezaud (2001) gives the distance at most
26 b (τ₂/σ²)^{1/2} (t/τ₂)^{−1/2} + e^{−t/τ₂}, so the requested bound holds once σ²/τ₂ is bounded below; the examples show
that this dependence cannot be dropped, even for chains with a fixed number of states.

## Contents

- `paper/main.tex`, `paper/main.pdf`: the paper.
- `code/checks.py`: exact rational checks of the algebraic identities and numerical checks of the bounds (Python 3 with
  mpmath). `code/checks_output.txt` is its output.
- `SHA256SUMS.txt`: checksums of the files above.

## Running the checks

    python code/checks.py > code/checks_output.txt

## Citation

Y. Shmalo, The relaxation time does not control the normal approximation of stationary additive functionals, 2026,
https://github.com/yspennstate/relaxation-time-normal-approximation
