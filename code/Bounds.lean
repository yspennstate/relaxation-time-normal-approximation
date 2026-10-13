import Mathlib

/-!
The real-variable inequalities behind Theorem 1 of the paper.

For `b ≥ 1` and `s ≥ 2b` the paper takes `ε = 1/s²`, `R = s⁴`, `α > 0` with `α² (1 - ε) = 1 - b² ε`,
and `m = b ε / (α (1 - ε))`. Lemma 1 uses `3/4 ≤ α² ≤ 1` and `b ε ≤ m < 1/2` (`params`). The proof of
Theorem 1 uses `(1 - ε) e^{-ε s} ≥ 1 - ε (1 + s)` (`stay`) and
`ε (1 + s) + 2 (1 - m²) / (R m² s) ≤ 4/s` (`final`).
-/

theorem params {b s ε α m : ℝ} (hb : 1 ≤ b) (hs : 2 * b ≤ s) (hε : ε * s ^ 2 = 1) (hα : 0 < α)
    (hα2 : α ^ 2 * (1 - ε) = 1 - b ^ 2 * ε) (hm : m * (α * (1 - ε)) = b * ε) :
    3 / 4 ≤ α ^ 2 ∧ α ^ 2 ≤ 1 ∧ b * ε ≤ m ∧ m < 1 / 2 := by
  have hs2 : 2 ≤ s := by linarith
  have hspos : 0 < s := by linarith
  have hb0 : 0 < b := by linarith
  have hεpos : 0 < ε := by
    by_contra h
    have h' : ε ≤ 0 := not_lt.mp h
    linarith [mul_nonpos_of_nonpos_of_nonneg h' (sq_nonneg s)]
  have hs4 : 4 ≤ s ^ 2 := by linarith [mul_le_mul hs2 hs2 (by norm_num) hspos.le]
  have hεle : ε ≤ 1 / 4 := by linarith [mul_le_mul_of_nonneg_left hs4 hεpos.le]
  have h2b : (2 * b) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by linarith) hs 2
  have hbε : b ^ 2 * ε ≤ 1 / 4 := by linarith [mul_le_mul_of_nonneg_right h2b hεpos.le]
  have hb2 : 1 ≤ b ^ 2 := by linarith [mul_le_mul hb hb zero_le_one hb0.le]
  have hα2lo : 3 / 4 ≤ α ^ 2 := by linarith [mul_nonneg (sq_nonneg α) hεpos.le]
  have hα2hi : α ^ 2 ≤ 1 := by
    by_contra h
    have h' : 1 < α ^ 2 := not_le.mp h
    have h3 : 0 < (α ^ 2 - 1) * (1 - ε) := mul_pos (by linarith) (by linarith)
    linarith [mul_le_mul_of_nonneg_right hb2 hεpos.le]
  have hαhi : α ≤ 1 := by
    by_contra h
    have h' : 1 < α := not_le.mp h
    linarith [mul_lt_mul'' h' h' zero_le_one zero_le_one]
  have hαlo : 4 / 5 < α := by
    by_contra h
    have h' : α ≤ 4 / 5 := not_lt.mp h
    linarith [mul_le_mul h' h' hα.le (by norm_num)]
  have hden : 0 < α * (1 - ε) := mul_pos hα (by linarith)
  have hden1 : α * (1 - ε) ≤ 1 := by linarith [mul_nonneg hα.le hεpos.le]
  have hden2 : 3 / 5 < α * (1 - ε) := by
    linarith [mul_lt_mul hαlo (show (3 : ℝ) / 4 ≤ 1 - ε by linarith) (by norm_num) hα.le]
  have hmpos : 0 < m := by
    by_contra h
    have h' : m ≤ 0 := not_lt.mp h
    linarith [mul_nonpos_of_nonpos_of_nonneg h' hden.le, mul_pos hb0 hεpos]
  have hsε0 : 0 ≤ s * ε := by positivity
  have hsε : s * ε ≤ 1 / 2 := by linarith [mul_le_mul_of_nonneg_left hs2 hsε0]
  have hbε1 : b * ε ≤ 1 / 4 := by linarith [mul_le_mul_of_nonneg_right hs hεpos.le]
  refine ⟨hα2lo, hα2hi, ?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left hden1 hmpos.le]
  · by_contra h
    have h' : 1 / 2 ≤ m := not_lt.mp h
    linarith [mul_le_mul_of_nonneg_right h' hden.le]

theorem stay {ε s : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hs : 0 ≤ s) :
    1 - ε * (1 + s) ≤ (1 - ε) * Real.exp (-(ε * s)) := by
  have hx : 1 - ε * s ≤ Real.exp (-(ε * s)) := by
    have := Real.add_one_le_exp (-(ε * s))
    linarith
  have h1e : 0 ≤ 1 - ε := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hx h1e, mul_nonneg h0 (mul_nonneg h0 hs)]

theorem final {b s ε m : ℝ} (hb : 1 ≤ b) (hs : 2 * b ≤ s) (hε : ε * s ^ 2 = 1) (hm : b * ε ≤ m) :
    ε * (1 + s) + 2 * (1 - m ^ 2) / (s ^ 4 * m ^ 2 * s) ≤ 4 / s := by
  have hs2 : 2 ≤ s := by linarith
  have hspos : 0 < s := by linarith
  have hεpos : 0 < ε := by
    by_contra h
    have h' : ε ≤ 0 := not_lt.mp h
    nlinarith [sq_nonneg s]
  have hmpos : 0 < m := by nlinarith [mul_pos (by linarith : (0 : ℝ) < b) hεpos]
  have hsm : 1 ≤ s ^ 2 * m := by nlinarith [mul_le_mul_of_nonneg_left hm (sq_nonneg s)]
  have hfrac : 2 * (1 - m ^ 2) / (s ^ 4 * m ^ 2 * s) ≤ 2 / s := by
    rw [div_le_div_iff₀ (by positivity) hspos]
    have h4 : 1 ≤ (s ^ 2 * m) ^ 2 := by nlinarith
    nlinarith [sq_nonneg m, mul_le_mul_of_nonneg_left h4 hspos.le]
  have hfirst : ε * (1 + s) ≤ 3 / 2 / s := by
    rw [le_div_iff₀ hspos]
    nlinarith
  have hgap : 4 / s - 3 / 2 / s - 2 / s = 1 / 2 / s := by ring
  have hgap0 : 0 ≤ 1 / 2 / s := by positivity
  linarith

#print axioms params
#print axioms stay
#print axioms final
