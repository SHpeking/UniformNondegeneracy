module

public import UniformNondegeneracy.Analysis.Taylor
public import Mathlib.Analysis.Calculus.Taylor

@[expose] public section

open Filter Topology Set
open scoped RealInnerProductSpace

/-!
# Bregman differences and quadratic bounds
-/

noncomputable section

namespace UN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The Bregman difference of `E`, with expansion point `x₂`. -/
def bregman (E : H → ℝ) (x₁ x₂ : H) : ℝ :=
  E x₁ - E x₂ - ⟪gradient E x₂, x₁ - x₂⟫

@[simp] theorem bregman_self (E : H → ℝ) (x : H) :
    bregman E x x = 0 := by
  simp [bregman]

theorem bregman_add_reverse (E : H → ℝ) (x₁ x₂ : H) :
    bregman E x₁ x₂ + bregman E x₂ x₁ = ⟪gradient E x₁ - gradient E x₂, x₁ - x₂⟫ := by
  simp only [bregman, inner_sub_left, inner_sub_right]
  ring

theorem bregman_three_point (E : H → ℝ) (x₃ x₁ x₂ : H) :
    bregman E x₃ x₂ = bregman E x₁ x₂ + ⟪gradient E x₁ - gradient E x₂, x₃ - x₁⟫ + bregman E x₃ x₁ := by
  simp only [bregman, inner_sub_left, inner_sub_right]
  ring

/-- The second-order Bregman limit is half the Hessian quadratic form. -/
theorem bregman_second_order (hE : ContDiff ℝ 2 E) (x v : H) :
    Tendsto (fun ε : ℝ => bregman E (x + ε • v) x / ε ^ 2)
      (𝓝[≠] 0) (𝓝 (⟪(fderiv ℝ (gradient E) x) v, v⟫ / 2)) := by
  let f : ℝ → ℝ := fun ε => E (x + ε • v)
  let a := ⟪(fderiv ℝ (gradient E) x) v, v⟫
  have hLine (ε : ℝ) : HasDerivAt (fun ε : ℝ => x + ε • v) v ε := by
    simpa using ((hasDerivAt_id ε).smul_const v).const_add x
  have hf (ε : ℝ) : HasDerivAt f ⟪gradient E (x + ε • v), v⟫ ε :=
    (hE.differentiable (by norm_num) _).hasGradientAt.hasFDerivAt.comp_hasDerivAt ε (hLine ε)
  have hf' : deriv f = fun ε => ⟪gradient E (x + ε • v), v⟫ := funext fun ε => (hf ε).deriv
  have hg : HasDerivAt (fun ε : ℝ => gradient E (x + ε • v)) ((fderiv ℝ (gradient E) x) v) 0 := by
    simpa [Function.comp_def] using ((contDiff_gradient hE).differentiable one_ne_zero (x + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt 0 (hLine 0)
  have hf'' : deriv (deriv f) 0 = a := by
    rw [hf']
    simpa [a] using (hg.inner ℝ (hasDerivAt_const (0 : ℝ) v)).deriv
  have hTaylor (ε : ℝ) :
      taylorWithinEval f 2 univ 0 ε = E x + ε * ⟪gradient E x, v⟫ + ε ^ 2 / 2 * a := by
    simp only [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_univ, iteratedDeriv_succ, iteratedDeriv_zero, hf'']
    norm_num only [hf', f, zero_smul, add_zero, sub_zero, Nat.factorial, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, pow_one, pow_zero, one_mul, div_one, smul_eq_mul]
    ring
  have hSmooth : ContDiff ℝ 2 f := hE.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hLimit : Tendsto (fun ε : ℝ => (f ε - taylorWithinEval f 2 univ 0 ε) / (ε - 0) ^ 2) (𝓝[≠] 0) (𝓝 0) := (taylor_isLittleO_univ (n := 2) hSmooth).tendsto_div_nhds_zero.mono_left nhdsWithin_le_nhds
  have h := hLimit.add_const (a / 2)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := hε
  rw [hTaylor]
  dsimp [f, bregman]
  simp only [sub_zero, add_sub_cancel_left, real_inner_smul_right]
  field_simp
  ring

/-- Reversing the Bregman difference gives the same second-order limit. -/
theorem bregman_second_order_reverse (hE : ContDiff ℝ 2 E) (x v : H) :
    Tendsto (fun ε : ℝ => bregman E x (x + ε • v) / ε ^ 2)
      (𝓝[≠] 0) (𝓝 (⟪(fderiv ℝ (gradient E) x) v, v⟫ / 2)) := by
  have hLine : HasDerivAt (fun ε : ℝ => x + ε • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hg := ((contDiff_gradient hE).differentiable one_ne_zero (x + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt 0 hLine
  have hSlope : Tendsto (fun ε : ℝ => ε⁻¹ • (gradient E (x + ε • v) - gradient E x))
      (𝓝[≠] 0) (𝓝 ((fderiv ℝ (gradient E) x) v)) := by
    have hh := hg.tendsto_slope
    change Tendsto (fun ε : ℝ => (ε - 0)⁻¹ • (gradient E (x + ε • v) - gradient E (x + (0 : ℝ) • v))) _ _ at hh
    simpa only [sub_zero, zero_smul, add_zero] using hh
  have h := (hSlope.inner (tendsto_const_nhds (x := v))).sub (bregman_second_order hE x v)
  convert h.congr' ?_ using 1
  · congr 1
    ring
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := hε
  have hSum := bregman_add_reverse E (x + ε • v) x
  simp only [add_sub_cancel_left, real_inner_smul_right] at hSum
  simp only [real_inner_smul_left]
  field_simp
  nlinarith [hSum]

/-- Global lower and upper quadratic bounds on the Bregman difference of an energy. -/
structure HasBregmanBounds (LPlus LMinus : ℝ) (E : H → ℝ) : Prop where
  lower : ∀ x₁ x₂, -(LMinus / 2) * ‖x₁ - x₂‖ ^ 2 ≤ bregman E x₁ x₂
  upper : ∀ x₁ x₂, bregman E x₁ x₂ ≤ LPlus / 2 * ‖x₁ - x₂‖ ^ 2

namespace HasBregmanBounds

variable {E : H → ℝ} {LPlus LMinus : ℝ}

theorem hasGradientAt (hBounds : HasBregmanBounds LPlus LMinus E) (x : H) :
    HasGradientAt E (gradient E x) x :=
  hasGradientAt_of_quadratic_bounds (fun y => hBounds.lower y x) (fun y => hBounds.upper y x)

theorem differentiable (hBounds : HasBregmanBounds LPlus LMinus E) : Differentiable ℝ E :=
  fun x => (hBounds.hasGradientAt x).differentiableAt

/-- Enlarging either outer bound preserves the quadratic estimates. -/
theorem mono (hBounds : HasBregmanBounds LPlus LMinus E)
    {LPlus' LMinus' : ℝ} (hPlus : LPlus ≤ LPlus') (hMinus : LMinus ≤ LMinus') :
    HasBregmanBounds LPlus' LMinus' E := by
  constructor
  · intro x₁ x₂
    exact (mul_le_mul_of_nonneg_right (by linarith : -(LMinus' / 2) ≤ -(LMinus / 2))
      (sq_nonneg _)).trans (hBounds.lower x₁ x₂)
  · intro x₁ x₂
    exact (hBounds.upper x₁ x₂).trans
      (mul_le_mul_of_nonneg_right (by linarith : LPlus / 2 ≤ LPlus' / 2) (sq_nonneg _))

omit [CompleteSpace H] in
private lemma interpolation_cost (u v : H) (a b : ℝ) (hab : a + b ≠ 0) :
    let w := (b / (a + b)) • u + (a + b)⁻¹ • v
    ⟪v, u - w⟫ + b / 2 * ‖w - u‖ ^ 2 + a / 2 * ‖w‖ ^ 2 =
      (a * b * ‖u‖ ^ 2 + 2 * a * ⟪u, v⟫ - ‖v‖ ^ 2) / (2 * (a + b)) := by
  dsimp
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm v u]
  field_simp
  ring

/-- Interpolate the two quadratic models at their optimal common trial point. -/
theorem interpolation_upper (hBounds : HasBregmanBounds LPlus LMinus E)
    (hSum : 0 < LPlus + LMinus) (x₁ x₂ : H) :
    bregman E x₁ x₂ ≤
      (LPlus * LMinus * ‖x₁ - x₂‖ ^ 2 + 2 * LPlus * ⟪x₁ - x₂, gradient E x₁ - gradient E x₂⟫ - ‖gradient E x₁ - gradient E x₂‖ ^ 2) / (2 * (LPlus + LMinus)) := by
  let u := x₁ - x₂
  let v := gradient E x₁ - gradient E x₂
  let w := (LMinus / (LPlus + LMinus)) • u + (LPlus + LMinus)⁻¹ • v
  let ξ := x₂ + w
  have hLower := hBounds.lower ξ x₁
  have hUpper := hBounds.upper ξ x₂
  have hIdentity : bregman E x₁ x₂ = ⟪v, x₁ - ξ⟫ - bregman E ξ x₁ + bregman E ξ x₂ := by
    simp only [bregman, v, inner_sub_left, inner_sub_right]
    ring
  have hξ₁ : ξ - x₁ = w - u := by dsimp [ξ, u]; abel
  have h₁ξ : x₁ - ξ = u - w := by dsimp [ξ, u]; abel
  have hξ₂ : ξ - x₂ = w := by dsimp [ξ]; abel
  calc
    _ ≤ ⟪v, x₁ - ξ⟫ + LMinus / 2 * ‖ξ - x₁‖ ^ 2 + LPlus / 2 * ‖ξ - x₂‖ ^ 2 := by
      rw [hIdentity]
      nlinarith
    _ = _ := by
      rw [hξ₁, h₁ξ, hξ₂]
      exact interpolation_cost u v LPlus LMinus hSum.ne'

end HasBregmanBounds

end UN
