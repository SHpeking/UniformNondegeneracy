module

public import UniformNondegeneracy.Analysis.Taylor

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Bregman differences and quadratic bounds
-/

namespace UN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The first-order remainder of `E` relative to `g`, with expansion point `x₂`. -/
def bregman (E : H → ℝ) (g : H → H) (x₁ x₂ : H) : ℝ :=
  E x₁ - E x₂ - ⟪g x₂, x₁ - x₂⟫

@[simp] theorem bregman_self (E : H → ℝ) (g : H → H) (x : H) :
    bregman E g x x = 0 := by
  simp [bregman]

theorem bregman_add_reverse (E : H → ℝ) (g : H → H) (x₁ x₂ : H) :
    bregman E g x₁ x₂ + bregman E g x₂ x₁ = ⟪g x₁ - g x₂, x₁ - x₂⟫ := by
  simp only [bregman, inner_sub_left, inner_sub_right]
  ring

theorem bregman_three_point (E : H → ℝ) (g : H → H) (x₃ x₁ x₂ : H) :
    bregman E g x₃ x₂ = bregman E g x₁ x₂ + ⟪g x₁ - g x₂, x₃ - x₁⟫ + bregman E g x₃ x₁ := by
  simp only [bregman, inner_sub_left, inner_sub_right]
  ring

/-- Global lower and upper quadratic bounds on `bregman E g`. -/
structure HasBregmanBounds (E : H → ℝ) (g : H → H) (LPlus LMinus : ℝ) : Prop where
  lower : ∀ x₁ x₂, -(LMinus / 2) * ‖x₁ - x₂‖ ^ 2 ≤ bregman E g x₁ x₂
  upper : ∀ x₁ x₂, bregman E g x₁ x₂ ≤ LPlus / 2 * ‖x₁ - x₂‖ ^ 2

namespace HasBregmanBounds

variable {E : H → ℝ} {g : H → H} {LPlus LMinus : ℝ}

/-- Quadratic Bregman bounds imply that `g` is the gradient of `E`. -/
theorem hasGradientAt [CompleteSpace H] (hBounds : HasBregmanBounds E g LPlus LMinus) (x : H) :
    HasGradientAt E (g x) x := by
  apply hasGradientAt_iff_isLittleO.mpr
  have hO : (fun x₁ => bregman E g x₁ x) =O[nhds x] (fun x₁ => ‖x₁ - x‖ ^ 2) := by
    apply Asymptotics.isBigO_of_le' (c := max |LPlus| |LMinus| / 2) (nhds x)
    intro x₁
    simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x₁ - x‖)]
    apply abs_le.mpr
    constructor
    · have h := hBounds.lower x₁ x
      have hm : LMinus ≤ max |LPlus| |LMinus| := (le_abs_self _).trans (le_max_right _ _)
      nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sq_nonneg ‖x₁ - x‖)]
    · have h := hBounds.upper x₁ x
      have hm : LPlus ≤ max |LPlus| |LMinus| := (le_abs_self _).trans (le_max_left _ _)
      nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sq_nonneg ‖x₁ - x‖)]
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub x (by norm_num : 1 < 2))

/-- Enlarging either outer bound preserves the quadratic estimates. -/
theorem mono (hBounds : HasBregmanBounds E g LPlus LMinus)
    {LPlus' LMinus' : ℝ} (hPlus : LPlus ≤ LPlus') (hMinus : LMinus ≤ LMinus') :
    HasBregmanBounds E g LPlus' LMinus' := by
  constructor
  · intro x₁ x₂
    exact (mul_le_mul_of_nonneg_right (by linarith : -(LMinus' / 2) ≤ -(LMinus / 2))
      (sq_nonneg _)).trans (hBounds.lower x₁ x₂)
  · intro x₁ x₂
    exact (hBounds.upper x₁ x₂).trans
      (mul_le_mul_of_nonneg_right (by linarith : LPlus / 2 ≤ LPlus' / 2) (sq_nonneg _))

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
theorem interpolation_upper (hBounds : HasBregmanBounds E g LPlus LMinus)
    (hSum : 0 < LPlus + LMinus) (x₁ x₂ : H) :
    bregman E g x₁ x₂ ≤
      (LPlus * LMinus * ‖x₁ - x₂‖ ^ 2 + 2 * LPlus * ⟪x₁ - x₂, g x₁ - g x₂⟫ - ‖g x₁ - g x₂‖ ^ 2) / (2 * (LPlus + LMinus)) := by
  let u := x₁ - x₂
  let v := g x₁ - g x₂
  let w := (LMinus / (LPlus + LMinus)) • u + (LPlus + LMinus)⁻¹ • v
  let ξ := x₂ + w
  have hLower := hBounds.lower ξ x₁
  have hUpper := hBounds.upper ξ x₂
  have hIdentity : bregman E g x₁ x₂ = ⟪v, x₁ - ξ⟫ - bregman E g ξ x₁ + bregman E g ξ x₂ := by
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
