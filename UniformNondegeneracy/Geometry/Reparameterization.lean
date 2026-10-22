module

public import UniformNondegeneracy.Geometry.Transforms

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Changing curvature bounds

UN is preserved when the inner gap shrinks and the outer interval expands. Subtracting a quadratic with curvature in the inner gap gives symmetric bounds around the new origin.
-/

noncomputable section

namespace UN.IsUN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {bounds : CurvatureBounds} {E : H → ℝ}

local notation "g" => gradient E

/-- Lower bound for gradient secants measured relative to curvature `c`. -/
theorem gradient_lower_bound_at (hUN : IsUN bounds E) (c : ℝ) (x₁ x₂ : H) :
    bounds.innerRadiusAt c * ‖x₁ - x₂‖ ≤ ‖g x₁ - g x₂ - c • (x₁ - x₂)‖ := by
  have ht := norm_add_le (g x₁ - g x₂ - c • (x₁ - x₂)) ((c - bounds.innerCenter) • (x₁ - x₂))
  rw [show g x₁ - g x₂ - c • (x₁ - x₂) + (c - bounds.innerCenter) • (x₁ - x₂) =
      g x₁ - g x₂ - bounds.innerCenter • (x₁ - x₂) by module,
    norm_smul, Real.norm_eq_abs, abs_sub_comm] at ht
  rw [bounds.innerRadiusAt_eq]
  nlinarith [hUN.inner_centered x₁ x₂]

/-- Upper bound for gradient secants measured relative to curvature `c`. -/
theorem gradient_upper_bound_at (hUN : IsUN bounds E) (c : ℝ) (x₁ x₂ : H) :
    ‖g x₁ - g x₂ - c • (x₁ - x₂)‖ ≤ bounds.outerRadiusAt c * ‖x₁ - x₂‖ := by
  have ht := norm_add_le (g x₁ - g x₂ - bounds.outerCenter • (x₁ - x₂)) ((bounds.outerCenter - c) • (x₁ - x₂))
  rw [show g x₁ - g x₂ - bounds.outerCenter • (x₁ - x₂) + (bounds.outerCenter - c) • (x₁ - x₂) =
      g x₁ - g x₂ - c • (x₁ - x₂) by module,
    norm_smul, Real.norm_eq_abs] at ht
  rw [bounds.outerRadiusAt_eq]
  nlinarith [hUN.outer_centered x₁ x₂]

/-- Shrinking the inner gap and enlarging the outer interval preserves UN. -/
theorem mono (hUN : IsUN bounds E) {bounds' : CurvatureBounds}
    (hMuPlus : bounds'.muPlus ≤ bounds.muPlus) (hMuMinus : bounds'.muMinus ≤ bounds.muMinus)
    (hLPlus : bounds.lPlus ≤ bounds'.lPlus) (hLMinus : bounds.lMinus ≤ bounds'.lMinus) :
    IsUN bounds' E := by
  have hInner : bounds'.innerRadius ≤ bounds.innerRadiusAt bounds'.innerCenter := by
    dsimp [CurvatureBounds.innerRadiusAt, CurvatureBounds.innerRadius, CurvatureBounds.innerCenter]
    apply le_min <;> linarith
  have hOuter : bounds.outerRadiusAt bounds'.outerCenter ≤ bounds'.outerRadius := by
    dsimp [CurvatureBounds.outerRadiusAt, CurvatureBounds.outerRadius, CurvatureBounds.outerCenter]
    apply max_le <;> linarith
  refine ⟨hUN.contDiff, ?_, ?_⟩
  · intro x₁ x₂
    have h := (mul_le_mul_of_nonneg_right hInner (norm_nonneg (x₁ - x₂))).trans
      (hUN.gradient_lower_bound_at bounds'.innerCenter x₁ x₂)
    rw [← centered_secant_identity]
    change 0 ≤ ‖g x₁ - g x₂ - bounds'.innerCenter • (x₁ - x₂)‖ ^ 2 - bounds'.innerRadius ^ 2 * ‖x₁ - x₂‖ ^ 2
    have hn := mul_nonneg bounds'.innerRadius_pos.le (norm_nonneg (x₁ - x₂))
    nlinarith [norm_nonneg (g x₁ - g x₂ - bounds'.innerCenter • (x₁ - x₂))]
  · intro x₁ x₂
    have h := (hUN.gradient_upper_bound_at bounds'.outerCenter x₁ x₂).trans
      (mul_le_mul_of_nonneg_right hOuter (norm_nonneg (x₁ - x₂)))
    rw [← centered_secant_identity]
    change ‖g x₁ - g x₂ - bounds'.outerCenter • (x₁ - x₂)‖ ^ 2 - bounds'.outerRadius ^ 2 * ‖x₁ - x₂‖ ^ 2 ≤ 0
    nlinarith [norm_nonneg (g x₁ - g x₂ - bounds'.outerCenter • (x₁ - x₂))]

/-- Centering at a curvature in the inner gap gives symmetric UN bounds. -/
theorem centered (hUN : IsUN bounds E) (c : ℝ)
    (hLower : -bounds.muMinus < c) (hUpper : c < bounds.muPlus) (x₂ : H) :
    IsUN (bounds.centered c hLower hUpper) (UN.quadraticShift E c x₂) :=
  (hUN.quadraticShift c hLower hUpper x₂).mono
    (min_le_left _ _) (min_le_right _ _) (le_max_left _ _) (le_max_right _ _)

end UN.IsUN
