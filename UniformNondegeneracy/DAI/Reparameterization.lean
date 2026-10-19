module

public import UniformNondegeneracy.DAI.Admissibility
public import UniformNondegeneracy.Geometry.Transforms

@[expose] public section

/-!
# UN reparameterization at descent–ascent scales
-/

noncomputable section
namespace UN

open DAI
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {bounds : CurvatureBounds} {E : H → ℝ} {g : H → H}

local notation "xStar" => stationaryPoint g
namespace IsUN

private theorem centered_lower (hUN : IsUN bounds E g) {Λ : Scales}
    (x₁ x₂ : H) :
    gapMargin bounds Λ * ‖x₁ - x₂‖ ≤ ‖g x₁ - g x₂ - Λ.center • (x₁ - x₂)‖ := by
  have ht := norm_add_le (g x₁ - g x₂ - Λ.center • (x₁ - x₂))
    ((Λ.center - bounds.innerCenter) • (x₁ - x₂))
  rw [show g x₁ - g x₂ - Λ.center • (x₁ - x₂) + (Λ.center - bounds.innerCenter) • (x₁ - x₂) =
      g x₁ - g x₂ - bounds.innerCenter • (x₁ - x₂) by module,
    norm_smul, Real.norm_eq_abs, abs_sub_comm] at ht
  rw [gapMargin_eq_innerRadius_sub_abs bounds Λ]
  nlinarith [hUN.inner_centered x₁ x₂]

private theorem centered_upper (hUN : IsUN bounds E g) {Λ : Scales}
    (x₁ x₂ : H) :
    ‖g x₁ - g x₂ - Λ.center • (x₁ - x₂)‖ ≤ centeredOuterRadius bounds Λ * ‖x₁ - x₂‖ := by
  have ht := norm_add_le (g x₁ - g x₂ - bounds.outerCenter • (x₁ - x₂))
    ((bounds.outerCenter - Λ.center) • (x₁ - x₂))
  rw [show g x₁ - g x₂ - bounds.outerCenter • (x₁ - x₂) + (bounds.outerCenter - Λ.center) • (x₁ - x₂) =
      g x₁ - g x₂ - Λ.center • (x₁ - x₂) by module,
    norm_smul, Real.norm_eq_abs] at ht
  rw [centeredOuterRadius_eq bounds Λ]
  nlinarith [hUN.outer_centered x₁ x₂]

/-- Reparameterization at descent–ascent scales: take the largest inner interval centered at `Λ.center` contained in the original gap, and enlarge the outer bounds to the selected scales. -/
theorem effectiveBounds (hUN : IsUN bounds E g) {Λ : Scales}
    (hAdmissible : Admissible bounds Λ) :
    IsUN hAdmissible.effectiveBounds E g := by
  have hc : (effectiveMuPlus bounds Λ - effectiveMuMinus bounds Λ) / 2 = Λ.center := by
    unfold effectiveMuPlus effectiveMuMinus; ring
  have hr : (effectiveMuPlus bounds Λ + effectiveMuMinus bounds Λ) / 2 = gapMargin bounds Λ := by
    unfold effectiveMuPlus effectiveMuMinus; ring
  refine ⟨hUN.has_gradient, ?_, ?_⟩
  · intro x₁ x₂
    dsimp [Admissible.effectiveBounds]
    rw [← centered_secant_identity, hc, hr]
    have h := centered_lower hUN (Λ := Λ) x₁ x₂
    have hnonneg := mul_nonneg hAdmissible.gapMargin_pos.le (norm_nonneg (x₁ - x₂))
    nlinarith [norm_nonneg (g x₁ - g x₂ - Λ.center • (x₁ - x₂))]
  · intro x₁ x₂
    dsimp [Admissible.effectiveBounds]
    rw [← centered_secant_identity]
    change ‖g x₁ - g x₂ - Λ.center • (x₁ - x₂)‖ ^ 2 - Λ.radius ^ 2 * ‖x₁ - x₂‖ ^ 2 ≤ 0
    have houter := hAdmissible.toOuterCompatible.centeredOuterRadius_le_radius
    have h := (centered_upper hUN (Λ := Λ) x₁ x₂).trans
      (mul_le_mul_of_nonneg_right houter (norm_nonneg (x₁ - x₂)))
    nlinarith [norm_nonneg (g x₁ - g x₂ - Λ.center • (x₁ - x₂))]

/-- The centered energy has symmetric curvature bounds. -/
theorem centered (hUN : IsUN bounds E g) {Λ : Scales}
    (hAdmissible : Admissible bounds Λ) :
    IsUN hAdmissible.centeredBounds (UN.quadraticShift E Λ.center xStar) (fun x₁ => g x₁ - Λ.center • (x₁ - xStar)) := by
  have hshift := hUN.quadraticShift Λ.center hAdmissible.center_mem_gap.1
    hAdmissible.center_mem_gap.2 xStar
  refine ⟨hshift.has_gradient, ?_, ?_⟩
  · intro x₁ x₂
    dsimp [Admissible.centeredBounds]
    rw [← centered_secant_identity]
    simp only [sub_self, zero_div, zero_smul, sub_zero, add_self_div_two]
    rw [show g x₁ - Λ.center • (x₁ - xStar) - (g x₂ - Λ.center • (x₂ - xStar)) =
        g x₁ - g x₂ - Λ.center • (x₁ - x₂) by module]
    have h := centered_lower hUN (Λ := Λ) x₁ x₂
    have hnonneg := mul_nonneg hAdmissible.gapMargin_pos.le (norm_nonneg (x₁ - x₂))
    nlinarith [norm_nonneg (g x₁ - g x₂ - Λ.center • (x₁ - x₂))]
  · intro x₁ x₂
    dsimp [Admissible.centeredBounds]
    rw [← centered_secant_identity]
    simp only [sub_self, zero_div, zero_smul, sub_zero, add_self_div_two]
    rw [show g x₁ - Λ.center • (x₁ - xStar) - (g x₂ - Λ.center • (x₂ - xStar)) =
        g x₁ - g x₂ - Λ.center • (x₁ - x₂) by module]
    have h := centered_upper hUN (Λ := Λ) x₁ x₂
    nlinarith [norm_nonneg (g x₁ - g x₂ - Λ.center • (x₁ - x₂))]

end IsUN
end UN
