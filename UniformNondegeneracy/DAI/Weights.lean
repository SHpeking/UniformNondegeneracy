module

public import UniformNondegeneracy.DAI.Admissibility

@[expose] public section

/-!
# DAI weight families

Balanced weights for the secant bounds and compatible weights for the UN-to-DAI theorem.
-/

namespace UN.DAI
noncomputable section

/-- Balanced weights at the outer scales, with common numerator equal to the outer radius. -/
def outerSecantWeights (bounds : CurvatureBounds) : Weights :=
  balancedWeights (outerScales bounds) (outerScales bounds).radius (outerScales bounds).radius_pos.le

/-- Balanced weights recovering the inner secant at the balanced scales. -/
def innerSecantWeights (bounds : CurvatureBounds) : Weights :=
  balancedWeights (balancedScales bounds)
    (Real.sqrt (bounds.maxBandWidth * (bounds.maxBandWidth + bounds.muPlus + bounds.muMinus))) (Real.sqrt_nonneg _)

theorem outerSecantWeights_balanced (bounds : CurvatureBounds) :
    (outerSecantWeights bounds).Balanced (outerScales bounds) :=
  balancedWeights_balanced _ _ _

theorem outerSecantWeights_pos (bounds : CurvatureBounds) :
    0 < (outerSecantWeights bounds).plus ∧ 0 < (outerSecantWeights bounds).minus :=
  ⟨div_pos (outerScales bounds).radius_pos (outerScales bounds).minus_pos,
    div_pos (outerScales bounds).radius_pos (outerScales bounds).plus_pos⟩

theorem innerSecantWeights_balanced (bounds : CurvatureBounds) :
    (innerSecantWeights bounds).Balanced (balancedScales bounds) :=
  balancedWeights_balanced _ _ _

theorem innerSecantWeights_product (bounds : CurvatureBounds) :
    (innerSecantWeights bounds).plus * (innerSecantWeights bounds).minus *
      ((balancedScales bounds).plus * (balancedScales bounds).minus) =
      bounds.maxBandWidth * (bounds.maxBandWidth + bounds.muPlus + bounds.muMinus) := by
  unfold innerSecantWeights
  rw [balancedWeights_product, Real.sq_sqrt]
  exact mul_nonneg bounds.maxBandWidth_nonneg
    (by linarith [bounds.maxBandWidth_nonneg, bounds.muPlus_pos, bounds.muMinus_pos])

namespace Admissible

variable {bounds : CurvatureBounds} {Λ : Scales}

/-- Weights with product `q bounds Λ`, used in the ADA Lyapunov estimate. -/
def canonicalWeights (hAdmissible : Admissible bounds Λ) : Weights where
  plus := q bounds Λ * Λ.tauMinus / Λ.tauPlus
  minus := Λ.tauPlus / Λ.tauMinus
  plus_nonneg := div_nonneg (mul_nonneg hAdmissible.toOuterCompatible.q_nonneg Λ.tauMinus_pos.le) Λ.tauPlus_pos.le
  minus_nonneg := div_nonneg Λ.tauPlus_pos.le Λ.tauMinus_pos.le

theorem canonicalWeights_product (hAdmissible : Admissible bounds Λ) :
    hAdmissible.canonicalWeights.plus * hAdmissible.canonicalWeights.minus = q bounds Λ := by
  dsimp [canonicalWeights]
  field_simp [ne_of_gt Λ.tauPlus_pos, ne_of_gt Λ.tauMinus_pos]

theorem canonicalWeights_plus_lower (hAdmissible : Admissible bounds Λ) :
    (Λ.radius - gapMargin bounds Λ) / Λ.minus ≤ hAdmissible.canonicalWeights.plus := by
  have hdr : gapMargin bounds Λ ≤ Λ.radius := by
    have h := (effectiveMuPlus_le_muPlus bounds Λ).trans
      (bounds.muPlus_le_lPlus.trans hAdmissible.lPlus_le_plus)
    dsimp [effectiveMuPlus, Scales.radius, Scales.center, Scales.difference] at *
    linarith
  have hcd := hAdmissible.effectiveMuPlus_pos
  dsimp [effectiveMuPlus] at hcd
  have hidentity : hAdmissible.canonicalWeights.plus =
      (Λ.radius ^ 2 - gapMargin bounds Λ ^ 2) / Λ.minus ^ 2 := by
    dsimp [canonicalWeights, Scales.tauMinus, Scales.tauPlus]
    rw [hAdmissible.q_eq_radius_gapMargin]
    field_simp [ne_of_gt Λ.plus_pos, ne_of_gt Λ.minus_pos]
  rw [hidentity]
  apply (div_le_div_iff₀ Λ.minus_pos (sq_pos_of_pos Λ.minus_pos)).mpr
  have hprod := mul_nonneg (sub_nonneg.mpr hdr) hcd.le
  have hrc : Λ.radius - Λ.minus = Λ.center := by
    unfold Scales.radius Scales.center Scales.difference; ring
  nlinarith [mul_nonneg Λ.minus_pos.le hprod]

theorem canonicalWeights_minus_lower (hAdmissible : Admissible bounds Λ) :
    (Λ.radius - gapMargin bounds Λ) / Λ.plus ≤ hAdmissible.canonicalWeights.minus := by
  have hid : hAdmissible.canonicalWeights.minus = Λ.minus / Λ.plus := by
    dsimp [canonicalWeights, Scales.tauMinus, Scales.tauPlus]
    field_simp
  rw [hid]
  apply (div_le_div_iff_of_pos_right Λ.plus_pos).mpr
  have h := (abs_lt.mp hAdmissible.abs_center_lt_gapMargin).2
  dsimp [Scales.center, Scales.difference, Scales.radius] at *
  linarith

end Admissible

/-- Weight conditions for the DAI family on the admissible scale region. -/
structure CompatibleWeights (bounds : CurvatureBounds) (Λ : Scales) (ρ : Weights) : Prop where
  plus_lower : (Λ.radius - gapMargin bounds Λ) / Λ.minus ≤ ρ.plus
  minus_lower : (Λ.radius - gapMargin bounds Λ) / Λ.plus ≤ ρ.minus

  product_lower : q bounds Λ ≤ ρ.plus * ρ.minus

theorem Admissible.canonicalWeights_compatible {bounds : CurvatureBounds} {Λ : Scales}
    (hAdmissible : Admissible bounds Λ) :
    CompatibleWeights bounds Λ hAdmissible.canonicalWeights := by
  exact ⟨hAdmissible.canonicalWeights_plus_lower, hAdmissible.canonicalWeights_minus_lower,
    hAdmissible.canonicalWeights_product.ge⟩

/-- Reduce compatible positive weights to the boundary where their product is exactly `q`. -/
theorem CompatibleWeights.exists_product_eq
    {bounds : CurvatureBounds} {Λ : Scales} {ρ : Weights}
    (hCompatible : CompatibleWeights bounds Λ ρ)
    (hStrict : StrictAdmissible bounds Λ) (hplus : 0 < ρ.plus) :
    ∃ a b : ℝ,
      0 < a ∧ 0 < b ∧
      a ≤ ρ.plus ∧ b ≤ ρ.minus ∧
      (Λ.radius - gapMargin bounds Λ) / Λ.minus ≤ a ∧
      (Λ.radius - gapMargin bounds Λ) / Λ.plus ≤ b ∧
      a * b = q bounds Λ ∧
      a ≤ (Λ.radius + gapMargin bounds Λ) / Λ.minus := by
  let low := (Λ.radius - gapMargin bounds Λ) / Λ.plus
  let high := (Λ.radius + gapMargin bounds Λ) / Λ.minus
  have hdist : gapMargin bounds Λ < Λ.radius :=
    (gapMargin_le_centeredOuterRadius bounds Λ).trans_lt
      hStrict.centeredOuterRadius_lt_radius
  have hlow : 0 < low := div_pos (sub_pos.mpr hdist) Λ.plus_pos
  have hhigh : 0 < high := div_pos
    (add_pos Λ.radius_pos hStrict.toAdmissible.gapMargin_pos) Λ.minus_pos
  have hproduct : high * low = q bounds Λ := by
    rw [hStrict.toAdmissible.q_eq_radius_gapMargin]
    dsimp [high, low]
    field_simp; ring
  have horder : (Λ.radius - gapMargin bounds Λ) / Λ.minus ≤ high := by
    apply (div_le_div_iff_of_pos_right Λ.minus_pos).mpr
    linarith [hStrict.toAdmissible.gapMargin_pos]
  by_cases hcase : ρ.plus ≤ high
  · refine ⟨ρ.plus, q bounds Λ / ρ.plus, hplus,
      div_pos hStrict.q_pos hplus, le_rfl, ?_, hCompatible.plus_lower, ?_, ?_, hcase⟩
    · exact (div_le_iff₀ hplus).mpr (by nlinarith [hCompatible.product_lower])
    · apply (le_div_iff₀ hplus).mpr
      rw [← hproduct]
      simpa [low, mul_comm] using (mul_le_mul_of_nonneg_right hcase hlow.le)
    · field_simp
  · refine ⟨high, low, hhigh, hlow, le_of_not_ge hcase,
      hCompatible.minus_lower, horder, le_rfl, hproduct, le_rfl⟩

end
end UN.DAI
