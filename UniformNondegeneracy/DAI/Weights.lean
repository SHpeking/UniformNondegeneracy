module

public import UniformNondegeneracy.DAI.Admissibility
public import Mathlib.Analysis.Real.Sqrt

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

/-- Weight conditions for the DAI family on the admissible scale region. -/
structure CompatibleWeights (bounds : CurvatureBounds) (Λ : Scales) (ρ : Weights) : Prop where
  plus_lower : (Λ.radius - gapMargin bounds Λ) / Λ.minus ≤ ρ.plus
  minus_lower : (Λ.radius - gapMargin bounds Λ) / Λ.plus ≤ ρ.minus

  product_lower : q bounds Λ ≤ ρ.plus * ρ.minus

/-- Compatible weights are positive at strict admissible scales. -/
theorem CompatibleWeights.pos {bounds : CurvatureBounds} {Λ : Scales} {ρ : Weights}
    (hCompatible : CompatibleWeights bounds Λ ρ) (hStrict : StrictAdmissible bounds Λ) :
    0 < ρ.plus ∧ 0 < ρ.minus := by
  have hProduct : 0 < ρ.plus * ρ.minus := hStrict.q_pos.trans_le hCompatible.product_lower
  constructor <;> nlinarith [ρ.plus_nonneg, ρ.minus_nonneg]

/-- Reduce compatible positive weights to the boundary where their product is exactly `q`. -/
theorem CompatibleWeights.exists_product_eq
    {bounds : CurvatureBounds} {Λ : Scales} {ρ : Weights}
    (hCompatible : CompatibleWeights bounds Λ ρ) (hStrict : StrictAdmissible bounds Λ) :
    ∃ ρ' : Weights, CompatibleWeights bounds Λ ρ' ∧
      ρ'.plus ≤ ρ.plus ∧ ρ'.minus ≤ ρ.minus ∧ ρ'.plus * ρ'.minus = q bounds Λ := by
  have hplus := (hCompatible.pos hStrict).1
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
  · let ρ' : Weights := ⟨ρ.plus, q bounds Λ / ρ.plus, hplus.le, (div_pos hStrict.q_pos hplus).le⟩
    have hProduct : ρ'.plus * ρ'.minus = q bounds Λ := by dsimp [ρ']; field_simp
    refine ⟨ρ', ⟨hCompatible.plus_lower, ?_, hProduct.ge⟩, le_rfl, ?_, hProduct⟩
    · change low ≤ q bounds Λ / ρ.plus
      apply (le_div_iff₀ hplus).mpr
      rw [← hproduct]
      simpa [mul_comm] using (mul_le_mul_of_nonneg_right hcase hlow.le)
    · exact (div_le_iff₀ hplus).mpr (by nlinarith [hCompatible.product_lower])
  · let ρ' : Weights := ⟨high, low, hhigh.le, hlow.le⟩
    exact ⟨ρ', ⟨horder, le_rfl, hproduct.ge⟩, le_of_not_ge hcase, hCompatible.minus_lower, hproduct⟩

end
end UN.DAI
