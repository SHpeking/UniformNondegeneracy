module

public import UniformNondegeneracy.DAI.Admissibility

@[expose] public section

/-!
# Minimizing the DAI condition number

For `w = bounds.maxBandWidth`, the balanced scales `Λ₊ = μ₊ + w` and `Λ₋ = μ₋ + w` are admissible and minimize `kappa` over all admissible scales. The minimum is `(1 + w / μ₊) * (1 + w / μ₋)`.
-/

namespace UN.DAI
noncomputable section

/-- The condition number at the balanced scales. -/
theorem kappa_balancedScales (bounds : CurvatureBounds) :
    kappa bounds (balancedScales bounds) = (1 + bounds.maxBandWidth / bounds.muPlus) * (1 + bounds.maxBandWidth / bounds.muMinus) := by
  rw [(balancedScales_admissible bounds).kappa_eq_div]
  have hDenominator : kappaDenominator bounds (balancedScales bounds) = bounds.muPlus * bounds.muMinus := by
    simp only [kappaDenominator, balancedScales_difference]
    have hPlus : bounds.muPlus - (bounds.muPlus - bounds.muMinus) = bounds.muMinus := by ring
    have hMinus : bounds.muMinus + (bounds.muPlus - bounds.muMinus) = bounds.muPlus := by ring
    rw [hPlus, hMinus, mul_comm bounds.muMinus bounds.muPlus, min_self]
  rw [hDenominator]
  dsimp [balancedScales]
  field_simp [ne_of_gt bounds.muPlus_pos, ne_of_gt bounds.muMinus_pos]

namespace Admissible

variable {bounds : CurvatureBounds} {Λ : Scales}

/-- Every admissible scale pair has condition number at least the product determined by the maximum band width. -/
theorem kappa_lower_bound (hAdmissible : Admissible bounds Λ) :
    (1 + bounds.maxBandWidth / bounds.muPlus) * (1 + bounds.maxBandWidth / bounds.muMinus) ≤ kappa bounds Λ := by
  let a := effectiveMuPlus bounds Λ
  let b := effectiveMuMinus bounds Λ
  let v := Λ.plus - a
  have ha : 0 < a := hAdmissible.effectiveMuPlus_pos
  have hb : 0 < b := hAdmissible.effectiveMuMinus_pos
  have ha_le : a ≤ bounds.muPlus := effectiveMuPlus_le_muPlus bounds Λ
  have hb_le : b ≤ bounds.muMinus := effectiveMuMinus_le_muMinus bounds Λ
  have hv : v = Λ.minus - b := effective_widths_eq bounds Λ
  have hw : bounds.maxBandWidth ≤ v := by
    apply max_le
    · dsimp [v]
      linarith [hAdmissible.lPlus_le_plus]
    · linarith [hAdmissible.lMinus_le_minus]
  have hPlus : bounds.maxBandWidth / bounds.muPlus ≤ v / a := by
    calc
      _ ≤ bounds.maxBandWidth / a := div_le_div_of_nonneg_left bounds.maxBandWidth_nonneg ha ha_le
      _ ≤ v / a := (div_le_div_iff_of_pos_right ha).mpr hw
  have hMinus : bounds.maxBandWidth / bounds.muMinus ≤ v / b := by
    calc
      _ ≤ bounds.maxBandWidth / b := div_le_div_of_nonneg_left bounds.maxBandWidth_nonneg hb hb_le
      _ ≤ v / b := (div_le_div_iff_of_pos_right hb).mpr hw
  calc
    _ ≤ (1 + v / a) * (1 + v / b) := by
      apply mul_le_mul (add_le_add le_rfl hPlus) (add_le_add le_rfl hMinus)
      · exact add_nonneg zero_le_one (div_nonneg bounds.maxBandWidth_nonneg bounds.muMinus_pos.le)
      · exact add_nonneg zero_le_one (div_nonneg (bounds.maxBandWidth_nonneg.trans hw) ha.le)
    _ = kappa bounds Λ := by
      rw [hAdmissible.kappa_eq_div, ← hAdmissible.effectiveMuPlus_mul_effectiveMuMinus]
      change (1 + v / a) * (1 + v / b) = Λ.plus * Λ.minus / (a * b)
      have hPlus : a + v = Λ.plus := by dsimp [v]; ring
      have hMinus : b + v = Λ.minus := by linarith [hv]
      rw [← hPlus, ← hMinus]
      field_simp [ne_of_gt ha, ne_of_gt hb]

/-- Balanced scales globally minimize the condition number over admissible scales. -/
theorem kappa_balancedScales_le (hAdmissible : Admissible bounds Λ) :
    kappa bounds (balancedScales bounds) ≤ kappa bounds Λ := by
  rw [kappa_balancedScales]
  exact hAdmissible.kappa_lower_bound

end Admissible

end
end UN.DAI
