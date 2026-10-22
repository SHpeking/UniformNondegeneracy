module

public import UniformNondegeneracy.DAI.Admissibility

@[expose] public section

/-!
# ADA condition number and optimal scales

For `w = bounds.maxBandWidth`, the balanced scales `Λ₊ = μ₊ + w` and `Λ₋ = μ₋ + w` are admissible and minimize `kappa` over all admissible scales. The minimum is `(1 + w / μ₊) * (1 + w / μ₋)`.
-/

namespace UN.ADA

open DAI

noncomputable section

/-- Effective condition number in the ADA convergence bound. -/
def kappa (bounds : CurvatureBounds) (Λ : Scales) : ℝ := 1 / (1 - q bounds Λ)

variable {bounds : CurvatureBounds} {Λ : Scales}

theorem one_sub_q_eq_inv_kappa (bounds : CurvatureBounds) (Λ : Scales) :
    1 - q bounds Λ = 1 / kappa bounds Λ := by simp [kappa]

theorem kappa_pos (hAdmissible : Admissible bounds Λ) : 0 < kappa bounds Λ := by
  exact one_div_pos.mpr (sub_pos.mpr hAdmissible.q_lt_one)

theorem one_le_kappa (hAdmissible : Admissible bounds Λ) : 1 ≤ kappa bounds Λ := by
  exact (le_div_iff₀ (sub_pos.mpr hAdmissible.q_lt_one)).mpr (by
    simpa using sub_le_self (1 : ℝ) hAdmissible.toOuterCompatible.q_nonneg)

theorem kappa_eq_div (hAdmissible : Admissible bounds Λ) :
    kappa bounds Λ = Λ.plus * Λ.minus / (effectiveMuPlus bounds Λ * effectiveMuMinus bounds Λ) := by
  unfold kappa
  rw [hAdmissible.q_eq_one_sub_div, ← hAdmissible.effectiveMuPlus_mul_effectiveMuMinus]
  simp

theorem kappa_sub_one (hAdmissible : Admissible bounds Λ) :
    kappa bounds Λ - 1 = kappa bounds Λ * q bounds Λ := by
  unfold kappa
  field_simp [ne_of_gt (sub_pos.mpr hAdmissible.q_lt_one)]; ring

theorem kappa_mul_steps_mul_effective_inner (hAdmissible : Admissible bounds Λ) :
    kappa bounds Λ * Λ.tauPlus * Λ.tauMinus * effectiveMuPlus bounds Λ * effectiveMuMinus bounds Λ = 1 := by
  rw [kappa_eq_div hAdmissible]
  unfold Scales.tauPlus Scales.tauMinus
  field_simp [ne_of_gt Λ.plus_pos, ne_of_gt Λ.minus_pos, ne_of_gt hAdmissible.effectiveMuPlus_pos, ne_of_gt hAdmissible.effectiveMuMinus_pos]

theorem kappa_swap (hAdmissible : Admissible bounds Λ) :
    kappa bounds.swap Λ.swap = kappa bounds Λ := by
  simp only [kappa, hAdmissible.q_swap]

theorem kappa_inflate (hAdmissible : Admissible bounds Λ) (ε : ℝ) (hε : 0 ≤ ε) :
    kappa bounds (Λ.inflate ε hε) =
      (Λ.plus + ε) * (Λ.minus + ε) / (effectiveMuPlus bounds Λ * effectiveMuMinus bounds Λ) := by
  rw [kappa_eq_div (hAdmissible.inflate ε hε)]
  simp only [effectiveMuPlus, effectiveMuMinus, gapMargin_inflate, Scales.inflate_center]
  rfl

/-- The condition number at the balanced scales. -/
theorem kappa_balancedScales (bounds : CurvatureBounds) :
    kappa bounds (balancedScales bounds) =
      (1 + bounds.maxBandWidth / bounds.muPlus) * (1 + bounds.maxBandWidth / bounds.muMinus) := by
  rw [kappa_eq_div (balancedScales_admissible bounds), effectiveMuPlus_balancedScales, effectiveMuMinus_balancedScales]
  dsimp [balancedScales]
  field_simp [ne_of_gt bounds.muPlus_pos, ne_of_gt bounds.muMinus_pos]

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
      rw [kappa_eq_div hAdmissible]
      change (1 + v / a) * (1 + v / b) = Λ.plus * Λ.minus / (a * b)
      have hPlus : a + v = Λ.plus := by dsimp [v]; ring
      have hMinus : b + v = Λ.minus := by linarith [hv]
      rw [← hPlus, ← hMinus]
      field_simp [ne_of_gt ha, ne_of_gt hb]

/-- Balanced scales globally minimize the condition number over admissible scales. -/
theorem balancedScales_optimal (hAdmissible : Admissible bounds Λ) :
    kappa bounds (balancedScales bounds) ≤ kappa bounds Λ := by
  rw [kappa_balancedScales]
  exact kappa_lower_bound hAdmissible

end
end UN.ADA
