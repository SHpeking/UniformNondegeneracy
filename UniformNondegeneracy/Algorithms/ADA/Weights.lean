module

public import UniformNondegeneracy.DAI.Weights

@[expose] public section

/-!
# Weights for the ADA Lyapunov estimate

The selected weights are DAI-compatible and have product `q bounds Λ`.
-/

namespace UN.ADA

open DAI

noncomputable section

variable {bounds : CurvatureBounds} {Λ : Scales}

/-- Weights with product `q bounds Λ`, used in the ADA Lyapunov estimate. -/
def lyapunovWeights (hAdmissible : Admissible bounds Λ) : Weights where
  plus := q bounds Λ * Λ.tauMinus / Λ.tauPlus
  minus := Λ.tauPlus / Λ.tauMinus
  plus_nonneg := div_nonneg (mul_nonneg hAdmissible.toOuterCompatible.q_nonneg Λ.tauMinus_pos.le) Λ.tauPlus_pos.le
  minus_nonneg := div_nonneg Λ.tauPlus_pos.le Λ.tauMinus_pos.le

theorem lyapunovWeights_product (hAdmissible : Admissible bounds Λ) :
    (lyapunovWeights hAdmissible).plus * (lyapunovWeights hAdmissible).minus = q bounds Λ := by
  dsimp [lyapunovWeights]
  field_simp [ne_of_gt Λ.tauPlus_pos, ne_of_gt Λ.tauMinus_pos]

private theorem lyapunovWeights_plus_lower (hAdmissible : Admissible bounds Λ) :
    (Λ.radius - gapMargin bounds Λ) / Λ.minus ≤ (lyapunovWeights hAdmissible).plus := by
  have hdr : gapMargin bounds Λ ≤ Λ.radius := by
    have h := (effectiveMuPlus_le_muPlus bounds Λ).trans
      (bounds.muPlus_le_lPlus.trans hAdmissible.lPlus_le_plus)
    dsimp [effectiveMuPlus, Scales.radius, Scales.center, Scales.difference] at *
    linarith
  have hcd := hAdmissible.effectiveMuPlus_pos
  dsimp [effectiveMuPlus] at hcd
  have hidentity : (lyapunovWeights hAdmissible).plus =
      (Λ.radius ^ 2 - gapMargin bounds Λ ^ 2) / Λ.minus ^ 2 := by
    dsimp [lyapunovWeights, Scales.tauMinus, Scales.tauPlus]
    rw [hAdmissible.q_eq_radius_gapMargin]
    field_simp [ne_of_gt Λ.plus_pos, ne_of_gt Λ.minus_pos]
  rw [hidentity]
  apply (div_le_div_iff₀ Λ.minus_pos (sq_pos_of_pos Λ.minus_pos)).mpr
  have hprod := mul_nonneg (sub_nonneg.mpr hdr) hcd.le
  have hrc : Λ.radius - Λ.minus = Λ.center := by
    unfold Scales.radius Scales.center Scales.difference; ring
  nlinarith [mul_nonneg Λ.minus_pos.le hprod]

private theorem lyapunovWeights_minus_lower (hAdmissible : Admissible bounds Λ) :
    (Λ.radius - gapMargin bounds Λ) / Λ.plus ≤ (lyapunovWeights hAdmissible).minus := by
  have hid : (lyapunovWeights hAdmissible).minus = Λ.minus / Λ.plus := by
    dsimp [lyapunovWeights, Scales.tauMinus, Scales.tauPlus]
    field_simp
  rw [hid]
  apply (div_le_div_iff_of_pos_right Λ.plus_pos).mpr
  have h := (abs_lt.mp hAdmissible.abs_center_lt_gapMargin).2
  dsimp [Scales.center, Scales.difference, Scales.radius] at *
  linarith

theorem lyapunovWeights_compatible (hAdmissible : Admissible bounds Λ) :
    CompatibleWeights bounds Λ (lyapunovWeights hAdmissible) := by
  exact ⟨lyapunovWeights_plus_lower hAdmissible, lyapunovWeights_minus_lower hAdmissible, (lyapunovWeights_product hAdmissible).ge⟩

end
end UN.ADA
