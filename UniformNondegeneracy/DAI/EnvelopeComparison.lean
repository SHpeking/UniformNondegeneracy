module

public import UniformNondegeneracy.Envelopes.Comparison
public import UniformNondegeneracy.DAI.Reparameterization
public import UniformNondegeneracy.DAI.Weights

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Envelope comparison at DAI scales

A weighted sum of envelope values at positive and negative parameters, together with quadratic terms, bounds the inner product of two anchors centered at the stationary point. This comparison yields the descent–ascent inequality.
-/

noncomputable section
namespace UN

open DAI
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {bounds : CurvatureBounds} {E : H → ℝ} {g : H → H}

local notation "M" => interiorEnvelope E g

theorem DAI.StrictAdmissible.centered_envelope_parameter_mem {Λ : Scales}
    (hStrict : StrictAdmissible bounds Λ) :
    -1 / Λ.radius ∈ envelopeDomain hStrict.toAdmissible.centeredBounds := by
  change -1 / centeredOuterRadius bounds Λ < -1 / Λ.radius ∧
    -1 / Λ.radius < 1 / centeredOuterRadius bounds Λ
  constructor
  · exact (div_lt_div_iff₀ hStrict.toAdmissible.centeredOuterRadius_pos Λ.radius_pos).mpr
      (by nlinarith [hStrict.centeredOuterRadius_lt_radius])
  · exact (div_neg_of_neg_of_pos (by norm_num) Λ.radius_pos).trans
      (div_pos zero_lt_one hStrict.toAdmissible.centeredOuterRadius_pos)

theorem DAI.StrictAdmissible.positive_parameter_mem {Λ : Scales}
    (hStrict : StrictAdmissible bounds Λ) :
    Λ.tauPlus ∈ envelopeDomain bounds := by
  constructor
  · exact (div_neg_of_neg_of_pos (by norm_num) bounds.lMinus_pos).trans Λ.tauPlus_pos
  · exact one_div_lt_one_div_of_lt bounds.lPlus_pos hStrict.lPlus_lt_plus

theorem DAI.StrictAdmissible.negative_parameter_mem {Λ : Scales}
    (hStrict : StrictAdmissible bounds Λ) :
    -Λ.tauMinus ∈ envelopeDomain bounds := by
  constructor
  · simpa [Scales.tauMinus, neg_div] using
      neg_lt_neg (one_div_lt_one_div_of_lt bounds.lMinus_pos hStrict.lMinus_lt_minus)
  · exact (neg_neg_of_pos Λ.tauMinus_pos).trans (div_pos zero_lt_one bounds.lPlus_pos)

namespace IsUN

set_option maxHeartbeats 1000000

private theorem envelope_pair_equality (hUN : IsUN bounds E g) {Λ : Scales}
    (hStrict : StrictAdmissible bounds Λ)
    (ρPlus ρMinus : ℝ) (hρPlus_pos : 0 < ρPlus)
    (hal : (Λ.radius - gapMargin bounds Λ) / Λ.minus ≤ ρPlus)
    (hau : ρPlus ≤ (Λ.radius + gapMargin bounds Λ) / Λ.minus)
    (hab : ρPlus * ρMinus = q bounds Λ) (x₁ x₂ : H) :
    ⟪x₁ - stationaryPoint g, x₂ - stationaryPoint g⟫ ≤
      ρPlus * (‖x₁ - stationaryPoint g‖ ^ 2 / 2 + M Λ.tauPlus x₁) +
      ρMinus * (‖x₂ - stationaryPoint g‖ ^ 2 / 2 + M (-Λ.tauMinus) x₂) := by
  let R := Λ.radius
  let c := Λ.center
  let δΛ := gapMargin bounds Λ
  let ΛPlus := Λ.plus
  let ΛMinus := Λ.minus
  let xStar := stationaryPoint g
  let Eshift := UN.quadraticShift E c xStar
  let gshift := fun z => g z - c • (z - xStar)
  let θ := ΛMinus * ρPlus - R
  let x := xStar + (ΛMinus / R) • (x₂ - xStar)
  let ξ := xStar + ρPlus⁻¹ • (x₂ - xStar)
  have hΛPlus_pos : 0 < ΛPlus := Λ.plus_pos
  have hΛMinus_pos : 0 < ΛMinus := Λ.minus_pos
  have hR : 0 < R := Λ.radius_pos
  have hRc : R - c = ΛMinus := by dsimp [R, c, ΛMinus, Scales.radius, Scales.center, Scales.difference]; ring
  have hpc : R + c = ΛPlus := by dsimp [R, c, ΛPlus, Scales.radius, Scales.center, Scales.difference]; ring
  have hc := hStrict.toAdmissible.center_mem_gap
  have hcen := hUN.centered hStrict.toAdmissible
  change IsUN hStrict.toAdmissible.centeredBounds Eshift gshift at hcen
  have hs := hStrict.negative_parameter_mem
  have hcenter := hStrict.centered_envelope_parameter_mem
  have hstar : stationaryPoint gshift = xStar := by
    apply Eq.symm
    apply (hcen.gradient_eq_zero_iff xStar).mp
    dsimp [gshift, xStar]
    simp [hUN.gradient_stationaryPoint]
  have hvalue : stationaryValue Eshift gshift = stationaryValue E g := by
    simp [stationaryValue, hstar, Eshift, UN.quadraticShift, xStar]
  have hθ : θ ∈ Set.Icc (-δΛ) δΛ := by
    have hl := (div_le_iff₀ hΛMinus_pos).mp hal
    have hu := (le_div_iff₀ hΛMinus_pos).mp hau
    constructor <;> dsimp [θ] <;> linarith
  have hcov := hUN.interiorEnvelope_quadraticShift hs hc.1 hc.2 x₂
  have hparameter : shiftedEnvelopeParameter (-Λ.tauMinus) c = -1 / R := by
    dsimp [shiftedEnvelopeParameter, Scales.tauMinus]
    change -(1 / ΛMinus) / (1 - -(1 / ΛMinus) * c) = -1 / R
    rw [show R = ΛMinus + c by linarith [hRc]]
    field_simp; ring
  have hpoint : rescaledEnvelopePoint g (-Λ.tauMinus) c x₂ = x := by
    dsimp [rescaledEnvelopePoint, x, xStar, Scales.tauMinus]
    congr 1
    congr 1
    change (1 - -(1 / ΛMinus) * c)⁻¹ = ΛMinus / R
    rw [show R = ΛMinus + c by linarith [hRc]]
    field_simp; ring
  change interiorEnvelope Eshift gshift (shiftedEnvelopeParameter (-Λ.tauMinus) c)
    (rescaledEnvelopePoint g (-Λ.tauMinus) c x₂) = _ at hcov
  rw [hparameter, hpoint] at hcov
  have hcov' : interiorEnvelope Eshift gshift (-1 / R) x =
      ΛMinus / R * M (-Λ.tauMinus) x₂ + c * ΛMinus / (2 * R ^ 2) * ‖x₂ - xStar‖ ^ 2 := by
    rw [hcov]
    change M (-(1 / ΛMinus)) x₂ / (1 - -(1 / ΛMinus) * c) -
      (-(1 / ΛMinus)) * c / (2 * (1 - -(1 / ΛMinus) * c) ^ 2) * ‖x₂ - xStar‖ ^ 2 =
      ΛMinus / R * M (-(1 / ΛMinus)) x₂ + c * ΛMinus / (2 * R ^ 2) * ‖x₂ - xStar‖ ^ 2
    have hden : 1 - -(1 / ΛMinus) * c = R / ΛMinus := by field_simp [hΛMinus_pos.ne']; linarith [hRc]
    rw [hden]
    field_simp [hΛMinus_pos.ne', hR.ne']; ring
  have hrescale : rescaledEnvelopePoint gshift (-1 / R) θ x = ξ := by
    dsimp [rescaledEnvelopePoint]
    rw [hstar]
    dsimp [x, ξ]
    simp only [add_sub_cancel_left, smul_smul]
    congr 1
    congr 1
    dsimp [θ]
    field_simp; ring
  have hcomp := hcen.envelope_rescaled_comparison hcenter hθ x
  rw [hstar, hvalue, hrescale, hcov'] at hcomp
  have hnormx : ‖x - xStar‖ ^ 2 = (ΛMinus / R) ^ 2 * ‖x₂ - xStar‖ ^ 2 := by
    simp [x, norm_smul, mul_pow, abs_of_pos hΛMinus_pos, abs_of_pos hR]
  have hnormξ : ‖ξ - xStar‖ ^ 2 = ρPlus⁻¹ ^ 2 * ‖x₂ - xStar‖ ^ 2 := by
    simp [ξ, norm_smul, mul_pow]
  change (-1 / R) * (1 - (-1 / R) * θ) ^ 2 * (Eshift ξ - stationaryValue E g) +
    (-1 / R) ^ 2 * δΛ * δΛ / 2 * ‖x - xStar‖ ^ 2 ≤
    (1 - (-1 / R) * δΛ) * (1 + (-1 / R) * δΛ) * _ at hcomp
  dsimp [Eshift, UN.quadraticShift] at hcomp
  rw [hnormx, hnormξ] at hcomp
  have hbform : ρMinus = (R ^ 2 - δΛ ^ 2) / (ΛPlus * ΛMinus * ρPlus) := by
    have hh := hStrict.toAdmissible.q_eq_radius_gapMargin
    change q bounds Λ = (R ^ 2 - δΛ ^ 2) / (ΛPlus * ΛMinus) at hh
    rw [← hab] at hh
    apply (eq_div_iff (by positivity : ΛPlus * ΛMinus * ρPlus ≠ 0)).mpr
    have hh' := (eq_div_iff (by positivity : ΛPlus * ΛMinus ≠ 0)).mp hh
    nlinarith [hh']
  have hnegative : ρPlus * (‖ξ - xStar‖ ^ 2 / 2 - (E ξ - stationaryValue E g) / ΛPlus) ≤
      ρMinus * (‖x₂ - xStar‖ ^ 2 / 2 + M (-Λ.tauMinus) x₂) := by
    rw [hnormξ, hbform]
    apply sub_nonneg.mp
    convert mul_nonneg (show 0 ≤ R ^ 3 / (ΛPlus * ΛMinus ^ 2 * ρPlus) by positivity) (sub_nonneg.mpr hcomp) using 1
    dsimp [θ]
    field_simp [hΛPlus_pos.ne', hΛMinus_pos.ne', hR.ne', hρPlus_pos.ne']
    rw [show ΛPlus = R + c by linarith [hpc], show ΛMinus = R - c by linarith [hRc]]
    ring
  have hpositive := hUN.envelopeObjective_le_interiorEnvelope (hStrict.positive_parameter_mem) x₁ ξ
  have hn : ‖ξ - x₁‖ ^ 2 =
      ‖ξ - xStar‖ ^ 2 + ‖x₁ - xStar‖ ^ 2 - 2 * ρPlus⁻¹ * ⟪x₁ - xStar, x₂ - xStar⟫ := by
    rw [show ξ - x₁ = (ξ - xStar) - (x₁ - xStar) by module, norm_sub_sq_real]
    dsimp [ξ]
    simp only [add_sub_cancel_left, real_inner_smul_left]
    rw [real_inner_comm]
    ring
  dsimp [envelopeObjective] at hpositive
  rw [hn] at hpositive
  have hmul := mul_le_mul_of_nonneg_left hpositive hρPlus_pos.le
  have hai : ρPlus * ρPlus⁻¹ = 1 := mul_inv_cancel₀ hρPlus_pos.ne'
  dsimp [Scales.tauPlus] at hmul
  change _ ≤ ρPlus * M (1 / ΛPlus) x₁ at hmul
  change _ ≤ ρPlus * (_ + M (1 / ΛPlus) x₁) + _
  have hi :
      ρPlus * (1 / ΛPlus * (E ξ - stationaryValue E g) -
        1 / 2 * (‖ξ - xStar‖ ^ 2 + ‖x₁ - xStar‖ ^ 2 - 2 * ρPlus⁻¹ * ⟪x₁ - xStar, x₂ - xStar⟫)) =
      ⟪x₁ - xStar, x₂ - xStar⟫ - ρPlus * ‖x₁ - xStar‖ ^ 2 / 2 -
        ρPlus * (‖ξ - xStar‖ ^ 2 / 2 - (E ξ - stationaryValue E g) / ΛPlus) := by
    field_simp [hρPlus_pos.ne', hΛPlus_pos.ne']
    ring
  change ρPlus * (1 / ΛPlus * (E ξ - stationaryValue E g) -
    1 / 2 * (‖ξ - xStar‖ ^ 2 + ‖x₁ - xStar‖ ^ 2 - 2 * ρPlus⁻¹ * ⟪x₁ - xStar, x₂ - xStar⟫)) ≤ _ at hmul
  rw [hi] at hmul
  change ⟪x₁ - xStar, x₂ - xStar⟫ ≤ _
  linarith only [hmul, hnegative]

/-- The weighted envelope values and quadratic terms bound the inner product of their centered anchors. -/
theorem envelope_pair_comparison_strict (hUN : IsUN bounds E g)
    {Λ : Scales} (hStrict : StrictAdmissible bounds Λ)
    (ρ : Weights)
    (hρPlus_pos : 0 < ρ.plus)
    (hρPlus_lower : (Λ.radius - gapMargin bounds Λ) / Λ.minus ≤ ρ.plus)
    (hρMinus_lower : (Λ.radius - gapMargin bounds Λ) / Λ.plus ≤ ρ.minus)
    (hProduct : q bounds Λ ≤ ρ.plus * ρ.minus)
    (x₁ x₂ : H) :
    ⟪x₁ - stationaryPoint g, x₂ - stationaryPoint g⟫ ≤
      ρ.plus * ((1 / 2 : ℝ) * ‖x₁ - stationaryPoint g‖ ^ 2 + M Λ.tauPlus x₁) +
      ρ.minus * ((1 / 2 : ℝ) * ‖x₂ - stationaryPoint g‖ ^ 2 + M (-Λ.tauMinus) x₂) := by
  have hc : CompatibleWeights bounds Λ ρ := ⟨hρPlus_lower, hρMinus_lower, hProduct⟩
  obtain ⟨ρPlus, ρMinus, hρPlus_pos, hρMinus_pos, hap, hbm, hal, hbl, hab, hau⟩ := hc.exists_product_eq hStrict hρPlus_pos
  have hΛPlus_pos := hUN.interiorEnvelope_lower (hStrict.positive_parameter_mem) x₁
  have hΛMinus_pos := hUN.interiorEnvelope_lower (hStrict.negative_parameter_mem) x₂
  have h := hUN.envelope_pair_equality hStrict ρPlus ρMinus hρPlus_pos hal hau hab x₁ x₂
  have hp' := mul_le_mul_of_nonneg_right hap
    (by linarith : 0 ≤ ‖x₁ - stationaryPoint g‖ ^ 2 / 2 + M Λ.tauPlus x₁)
  have hm' := mul_le_mul_of_nonneg_right hbm
    (by linarith : 0 ≤ ‖x₂ - stationaryPoint g‖ ^ 2 / 2 + M (-Λ.tauMinus) x₂)
  linarith only [h, hp', hm']

end IsUN
end UN
