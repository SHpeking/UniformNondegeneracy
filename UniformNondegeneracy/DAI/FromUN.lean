module

public import UniformNondegeneracy.DAI.Basic
public import UniformNondegeneracy.DAI.EnvelopeComparison

@[expose] public section

open scoped RealInnerProductSpace

/-!
# From UN to DAI, including boundary scales

The strict case is proved using centered envelopes. For general admissible scales, inflate both scales by the same positive amount, prove DAI there, and take the limit in the finite inequality for fixed points. This handles q = 0 without dividing by q or taking limits of entire ADA trajectories.
-/

open Filter
open scoped Topology

namespace UN

open DAI

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

namespace IsUN

variable {bounds : CurvatureBounds} {E : H → ℝ} {g : H → H} {Λ : Scales}

local notation "D" => bregman E g
local notation "Λ₊" => Λ.plus
local notation "Λ₋" => Λ.minus
local notation "τ₊" => Λ.tauPlus
local notation "τ₋" => Λ.tauMinus

private theorem plus_envelope_at_step (hUN : IsUN bounds E g)
    (hStrict : StrictAdmissible bounds Λ) (x₁ x₂ : H) :
    1 / 2 * ‖descentStep (fun x => g x - g x₁) Λ x₂ - x₁‖ ^ 2 +
      interiorEnvelope (UN.relativeEnergy E g x₁) (fun x => g x - g x₁) τ₊ (descentStep (fun x => g x - g x₁) Λ x₂) =
      phiPlus E g Λ x₁ x₂ := by
  have hs := hStrict.positive_parameter_mem
  have he := (hUN.relativeEnergy x₁).interiorEnvelope_at_step hs x₂
  change interiorEnvelope _ _ _ (x₂ - τ₊ • (g x₂ - g x₁)) = _ at he
  unfold descentStep gradientStep
  rw [he, hUN.stationaryValue_relativeEnergy]
  unfold phiPlus UN.relativeEnergy bregman
  rw [show x₂ - τ₊ • (g x₂ - g x₁) - x₁ = (x₂ - x₁) - τ₊ • (g x₂ - g x₁) by module]
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right, inner_sub_right, inner_sub_left]
  simp only [real_inner_comm x₂ x₁, real_inner_comm x₂ (g x₂), real_inner_comm x₂ (g x₁),
    real_inner_comm x₁ (g x₂), real_inner_comm x₁ (g x₁)]
  ring

private theorem minus_envelope_at_step (hUN : IsUN bounds E g)
    (hStrict : StrictAdmissible bounds Λ) (x₁ x₂ : H) :
    1 / 2 * ‖ascentStep (fun x => g x - g x₁) Λ x₂ - x₁‖ ^ 2 +
      interiorEnvelope (UN.relativeEnergy E g x₁) (fun x => g x - g x₁) (-τ₋) (ascentStep (fun x => g x - g x₁) Λ x₂) =
      phiMinus E g Λ x₁ x₂ := by
  have hs := hStrict.negative_parameter_mem
  have he := (hUN.relativeEnergy x₁).interiorEnvelope_at_step hs x₂
  change interiorEnvelope _ _ _ (x₂ - (-τ₋) • (g x₂ - g x₁)) = _ at he
  unfold ascentStep gradientStep
  rw [he, hUN.stationaryValue_relativeEnergy]
  unfold phiMinus UN.relativeEnergy bregman
  rw [show x₂ - (-τ₋) • (g x₂ - g x₁) - x₁ = (x₂ - x₁) - (-τ₋) • (g x₂ - g x₁) by module]
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right, inner_sub_right, inner_sub_left, neg_sq]
  simp only [real_inner_comm x₂ x₁, real_inner_comm x₂ (g x₂), real_inner_comm x₂ (g x₁),
    real_inner_comm x₁ (g x₂), real_inner_comm x₁ (g x₁)]
  ring

/-- Analytic core: strict outer scales place auxiliary envelopes in their domains. -/
theorem hasDAI_of_strict (hUN : IsUN bounds E g)
    (hStrict : StrictAdmissible bounds Λ) (ρ : Weights)
    (hWeights : CompatibleWeights bounds Λ ρ) :
    HasDAI E g Λ ρ := by
  have hprod : 0 < ρ.plus * ρ.minus := hStrict.q_pos.trans_le hWeights.product_lower
  have hp : 0 < ρ.plus := by nlinarith [ρ.plus_nonneg, ρ.minus_nonneg]
  intro x y z
  have h := (hUN.relativeEnergy x).envelope_pair_comparison_strict hStrict ρ hp
    hWeights.plus_lower hWeights.minus_lower hWeights.product_lower
    (descentStep (fun x' => g x' - g x) Λ y)
    (ascentStep (fun x' => g x' - g x) Λ z)
  rw [hUN.stationaryPoint_relativeEnergy,
    hUN.plus_envelope_at_step hStrict, hUN.minus_envelope_at_step hStrict] at h
  convert h using 1
  unfold descentStep ascentStep gradientStep
  rw [show y - τ₊ • (g y - g x) - x = -(x - τ₊ • g x - (y - τ₊ • g y)) by module]
  rw [show z - (-τ₋) • (g z - g x) - x = -(x - (-τ₋) • g x - (z - (-τ₋) • g z)) by module]
  rw [inner_neg_neg]

/-- Inflate the scales by `ε > 0` and add `sqrt (2 * Λ.radius * ε + ε ^ 2)` to the scaled weight numerators. This preserves compatibility and converges to the original weights, including when `q = 0` or a weight vanishes. The limit is taken only in the finite inequality for three fixed points. -/
private theorem hasDAI_by_inflation (hUN : IsUN bounds E g)
    (hAdmissible : Admissible bounds Λ) (ρ : Weights)
    (hWeights : CompatibleWeights bounds Λ ρ) :
    HasDAI E g Λ ρ := by
  let η : ℝ → ℝ := fun ε => Real.sqrt (2 * Λ.radius * ε + ε ^ 2)
  let ρPlus : ℝ → ℝ := fun ε => (Λ₋ * ρ.plus + η ε) / (Λ₋ + ε)
  let ρMinus : ℝ → ℝ := fun ε => (Λ₊ * ρ.minus + η ε) / (Λ₊ + ε)
  have hdist := hAdmissible.gapMargin_pos
  have hη_pos (ε : ℝ) (hε_pos : 0 < ε) : 0 < η ε := by
    apply Real.sqrt_pos.mpr
    positivity [Λ.radius_pos]
  have hε_le_η (ε : ℝ) (hε_pos : 0 < ε) : ε ≤ η ε := by
    apply (Real.le_sqrt hε_pos.le (by positivity [Λ.radius_pos])).mpr
    nlinarith [Λ.radius_pos]
  have hρPlus_pos (ε : ℝ) (hε_pos : 0 < ε) : 0 < ρPlus ε := by
    exact div_pos (add_pos_of_nonneg_of_pos
      (mul_nonneg Λ.minus_pos.le ρ.plus_nonneg) (hη_pos ε hε_pos))
      (add_pos Λ.minus_pos hε_pos)
  have hρMinus_pos (ε : ℝ) (hε_pos : 0 < ε) : 0 < ρMinus ε := by
    exact div_pos (add_pos_of_nonneg_of_pos
      (mul_nonneg Λ.plus_pos.le ρ.minus_nonneg) (hη_pos ε hε_pos))
      (add_pos Λ.plus_pos hε_pos)
  have hcompat (ε : ℝ) (hε_pos : 0 < ε) :
      CompatibleWeights bounds (Λ.inflate ε hε_pos.le)
        ⟨ρPlus ε, ρMinus ε, (hρPlus_pos ε hε_pos).le, (hρMinus_pos ε hε_pos).le⟩ := by
    have hi := hAdmissible.inflate ε hε_pos.le
    have hp : 0 < Λ₊ + ε := add_pos Λ.plus_pos hε_pos
    have hm : 0 < Λ₋ + ε := add_pos Λ.minus_pos hε_pos
    have hr : (Λ.inflate ε hε_pos.le).radius = Λ.radius + ε := by
      dsimp [Scales.inflate, Scales.radius]
      ring
    constructor
    · rw [gapMargin_inflate bounds Λ, hr]
      change (Λ.radius + ε - gapMargin bounds Λ) / (Λ₋ + ε) ≤ ρPlus ε
      apply (div_le_div_iff_of_pos_right hm).mpr
      have hl := (div_le_iff₀ Λ.minus_pos).mp hWeights.plus_lower
      linarith [hε_le_η ε hε_pos]
    · rw [gapMargin_inflate bounds Λ, hr]
      change (Λ.radius + ε - gapMargin bounds Λ) / (Λ₊ + ε) ≤ ρMinus ε
      apply (div_le_div_iff_of_pos_right hp).mpr
      have hl := (div_le_iff₀ Λ.plus_pos).mp hWeights.minus_lower
      linarith [hε_le_η ε hε_pos]
    · rw [hi.q_eq_radius_gapMargin, gapMargin_inflate bounds Λ, hr]
      change ((Λ.radius + ε) ^ 2 - gapMargin bounds Λ ^ 2) / ((Λ₊ + ε) * (Λ₋ + ε)) ≤ ρPlus ε * ρMinus ε
      rw [show ρPlus ε * ρMinus ε =
          ((Λ₋ * ρ.plus + η ε) * (Λ₊ * ρ.minus + η ε)) / ((Λ₊ + ε) * (Λ₋ + ε)) by
        dsimp [ρPlus, ρMinus]; field_simp [hp.ne', hm.ne']]
      apply (div_le_div_iff_of_pos_right (mul_pos hp hm)).mpr
      have hprod := hWeights.product_lower
      rw [hAdmissible.q_eq_radius_gapMargin] at hprod
      have hp' := (div_le_iff₀ (mul_pos Λ.plus_pos Λ.minus_pos)).mp hprod
      have hs : (η ε) ^ 2 = 2 * Λ.radius * ε + ε ^ 2 := Real.sq_sqrt (by positivity [Λ.radius_pos])
      have hcrossp := mul_nonneg (mul_nonneg Λ.minus_pos.le ρ.plus_nonneg) (hη_pos ε hε_pos).le
      have hcrossm := mul_nonneg (mul_nonneg Λ.plus_pos.le ρ.minus_nonneg) (hη_pos ε hε_pos).le
      nlinarith only [hp', hs, hcrossp, hcrossm]
  intro x y z
  let lhs : ℝ → ℝ := fun ε =>
    ⟪(x - (1 / (Λ₊ + ε)) • g x) - (y - (1 / (Λ₊ + ε)) • g y),
      (x - (-(1 / (Λ₋ + ε))) • g x) - (z - (-(1 / (Λ₋ + ε))) • g z)⟫
  let rhs : ℝ → ℝ := fun ε =>
    ρPlus ε * (‖x - y‖ ^ 2 / 2 - (1 / (Λ₊ + ε)) * D x y) +
    ρMinus ε * (‖x - z‖ ^ 2 / 2 + (1 / (Λ₋ + ε)) * D x z)
  have hle (ε : ℝ) (hε_pos : ε ∈ Set.Ioi (0 : ℝ)) : lhs ε ≤ rhs ε := by
    have hh := hUN.hasDAI_of_strict (hAdmissible.strict_inflate ε hε_pos)
      ⟨ρPlus ε, ρMinus ε, (hρPlus_pos ε hε_pos).le, (hρMinus_pos ε hε_pos).le⟩ (hcompat ε hε_pos)
    exact hh x y z
  have hLhs : ContinuousAt lhs 0 := by
    dsimp [lhs]
    fun_prop (disch := norm_num [Λ.plus_pos.ne', Λ.minus_pos.ne'])
  have hRhs : ContinuousAt rhs 0 := by
    dsimp [rhs, ρPlus, ρMinus, η]
    fun_prop (disch := norm_num [Λ.plus_pos.ne', Λ.minus_pos.ne'])
  have hmem : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by simp [closure_Ioi]
  have hlim := ContinuousWithinAt.closure_le hmem hLhs.continuousWithinAt hRhs.continuousWithinAt hle
  simpa [lhs, rhs, ρPlus, ρMinus, η,
    descentStep, ascentStep, gradientStep, phiPlus, phiMinus,
    Scales.tauPlus, Scales.tauMinus, Λ.plus_pos.ne', Λ.minus_pos.ne'] using hlim

/-- Canonical-weight DAI, obtained by equal scale inflations and continuity; valid even when `q = 0`. -/
theorem hasDAI_canonicalWeights (hUN : IsUN bounds E g)
    (hAdmissible : Admissible bounds Λ) :
    HasDAI E g Λ hAdmissible.canonicalWeights := by
  exact hUN.hasDAI_by_inflation hAdmissible hAdmissible.canonicalWeights
    hAdmissible.canonicalWeights_compatible

/-- The full DAI weight family, including boundary scales and zero weights. -/
theorem hasDAI (hUN : IsUN bounds E g)
    (hAdmissible : Admissible bounds Λ) (ρ : Weights)
    (hWeights : CompatibleWeights bounds Λ ρ) :
    HasDAI E g Λ ρ := by
  exact hUN.hasDAI_by_inflation hAdmissible ρ hWeights

end IsUN
end UN
