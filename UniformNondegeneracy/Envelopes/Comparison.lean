module

public import UniformNondegeneracy.Envelopes.Basic
public import UniformNondegeneracy.Geometry.Transforms
public import UniformNondegeneracy.Geometry.Duality
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Envelope comparisons

Quadratic comparison inequalities and covariance under quadratic shifts.
-/

noncomputable section

open Filter
open scoped Topology

namespace UN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Rescaling about the stationary point by `(1 - s * c)⁻¹`. -/
def rescaledEnvelopePoint (E : H → ℝ) (s c : ℝ) (x : H) : H :=
  stationaryPoint E + (1 - s * c)⁻¹ • (x - stationaryPoint E)

/-- Parameter transformation associated with subtracting a quadratic. -/
def shiftedEnvelopeParameter (s c : ℝ) : ℝ :=
  s / (1 - s * c)

variable {bounds : CurvatureBounds} {E : H → ℝ}

local notation "g" => gradient E

local notation "μ₊" => bounds.muPlus
local notation "μ₋" => bounds.muMinus
local notation "L₋" => bounds.lMinus
local notation "D" => bregman E
local notation "xStar" => stationaryPoint E
local notation "EStar" => stationaryValue E
local notation "J" => resolvent g
local notation "M" => envelope E

namespace Envelopes

theorem rescaling_denominator_pos
    {s c : ℝ} (hs : s ∈ envelopeDomain bounds)
    (hc_mem : c ∈ Set.Icc (-μ₋) μ₊) :
    0 < 1 - s * c := by
  have hp := (lt_div_iff₀ bounds.lPlus_pos).mp hs.2
  have hm := (div_lt_iff₀ bounds.lMinus_pos).mp hs.1
  rcases le_total 0 s with hs₁ | hs₁
  · have hc := mul_le_mul_of_nonneg_left
      (hc_mem.2.trans bounds.muPlus_le_lPlus) hs₁
    linarith
  · have hc := mul_le_mul_of_nonpos_left
      ((neg_le_neg bounds.muMinus_le_lMinus).trans hc_mem.1) hs₁
    nlinarith

theorem shiftedEnvelopeParameter_mem
    {s c : ℝ} (hs : s ∈ envelopeDomain bounds)
    (hLower : -μ₋ < c) (hUpper : c < μ₊) :
    shiftedEnvelopeParameter s c ∈ envelopeDomain (bounds.shift c hLower hUpper) := by
  have hd := rescaling_denominator_pos hs ⟨hLower.le, hUpper.le⟩
  have hp := (lt_div_iff₀ bounds.lPlus_pos).mp hs.2
  have hm := (div_lt_iff₀ bounds.lMinus_pos).mp hs.1
  have hsp := (bounds.shift c hLower hUpper).lPlus_pos
  have hsm := (bounds.shift c hLower hUpper).lMinus_pos
  change 0 < bounds.lPlus - c at hsp
  change 0 < L₋ + c at hsm
  change -1 / (L₋ + c) < s / (1 - s * c) ∧
    s / (1 - s * c) < 1 / (bounds.lPlus - c)
  constructor
  · apply (div_lt_div_iff₀ hsm hd).mpr
    nlinarith
  · apply (div_lt_div_iff₀ hd hsp).mpr
    nlinarith

end Envelopes

namespace IsUN

/-- Parameter derivative of `M s x / s`. -/
theorem hasDerivAt_envelope_quotient (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (hs_ne : s ≠ 0) (x : H) :
    HasDerivAt (fun s₁ => M s₁ x / s₁) ((1 / 2 : ℝ) * ‖g (J s x)‖ ^ 2) s := by
  have hvalue : M s x = s * (E (J s x) - EStar) - s ^ 2 / 2 * ‖g (J s x)‖ ^ 2 := by
    simpa only [hUN.resolvent_equation hs] using
      hUN.envelope_at_step hs (J s x)
  convert (hUN.hasDerivAt_envelope hs x).div (hasDerivAt_id s) hs_ne using 1
  · rfl
  · dsimp
    rw [hvalue]
    field_simp; ring

private theorem hasDerivAt_weighted_quotient (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (hs0 : s ≠ 0) (x : H) :
    HasDerivAt (fun s₁ => (1 - s₁ * μ₊) * (1 + s₁ * μ₋) * M s₁ x / s₁)
      ((μ₋ - μ₊ - 2 * s * μ₊ * μ₋) * (M s x / s) +
        (1 - s * μ₊) * (1 + s * μ₋) * ((1 / 2 : ℝ) * ‖g (J s x)‖ ^ 2)) s := by
  have hweight : HasDerivAt (fun s₁ => (1 - s₁ * μ₊) * (1 + s₁ * μ₋))
      (μ₋ - μ₊ - 2 * s * μ₊ * μ₋) s := by
    convert ((hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_id s).mul_const μ₊)).mul
      ((hasDerivAt_const s (1 : ℝ)).add ((hasDerivAt_id s).mul_const μ₋)) using 1
    · rfl
    · dsimp; ring
  convert hweight.mul (hUN.hasDerivAt_envelope_quotient hs hs0 x) using 1
  ext s₁
  dsimp
  ring

private theorem inner_parameter_bounds {s : ℝ} (hs : s ∈ envelopeDomain bounds) :
    -μ₊ < s * μ₊ * μ₋ ∧ s * μ₊ * μ₋ < μ₋ := by
  have hup : s < 1 / μ₊ :=
    lt_of_lt_of_le hs.2 (one_div_le_one_div_of_le bounds.muPlus_pos bounds.muPlus_le_lPlus)
  have hlo : -(1 / μ₋) < s := by
    have h := one_div_le_one_div_of_le bounds.muMinus_pos bounds.muMinus_le_lMinus
    have hslo : -(1 / L₋) < s := by
      simpa only [envelopeDomain, Set.mem_Ioo, neg_div] using hs.1
    linarith only [h, hslo]
  have h1 := (lt_div_iff₀ bounds.muPlus_pos).mp hup
  have h2 : -1 < s * μ₋ := by
    have := (div_lt_iff₀ bounds.muMinus_pos).mp (show -1 / μ₋ < s by rw [neg_div]; exact hlo)
    exact this
  constructor
  · nlinarith [mul_lt_mul_of_pos_right h2 bounds.muPlus_pos]
  · nlinarith [mul_lt_mul_of_pos_right h1 bounds.muMinus_pos]

/-- The inner curvature bounds control the derivative of the weighted envelope quotient from below. -/
private theorem weighted_envelope_quotient_deriv_lower (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (hs_ne : s ≠ 0) (x : H) :
    μ₊ * μ₋ / 2 * ‖x - xStar‖ ^ 2 ≤ deriv (fun s₁ => (1 - s₁ * μ₊) * (1 + s₁ * μ₋) * M s₁ x / s₁) s := by
  let ξ := J s x
  let bregmanGap := D ξ xStar - D xStar ξ
  have hvalue : M s x / s = E ξ - EStar - s / 2 * ‖g ξ‖ ^ 2 := by
    have h := hUN.envelope_at_step hs ξ
    rw [hUN.resolvent_equation hs] at h
    rw [h]
    field_simp
  have href := hUN.refined_inner_secant ξ xStar
  rw [hUN.gradient_stationaryPoint, sub_zero] at href
  have hcoeff : |bounds.innerCenter + s * μ₊ * μ₋| ≤ bounds.innerRadius := by
    have hp := inner_parameter_bounds hs
    rw [abs_le]
    dsimp [CurvatureBounds.innerCenter, CurvatureBounds.innerRadius]
    constructor <;> linarith [hp.1, hp.2]
  have hab : (bounds.innerCenter + s * μ₊ * μ₋) * bregmanGap ≤ bounds.innerRadius * |bregmanGap| := by
    exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _))
  have hd : bregmanGap = 2 * (E ξ - EStar) - ⟪g ξ, ξ - xStar⟫ := by
    dsimp [bregmanGap, bregman, stationaryValue]
    rw [hUN.gradient_stationaryPoint, inner_zero_left, ← neg_sub ξ xStar, inner_neg_right]
    ring
  have hx : x - xStar = (ξ - xStar) - s • g ξ := by
    have h := hUN.resolvent_equation hs x
    calc
      _ = (ξ - s • g ξ) - xStar := congrArg (fun z => z - xStar) h.symm
      _ = _ := by abel
  rw [(hUN.hasDerivAt_weighted_quotient hs hs_ne x).deriv, hvalue]
  change μ₊ * μ₋ / 2 * ‖x - xStar‖ ^ 2 ≤ _
  rw [hx, norm_sub_sq_real]
  rw [norm_sub_sq_real] at href
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right] at href ⊢
  rw [real_inner_comm (g ξ) (ξ - xStar)]
  change 2 * bounds.innerRadius * |bregmanGap| ≤ _ at href
  dsimp [CurvatureBounds.innerRadius, CurvatureBounds.innerCenter] at href hab
  rw [hd] at hab href
  dsimp [ξ] at href hab ⊢
  nlinarith only [href, hab]

/-- Quadratic comparison between the envelope and the energy gap. -/
theorem envelope_comparison (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x : H) :
    s * (E x - EStar) + s ^ 2 * μ₊ * μ₋ / 2 * ‖x - xStar‖ ^ 2 ≤ (1 - s * μ₊) * (1 + s * μ₋) * M s x := by
  classical
  let ΔE := E x - EStar
  let C := μ₊ * μ₋ / 2 * ‖x - xStar‖ ^ 2
  let Mx : ℝ → ℝ := fun s₁ => M s₁ x
  let ω : ℝ → ℝ := fun s₁ => (1 - s₁ * μ₊) * (1 + s₁ * μ₋)
  let Q : ℝ → ℝ := fun s₁ => ω s₁ * Mx s₁ / s₁
  let quotientExt : ℝ → ℝ := Function.update (fun s₁ => Mx s₁ / s₁) 0 ΔE
  let weightedExt : ℝ → ℝ := fun s₁ => ω s₁ * quotientExt s₁
  have h0 : (0 : ℝ) ∈ envelopeDomain bounds := by
    constructor
    · exact div_neg_of_neg_of_pos (by norm_num) bounds.lMinus_pos
    · exact div_pos zero_lt_one bounds.lPlus_pos
  have hω (s₁ : ℝ) : DifferentiableAt ℝ ω s₁ := by dsimp [ω]; fun_prop
  have hQ (s₁ : ℝ) (hs₁ : s₁ ∈ envelopeDomain bounds) (hs₁_ne : s₁ ≠ 0) :
      DifferentiableAt ℝ Q s₁ := by
    convert (hω s₁).mul (hUN.hasDerivAt_envelope_quotient hs₁ hs₁_ne x).differentiableAt using 1
    ext s₁
    dsimp [Q, ω, Mx]
    ring
  have hnear (s₁ : ℝ) (hs₁_ne : s₁ ≠ 0) : weightedExt =ᶠ[𝓝 s₁] Q := by
    filter_upwards [eventually_ne_nhds hs₁_ne] with u hu
    dsimp [weightedExt, Q, quotientExt]
    rw [Function.update_of_ne hu]
    ring
  have hWeighted_zero : weightedExt 0 = ΔE := by simp [weightedExt, ω, quotientExt]
  have hWeighted_continuous_zero : ContinuousAt weightedExt 0 := by
    have hd := hUN.hasDerivAt_envelope h0 x
    simp only [resolvent_zero] at hd
    have hQuotientExt : ContinuousAt quotientExt 0 := by simpa [quotientExt, Mx, ΔE] using hd.continuousAt_div
    exact (hω 0).continuousAt.mul hQuotientExt
  have hWeighted_continuous : ContinuousOn weightedExt (envelopeDomain bounds) := by
    intro s₁ hs₁
    by_cases hs₁_ne : s₁ = 0
    · subst s₁; exact hWeighted_continuous_zero.continuousWithinAt
    · exact ((hQ s₁ hs₁ hs₁_ne).continuousAt.congr_of_eventuallyEq (hnear s₁ hs₁_ne)).continuousWithinAt
  have hsec (a b : ℝ)
      (ha : a ∈ envelopeDomain bounds) (hb : b ∈ envelopeDomain bounds)
      (hab : a ≤ b) (havoid : ∀ s₁ ∈ Set.Ioo a b, s₁ ≠ 0) :
      C * (b - a) ≤ weightedExt b - weightedExt a := by
    have hsub : Set.Icc a b ⊆ envelopeDomain bounds := by
      intro s₁ hs₁
      exact ⟨lt_of_lt_of_le ha.1 hs₁.1, lt_of_le_of_lt hs₁.2 hb.2⟩
    apply (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv (hWeighted_continuous.mono hsub)
      (fun s₁ hs₁ => ?_) (fun s₁ hs₁ => ?_) a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab
    · rw [interior_Icc] at hs₁
      exact ((hQ s₁ (hsub ⟨hs₁.1.le, hs₁.2.le⟩) (havoid s₁ hs₁)).congr_of_eventuallyEq
        (hnear s₁ (havoid s₁ hs₁))).differentiableWithinAt
    · rw [interior_Icc] at hs₁
      rw [(hnear s₁ (havoid s₁ hs₁)).deriv_eq]
      exact hUN.weighted_envelope_quotient_deriv_lower (hsub ⟨hs₁.1.le, hs₁.2.le⟩) (havoid s₁ hs₁) x
  by_cases hs0 : s = 0
  · subst s; simp
  have hWeighted_eq : weightedExt s = Q s := by
    dsimp [weightedExt, Q, quotientExt]
    rw [Function.update_of_ne hs0]
    ring
  rcases lt_or_gt_of_ne hs0 with hs₁ | hs₁
  · have h := hsec s 0 hs h0 hs₁.le (fun s₁ hs₁ => ne_of_lt hs₁.2)
    rw [hWeighted_zero, hWeighted_eq] at h
    have hmul := mul_le_mul_of_nonpos_right h hs₁.le
    dsimp [Q] at hmul
    have hcancel : ω s * Mx s / s * s = ω s * Mx s :=
      div_mul_cancel₀ _ hs0
    dsimp [ΔE, C, ω, Mx] at hmul ⊢
    nlinarith [hcancel]
  · have h := hsec 0 s h0 hs hs₁.le (fun s₁ hs₁ => ne_of_gt hs₁.1)
    rw [hWeighted_zero, hWeighted_eq] at h
    have hmul := mul_le_mul_of_nonneg_right h hs₁.le
    dsimp [Q] at hmul
    have hcancel : ω s * Mx s / s * s = ω s * Mx s :=
      div_mul_cancel₀ _ hs0
    dsimp [ΔE, C, ω, Mx] at hmul ⊢
    nlinarith [hcancel]

/-- Envelope covariance under a quadratic shift about the stationary point. -/
theorem envelope_quadraticShift (hUN : IsUN bounds E)
    {s c : ℝ} (hs : s ∈ envelopeDomain bounds)
    (hLower : -μ₋ < c) (hUpper : c < μ₊) (x : H) :
    envelope (UN.quadraticShift E c xStar)
      (shiftedEnvelopeParameter s c) (rescaledEnvelopePoint E s c x) =
      M s x / (1 - s * c) - s * c / (2 * (1 - s * c) ^ 2) * ‖x - xStar‖ ^ 2 := by
  let gshift := fun z => g z - c • (z - xStar)
  let Eshift := UN.quadraticShift E c xStar
  have hshift := hUN.quadraticShift c hLower hUpper xStar
  have hs₁ := Envelopes.shiftedEnvelopeParameter_mem hs hLower hUpper
  have hd := Envelopes.rescaling_denominator_pos hs ⟨hLower.le, hUpper.le⟩
  have hdne := ne_of_gt hd
  have hstationary : stationaryPoint Eshift = xStar := by
    have h := hshift.gradient_eq_zero_iff xStar
    rw [gradient_quadraticShift hUN.differentiable] at h
    exact (h.mp (by simp [hUN.gradient_stationaryPoint])).symm
  have hvalue : stationaryValue Eshift = EStar := by
    simp [stationaryValue, hstationary, Eshift, UN.quadraticShift]
  have hr : resolvent gshift (shiftedEnvelopeParameter s c)
      (rescaledEnvelopePoint E s c x) = J s x := by
    have heq : J s x - shiftedEnvelopeParameter s c • gshift (J s x) = rescaledEnvelopePoint E s c x := by
      unfold gshift shiftedEnvelopeParameter rescaledEnvelopePoint
      conv_rhs => rw [← hUN.resolvent_equation hs x]
      apply (smul_right_injective («M» := H) hdne)
      simp only [smul_sub, smul_add, smul_smul]
      field_simp
      module
    rw [← heq]
    simpa only [gradient_quadraticShift hUN.differentiable] using hshift.resolvent_apply_step hs₁ (J s x)
  change envelope Eshift _ _ = _
  unfold envelope envelopeObjective
  rw [gradient_quadraticShift hUN.differentiable, hr, hvalue]
  dsimp [Eshift, UN.quadraticShift, shiftedEnvelopeParameter, rescaledEnvelopePoint]
  rw [show J s x - (xStar + (1 - s * c)⁻¹ • (x - xStar)) =
      (J s x - xStar) - (1 - s * c)⁻¹ • (x - xStar) by module,
    show J s x - x = (J s x - xStar) - (x - xStar) by module]
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right]
  field_simp
  ring

/-- Envelope comparison after rescaling about the stationary point. -/
theorem envelope_rescaled_comparison (hUN : IsUN bounds E)
    {s c : ℝ} (hs : s ∈ envelopeDomain bounds)
    (hc_mem : c ∈ Set.Icc (-μ₋) μ₊) (x : H) :
    s * (1 - s * c) ^ 2 * (E (rescaledEnvelopePoint E s c x) - EStar) +
      s ^ 2 * μ₊ * μ₋ / 2 * ‖x - xStar‖ ^ 2 ≤
      (1 - s * μ₊) * (1 + s * μ₋) * M s x := by
  have hopen : ∀ c ∈ Set.Ioo (-μ₋) μ₊,
      s * (1 - s * c) ^ 2 * (E (rescaledEnvelopePoint E s c x) - EStar) +
        s ^ 2 * μ₊ * μ₋ / 2 * ‖x - xStar‖ ^ 2 ≤
        (1 - s * μ₊) * (1 + s * μ₋) * M s x := by
    intro c hc
    have hd := Envelopes.rescaling_denominator_pos hs ⟨hc.1.le, hc.2.le⟩
    have hdne := ne_of_gt hd
    let Eshift := UN.quadraticShift E c xStar
    have hshift := hUN.quadraticShift c hc.1 hc.2 xStar
    have hs₁ := Envelopes.shiftedEnvelopeParameter_mem hs hc.1 hc.2
    have hstationary : stationaryPoint Eshift = xStar := by
      have h := hshift.gradient_eq_zero_iff xStar
      rw [gradient_quadraticShift hUN.differentiable] at h
      exact (h.mp (by simp [hUN.gradient_stationaryPoint])).symm
    have hvalue : stationaryValue Eshift = EStar := by
      simp [stationaryValue, hstationary, Eshift, UN.quadraticShift]
    have hcomp := hshift.envelope_comparison hs₁ (rescaledEnvelopePoint E s c x)
    change shiftedEnvelopeParameter s c * (Eshift (rescaledEnvelopePoint E s c x) - stationaryValue Eshift) +
      (shiftedEnvelopeParameter s c) ^ 2 * (μ₊ - c) * (μ₋ + c) / 2 * ‖rescaledEnvelopePoint E s c x - stationaryPoint Eshift‖ ^ 2 ≤ _ at hcomp
    rw [hstationary, hvalue, hUN.envelope_quadraticShift hs hc.1 hc.2] at hcomp
    dsimp [Eshift, UN.quadraticShift, shiftedEnvelopeParameter, CurvatureBounds.shift] at hcomp
    have hnorm : ‖rescaledEnvelopePoint E s c x - xStar‖ ^ 2 = ((1 - s * c)⁻¹) ^ 2 * ‖x - xStar‖ ^ 2 := by
      simp [rescaledEnvelopePoint, norm_smul, mul_pow]
    rw [hnorm] at hcomp
    apply sub_nonpos.mp
    convert mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hd.le 3) (sub_nonpos.mpr hcomp) using 1
    field_simp
    ring
  have hd := Envelopes.rescaling_denominator_pos hs hc_mem
  have hrescale : ContinuousAt (fun c => rescaledEnvelopePoint E s c x) c := by
    unfold rescaledEnvelopePoint
    apply continuousAt_const.add
    apply ContinuousAt.smul
    · apply ContinuousAt.inv₀
      · fun_prop
      · exact ne_of_gt hd
    · fun_prop
  have he : ContinuousAt (fun c => E (rescaledEnvelopePoint E s c x)) c :=
    (hUN.hasGradientAt _).continuousAt.comp hrescale
  have hleft : ContinuousAt
      (fun c => s * (1 - s * c) ^ 2 * (E (rescaledEnvelopePoint E s c x) - EStar) +
        s ^ 2 * μ₊ * μ₋ / 2 * ‖x - xStar‖ ^ 2) c := by
    exact ((continuousAt_const.mul
      ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).pow 2)).mul
      (he.sub continuousAt_const)).add continuousAt_const
  have hmem : c ∈ closure (Set.Ioo (-μ₋) μ₊) := by
    rw [closure_Ioo (by linarith [bounds.muPlus_pos, bounds.muMinus_pos])]
    exact hc_mem
  exact ContinuousWithinAt.closure_le hmem hleft.continuousWithinAt
    continuousWithinAt_const hopen

end IsUN
end UN
