module

public import UniformNondegeneracy.Analysis.GradientSteps
public import UniformNondegeneracy.Geometry.Basic
public import UniformNondegeneracy.Geometry.InverseEnergy

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Two-sided envelopes and resolvents

For a UN energy, the resolvent gives the unique envelope maximizer and determines the spatial and parameter derivatives. The gradient step is the unique minimizer of the envelope's proximal objective.
-/

noncomputable section

open Filter Asymptotics
open scoped Topology

namespace UN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The resolvent `Jₛ = (I - s g)⁻¹`. -/
def resolvent (g : H → H) (s : ℝ) : H → H :=
  Function.invFun (fun x => x - s • g x)

/-- The envelope parameter interval determined by the outer curvature bounds. -/
def envelopeDomain (bounds : CurvatureBounds) : Set ℝ :=
  Set.Ioo (-1 / bounds.lMinus) (1 / bounds.lPlus)

/-- The objective maximized over `ξ` when constructing the envelope. -/
def envelopeObjective (E : H → ℝ) (s : ℝ) (x ξ : H) : ℝ :=
  s * (E ξ - stationaryValue E) - (1 / 2 : ℝ) * ‖ξ - x‖ ^ 2

/-- The envelope objective evaluated at the resolvent. -/
def envelope (E : H → ℝ) (s : ℝ) (x : H) : ℝ :=
  envelopeObjective E s x (resolvent (gradient E) s x)

/-- Lower bound for the directional secants of the signed gradient step. -/
def gradientStepModulus (bounds : CurvatureBounds) (s : ℝ) : ℝ :=
  min (1 - s * bounds.lPlus) (1 + s * bounds.lMinus)

omit [CompleteSpace H] in
@[simp] theorem resolvent_zero (g : H → H) (x : H) :
    resolvent g 0 x = x := by
  simp only [resolvent, zero_smul, sub_zero]
  exact Function.leftInverse_invFun Function.injective_id x

@[simp] theorem envelope_zero (E : H → ℝ) (x : H) :
    envelope E 0 x = 0 := by
  simp [envelope, envelopeObjective]

variable {bounds : CurvatureBounds} {E : H → ℝ}

local notation "g" => gradient E

local notation "L₊" => bounds.lPlus
local notation "L₋" => bounds.lMinus
local notation "D" => bregman E
local notation "xStar" => stationaryPoint E
local notation "EStar" => stationaryValue E
local notation "J" => resolvent g
local notation "M" => envelope E

/-!
## Resolvent properties
-/

theorem gradientStepModulus_pos {s : ℝ} (hs : s ∈ envelopeDomain bounds) :
    0 < gradientStepModulus bounds s := by
  rcases hs with ⟨hl, hu⟩
  have hp := bounds.lPlus_pos
  have hm := bounds.lMinus_pos
  have hu' := (lt_div_iff₀ hp).mp hu
  have hl' := (div_lt_iff₀ hm).mp hl
  exact lt_min (by linarith) (by nlinarith)

namespace IsUN

/-- A directional secant bound for the signed gradient step. -/
theorem gradientStep_monotonicity_bound (hUN : IsUN bounds E) (s : ℝ) (x₁ x₂ : H) :
    gradientStepModulus bounds s * ‖x₁ - x₂‖ ^ 2 ≤ ⟪(x₁ - s • g x₁) - (x₂ - s • g x₂), x₁ - x₂⟫ := by
  have hb := hUN.directional_secant_bounds x₁ x₂
  have heq : (x₁ - s • g x₁) - (x₂ - s • g x₂) = (x₁ - x₂) - s • (g x₁ - g x₂) := by module
  rw [heq, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  change min (1 - s * L₊) (1 + s * L₋) * _ ≤ _
  rcases le_total 0 s with hs₁ | hs₁
  · have h := mul_le_mul_of_nonneg_left hb.2 hs₁
    have hm := mul_le_mul_of_nonneg_right
      (min_le_left (1 - s * L₊) (1 + s * L₋)) (sq_nonneg ‖x₁ - x₂‖)
    nlinarith
  · have h := mul_le_mul_of_nonpos_left hb.1 hs₁
    have hm := mul_le_mul_of_nonneg_right
      (min_le_right (1 - s * L₊) (1 + s * L₋)) (sq_nonneg ‖x₁ - x₂‖)
    nlinarith

theorem gradientStep_lower_norm (hUN : IsUN bounds E) (s : ℝ) (x₁ x₂ : H) :
    gradientStepModulus bounds s * ‖x₁ - x₂‖ ≤ ‖(x₁ - s • g x₁) - (x₂ - s • g x₂)‖ := by
  have hs₁ := hUN.gradientStep_monotonicity_bound s x₁ x₂
  have hc := real_inner_le_norm ((x₁ - s • g x₁) - (x₂ - s • g x₂)) (x₁ - x₂)
  by_cases he : x₁ = x₂
  · simp [he]
  · have hp : 0 < ‖x₁ - x₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
    nlinarith

theorem gradientStep_upper_norm (hUN : IsUN bounds E) (s : ℝ) (x₁ x₂ : H) :
    ‖(x₁ - s • g x₁) - (x₂ - s • g x₂)‖ ≤ (1 + |s| * bounds.lMax) * ‖x₁ - x₂‖ := by
  have heq : (x₁ - s • g x₁) - (x₂ - s • g x₂) = (x₁ - x₂) - s • (g x₁ - g x₂) := by module
  rw [heq]
  calc
    _ ≤ ‖x₁ - x₂‖ + ‖s • (g x₁ - g x₂)‖ := norm_sub_le _ _
    _ = ‖x₁ - x₂‖ + |s| * ‖g x₁ - g x₂‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖x₁ - x₂‖ + |s| * (bounds.lMax * ‖x₁ - x₂‖) := by
      gcongr
      exact hUN.gradient_upper_bound x₁ x₂
    _ = _ := by ring

theorem gradientStep_bijective (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) :
    Function.Bijective (fun x => x - s • g x) := by
  apply GradientMap.bijective_of_bilipschitz (gradientStepPotential E s)
    (fun x => x - s • g x)
    (gradientStepModulus bounds s) (1 + |s| * bounds.lMax)
  · exact fun x => hasGradientAt_gradientStepPotential (hUN.differentiable x) s
  · exact gradientStepModulus_pos hs
  · exact hUN.gradientStep_lower_norm s
  · exact hUN.gradientStep_upper_norm s

theorem resolvent_equation (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x : H) :
    J s x - s • g (J s x) = x := by
  exact Function.rightInverse_invFun (hUN.gradientStep_bijective hs).surjective x

theorem resolvent_apply_step (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x : H) :
    J s (x - s • g x) = x := by
  exact Function.leftInverse_invFun (hUN.gradientStep_bijective hs).injective x

theorem resolvent_norm_sub_le (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x₁ x₂ : H) :
    ‖J s x₁ - J s x₂‖ ≤ (gradientStepModulus bounds s)⁻¹ * ‖x₁ - x₂‖ := by
  exact GradientMap.inverse_norm_sub_le
    (fun x => x - s • g x) (J s)
    (gradientStepModulus bounds s) (gradientStepModulus_pos hs)
    (hUN.gradientStep_lower_norm s) (hUN.resolvent_equation hs) x₁ x₂

theorem resolvent_lipschitz (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) :
    LipschitzWith ⟨(gradientStepModulus bounds s)⁻¹, inv_nonneg.mpr (gradientStepModulus_pos hs).le⟩ (J s) :=
  lipschitzWith_iff_norm_sub_le.mpr (hUN.resolvent_norm_sub_le hs)

theorem resolvent_continuous (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) :
    Continuous (J s) :=
  (hUN.resolvent_lipschitz hs).continuous

theorem resolvent_parameter_continuousAt (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x : H) :
    ContinuousAt (fun s₁ => J s₁ x) s := by
  let xOpt := J s x
  have hdomain : ∀ᶠ s₁ in 𝓝 s, s₁ ∈ envelopeDomain bounds :=
    isOpen_Ioo.mem_nhds hs
  have hmod : ContinuousAt (fun s₁ => gradientStepModulus bounds s₁) s := by
    unfold gradientStepModulus
    fun_prop
  have hbound : ∀ᶠ s₁ in 𝓝 s,
      ‖J s₁ x - xOpt‖ ≤ (gradientStepModulus bounds s₁)⁻¹ * (|s₁ - s| * ‖g xOpt‖) := by
    filter_upwards [hdomain] with s₁ hs₁
    have hi := hUN.resolvent_norm_sub_le hs₁ x (xOpt - s₁ • g xOpt)
    rw [hUN.resolvent_apply_step hs₁ xOpt] at hi
    have hz := hUN.resolvent_equation hs x
    change xOpt - s • g xOpt = x at hz
    have heq : x - (xOpt - s₁ • g xOpt) = (s₁ - s) • g xOpt := by
      rw [← hz]
      module
    simpa only [heq, norm_smul, Real.norm_eq_abs] using hi
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun s₁ => norm_nonneg _)) hbound
  have hm := hmod.inv₀ (ne_of_gt (gradientStepModulus_pos hs))
  have hc : ContinuousAt
      (fun s₁ => (gradientStepModulus bounds s₁)⁻¹ * (|s₁ - s| * ‖g xOpt‖)) s :=
    hm.mul (((continuousAt_id.sub continuousAt_const).abs).mul continuousAt_const)
  simpa only [sub_self, abs_zero, zero_mul, mul_zero] using hc.tendsto

/-!
## Envelope maximization
-/

/-- The objective gap controls the squared distance to the resolvent. -/
theorem envelopeObjective_gap (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x ξ : H) :
    envelopeObjective E s x ξ + gradientStepModulus bounds s / 2 * ‖ξ - J s x‖ ^ 2 ≤ M s x := by
  let xOpt := J s x
  have hz : xOpt - x = s • g xOpt := by
    have h := hUN.resolvent_equation hs x
    change xOpt - s • g xOpt = x at h
    rw [← h]
    module
  have hn : ‖ξ - x‖ ^ 2 = ‖ξ - xOpt‖ ^ 2 + 2 * ⟪g xOpt, ξ - xOpt⟫ * s + ‖xOpt - x‖ ^ 2 := by
    have hvec : ξ - x = (ξ - xOpt) + (xOpt - x) := by module
    rw [hvec, norm_add_sq_real]
    rw [hz, inner_smul_right, real_inner_comm (ξ - xOpt) (g xOpt)]
    ring
  have hb := hUN.bregman_bounds ξ xOpt
  have hm : gradientStepModulus bounds s * ‖ξ - xOpt‖ ^ 2 ≤ ‖ξ - xOpt‖ ^ 2 - 2 * s * D ξ xOpt := by
    rcases le_total 0 s with hs₁ | hs₁
    · have hi := mul_le_mul_of_nonneg_left hb.2 hs₁
      have hm := mul_le_mul_of_nonneg_right
        (min_le_left (1 - s * L₊) (1 + s * L₋)) (sq_nonneg ‖ξ - xOpt‖)
      change min _ _ * _ ≤ _
      nlinarith
    · have hi := mul_le_mul_of_nonpos_left hb.1 hs₁
      have hm := mul_le_mul_of_nonneg_right
        (min_le_right (1 - s * L₊) (1 + s * L₋)) (sq_nonneg ‖ξ - xOpt‖)
      change min _ _ * _ ≤ _
      nlinarith
  change envelopeObjective E s x ξ + gradientStepModulus bounds s / 2 * ‖ξ - xOpt‖ ^ 2 ≤ envelopeObjective E s x xOpt
  unfold envelopeObjective
  unfold bregman at hm
  nlinarith

theorem envelopeObjective_le_envelope (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x ξ : H) :
    envelopeObjective E s x ξ ≤ M s x := by
  have h := hUN.envelopeObjective_gap hs x ξ
  have hnonneg : 0 ≤ gradientStepModulus bounds s / 2 * ‖ξ - J s x‖ ^ 2 :=
    mul_nonneg (div_nonneg (le_of_lt (gradientStepModulus_pos hs)) (by norm_num))
      (sq_nonneg _)
  linarith

theorem envelopeObjective_eq_iff (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x ξ : H) :
    envelopeObjective E s x ξ = M s x ↔ ξ = J s x := by
  constructor
  · intro he
    have h := hUN.envelopeObjective_gap hs x ξ
    rw [he] at h
    have hm := gradientStepModulus_pos hs
    have hn : ‖ξ - J s x‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖ξ - J s x‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
  · rintro rfl
    rfl

/-- The resolvent is the unique maximizer of the envelope objective. -/
theorem envelope_maximizer_iff (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x ξ : H) :
    IsMaxOn (envelopeObjective E s x) Set.univ ξ ↔ ξ = J s x := by
  rw [isMaxOn_univ_iff]
  constructor
  · intro h
    apply (hUN.envelopeObjective_eq_iff hs x ξ).mp
    exact le_antisymm (hUN.envelopeObjective_le_envelope hs x ξ) (h (J s x))
  · rintro rfl u
    exact hUN.envelopeObjective_le_envelope hs x u

/-- The envelope is the supremum of its objective. -/
theorem envelope_eq_iSup (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x : H) :
    M s x = ⨆ ξ : H, envelopeObjective E s x ξ := by
  symm
  apply IsGreatest.csSup_eq
  refine ⟨⟨J s x, rfl⟩, ?_⟩
  rintro _ ⟨ξ, rfl⟩
  exact hUN.envelopeObjective_le_envelope hs x ξ

/-- The stationary point as a trial point gives a lower bound on the envelope. -/
theorem envelope_lower (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x : H) :
    -(1 / 2 : ℝ) * ‖x - xStar‖ ^ 2 ≤ M s x := by
  simpa [envelopeObjective, stationaryValue, norm_sub_rev] using
    hUN.envelopeObjective_le_envelope hs x xStar

/-!
## Spatial and parameter derivatives
-/

/-- The spatial gradient of the envelope is `J s x - x`. -/
theorem hasGradientAt_envelope (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x : H) :
    HasGradientAt (M s) (J s x - x) x := by
  have hd := GradientMap.hasGradientAt_inverseEnergy
    (gradientStepPotential E s) (fun x' => x' - s • g x')
    (J s) (gradientStepModulus bounds s)⁻¹
    (fun x' => hasGradientAt_gradientStepPotential (hUN.differentiable x') s)
    (hUN.resolvent_equation hs)
    (hUN.resolvent_norm_sub_le hs) x
  have hn : HasGradientAt (fun x' : H => (1 / 2 : ℝ) * ‖x'‖ ^ 2) x x := by
    simpa using hasGradientAt_quadratic (H := H) 1 0 x
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! (hd.hasFDerivAt.sub hn.hasFDerivAt).sub_const (s * EStar) using 1
  · funext x'
    simp only [envelope, envelopeObjective, inverseEnergy, gradientStepPotential, norm_sub_sq_real, Pi.sub_apply]
    rw [real_inner_comm x' (J s x')]
    ring
  · ext v
    simp [InnerProductSpace.toDual_apply_apply]

theorem gradient_envelope (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x : H) :
    gradient (M s) x = J s x - x :=
  (hUN.hasGradientAt_envelope hs x).gradient

/-- The parameter derivative is the energy gap at the resolvent. -/
theorem hasDerivAt_envelope (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x : H) :
    HasDerivAt (fun s₁ => M s₁ x) (E (J s x) - EStar) s := by
  have he : ContinuousAt (fun s₁ => E (J s₁ x)) s :=
    (hUN.hasGradientAt (J s x)).continuousAt.comp
      (f := fun s₁ => J s₁ x)
      (hUN.resolvent_parameter_continuousAt hs x)
  have hdomain : ∀ᶠ s₁ in 𝓝 s, s₁ ∈ envelopeDomain bounds :=
    isOpen_Ioo.mem_nhds hs
  apply hasDerivAt_iff_isLittleO.mpr
  apply IsLittleO.of_bound
  intro c hc
  have hsmall : ∀ᶠ s₁ in 𝓝 s, |E (J s₁ x) - E (J s x)| < c := by
    have hz := (he.tendsto.sub_const (E (J s x))).abs
    simp only [sub_self, abs_zero] at hz
    exact hz (Iio_mem_nhds hc)
  filter_upwards [hdomain, hsmall] with s₁ hs₁ hsmall
  have hl := hUN.envelopeObjective_le_envelope hs₁ x (J s x)
  have hu := hUN.envelopeObjective_le_envelope hs x (J s₁ x)
  let remainder := M s₁ x - M s x - (s₁ - s) * (E (J s x) - EStar)
  have hnonneg : 0 ≤ remainder := by
    dsimp [remainder, envelope, envelopeObjective] at hl ⊢
    nlinarith
  have hupper : remainder ≤ (s₁ - s) * (E (J s₁ x) - E (J s x)) := by
    dsimp [remainder, envelope, envelopeObjective] at hl hu ⊢
    nlinarith
  change ‖remainder‖ ≤ c * ‖s₁ - s‖
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, Real.norm_eq_abs]
  calc
    remainder ≤ (s₁ - s) * (E (J s₁ x) - E (J s x)) := hupper
    _ ≤ |s₁ - s| * |E (J s₁ x) - E (J s x)| := by
      rw [← abs_mul]
      exact le_abs_self _
    _ ≤ c * |s₁ - s| := by
      nlinarith [mul_le_mul_of_nonneg_left (le_of_lt hsmall) (abs_nonneg (s₁ - s))]

theorem deriv_envelope (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x : H) :
    deriv (fun s₁ => M s₁ x) s = E (J s x) - EStar :=
  (hUN.hasDerivAt_envelope hs x).deriv

/-!
## Proximal identities
-/

/-- The scaled energy gap bounds the proximal objective from below. -/
theorem envelope_proximal_lower (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x ξ : H) :
    s * (E x - EStar) ≤ M s ξ + (1 / 2 : ℝ) * ‖ξ - x‖ ^ 2 := by
  have h := hUN.envelopeObjective_le_envelope hs ξ x
  simpa [envelopeObjective, norm_sub_rev, sub_le_iff_le_add] using h

theorem envelope_at_step (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x : H) :
    M s (x - s • g x) = s * (E x - EStar) - s ^ 2 / 2 * ‖g x‖ ^ 2 := by
  unfold envelope envelopeObjective
  rw [hUN.resolvent_apply_step hs]
  simp only [sub_sub_cancel, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- The proximal objective attains the scaled energy gap exactly at the gradient step. -/
theorem envelope_proximal_eq_iff (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x ξ : H) :
    M s ξ + (1 / 2 : ℝ) * ‖ξ - x‖ ^ 2 = s * (E x - EStar) ↔ ξ = x - s • g x := by
  have hEq : M s ξ + (1 / 2 : ℝ) * ‖ξ - x‖ ^ 2 = s * (E x - EStar) ↔ x = J s ξ := by
    rw [← hUN.envelopeObjective_eq_iff hs ξ x]
    unfold envelopeObjective
    rw [norm_sub_rev x ξ]
    constructor <;> intro h <;> linarith
  rw [hEq]
  constructor
  · intro h
    rw [h]
    exact (hUN.resolvent_equation hs ξ).symm
  · rintro rfl
    exact (hUN.resolvent_apply_step hs x).symm

/-- The gradient step is the unique minimizer of the proximal objective. -/
theorem envelope_proximal_minimizer_iff (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x ξ : H) :
    IsMinOn (fun u => M s u + (1 / 2 : ℝ) * ‖u - x‖ ^ 2) Set.univ ξ ↔ ξ = x - s • g x := by
  have hAt := (hUN.envelope_proximal_eq_iff hs x (x - s • g x)).mpr rfl
  rw [isMinOn_univ_iff]
  constructor
  · intro h
    apply (hUN.envelope_proximal_eq_iff hs x ξ).mp
    exact le_antisymm ((h (x - s • g x)).trans_eq hAt) (hUN.envelope_proximal_lower hs x ξ)
  · rintro rfl u
    rw [hAt]
    exact hUN.envelope_proximal_lower hs x u

/-- The minimum proximal value recovers the scaled energy gap. -/
theorem envelope_proximal_value (hUN : IsUN bounds E)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x : H) :
    (⨅ ξ : H, M s ξ + (1 / 2 : ℝ) * ‖ξ - x‖ ^ 2) = s * (E x - EStar) := by
  apply IsLeast.csInf_eq
  refine ⟨⟨x - s • g x, (hUN.envelope_proximal_eq_iff hs x (x - s • g x)).mpr rfl⟩, ?_⟩
  rintro _ ⟨ξ, rfl⟩
  exact hUN.envelope_proximal_lower hs x ξ

end IsUN


end UN
