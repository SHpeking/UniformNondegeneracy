module

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
def envelopeObjective (E : H → ℝ) (g : H → H) (s : ℝ) (x ξ : H) : ℝ :=
  s * (E ξ - stationaryValue E g) - (1 / 2 : ℝ) * ‖ξ - x‖ ^ 2

/-- The envelope objective evaluated at the resolvent. -/
def interiorEnvelope (E : H → ℝ) (g : H → H) (s : ℝ) (x : H) : ℝ :=
  envelopeObjective E g s x (resolvent g s x)

/-- Potential whose gradient is `I - s • g`. -/
def resolventPotential (E : H → ℝ) (s : ℝ) : H → ℝ :=
  fun x => (1 / 2 : ℝ) * ‖x‖ ^ 2 - s * E x

/-- Lower bound for the directional secants of `I - s g`. -/
def resolventModulus (bounds : CurvatureBounds) (s : ℝ) : ℝ :=
  min (1 - s * bounds.lPlus) (1 + s * bounds.lMinus)

variable {bounds : CurvatureBounds} {E : H → ℝ} {g : H → H}

local notation "L₊" => bounds.lPlus
local notation "L₋" => bounds.lMinus
local notation "D" => bregman E g
local notation "xStar" => stationaryPoint g
local notation "EStar" => stationaryValue E g
local notation "J" => resolvent g
local notation "M" => interiorEnvelope E g

/-!
## Resolvent properties
-/

theorem resolventModulus_pos {s : ℝ} (hs : s ∈ envelopeDomain bounds) :
    0 < resolventModulus bounds s := by
  rcases hs with ⟨hl, hu⟩
  have hp := bounds.lPlus_pos
  have hm := bounds.lMinus_pos
  have hu' := (lt_div_iff₀ hp).mp hu
  have hl' := (div_lt_iff₀ hm).mp hl
  exact lt_min (by linarith) (by nlinarith)

namespace IsUN

theorem hasGradientAt_resolventPotential (hUN : IsUN bounds E g)
    (s : ℝ) (x : H) :
    HasGradientAt (resolventPotential E s) (x - s • g x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  unfold resolventPotential
  convert! ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (1 / 2 : ℝ)).sub
    ((hUN.has_gradient x).hasFDerivAt.const_mul s) using 1
  ext v
  simp [InnerProductSpace.toDual_apply_apply]

theorem resolventMap_strong_monotonicity (hUN : IsUN bounds E g)
    (s : ℝ)
    (x₁ x₂ : H) :
    resolventModulus bounds s * ‖x₁ - x₂‖ ^ 2 ≤ ⟪(x₁ - s • g x₁) - (x₂ - s • g x₂), x₁ - x₂⟫ := by
  have hb := hUN.outer_inner_bounds x₁ x₂
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

theorem resolventMap_lower_norm (hUN : IsUN bounds E g)
    (s : ℝ)
    (x₁ x₂ : H) :
    resolventModulus bounds s * ‖x₁ - x₂‖ ≤ ‖(x₁ - s • g x₁) - (x₂ - s • g x₂)‖ := by
  have hs₁ := hUN.resolventMap_strong_monotonicity s x₁ x₂
  have hc := real_inner_le_norm ((x₁ - s • g x₁) - (x₂ - s • g x₂)) (x₁ - x₂)
  by_cases he : x₁ = x₂
  · simp [he]
  · have hp : 0 < ‖x₁ - x₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
    nlinarith

theorem resolventMap_upper_norm (hUN : IsUN bounds E g)
    (s : ℝ) (x₁ x₂ : H) :
    ‖(x₁ - s • g x₁) - (x₂ - s • g x₂)‖ ≤ (1 + |s| * bounds.lMax) * ‖x₁ - x₂‖ := by
  have heq : (x₁ - s • g x₁) - (x₂ - s • g x₂) = (x₁ - x₂) - s • (g x₁ - g x₂) := by module
  rw [heq]
  calc
    _ ≤ ‖x₁ - x₂‖ + ‖s • (g x₁ - g x₂)‖ := norm_sub_le _ _
    _ = ‖x₁ - x₂‖ + |s| * ‖g x₁ - g x₂‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖x₁ - x₂‖ + |s| * (bounds.lMax * ‖x₁ - x₂‖) := by
      gcongr
      exact hUN.norm_sub_le_upper x₁ x₂
    _ = _ := by ring

theorem resolventMap_bijective (hUN : IsUN bounds E g)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) :
    Function.Bijective (fun x => x - s • g x) := by
  apply GradientMap.bijective_of_bounds (resolventPotential E s)
    (fun x => x - s • g x)
    (resolventModulus bounds s) (1 + |s| * bounds.lMax)
  · exact hUN.hasGradientAt_resolventPotential s
  · exact resolventModulus_pos hs
  · have hm : resolventModulus bounds s ≤ 1 := by
      unfold resolventModulus
      rcases le_total 0 s with hs₁ | hs₁
      · exact (min_le_left _ _).trans (by nlinarith [bounds.lPlus_pos])
      · exact (min_le_right _ _).trans (by nlinarith [bounds.lMinus_pos])
    nlinarith [mul_nonneg (abs_nonneg s) (le_of_lt bounds.lMax_pos)]
  · exact hUN.resolventMap_lower_norm s
  · exact hUN.resolventMap_upper_norm s

theorem resolvent_equation (hUN : IsUN bounds E g)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x : H) :
    J s x - s • g (J s x) = x := by
  exact Function.rightInverse_invFun (hUN.resolventMap_bijective hs).surjective x

theorem resolvent_apply_step (hUN : IsUN bounds E g)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x : H) :
    J s (x - s • g x) = x := by
  exact Function.leftInverse_invFun (hUN.resolventMap_bijective hs).injective x

theorem resolvent_norm_sub_le (hUN : IsUN bounds E g)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds)
    (x₁ x₂ : H) :
    ‖J s x₁ - J s x₂‖ ≤ (resolventModulus bounds s)⁻¹ * ‖x₁ - x₂‖ := by
  exact GradientMap.inverse_norm_sub_le
    (fun x => x - s • g x) (J s)
    (resolventModulus bounds s) (resolventModulus_pos hs)
    (hUN.resolventMap_lower_norm s) (hUN.resolvent_equation hs) x₁ x₂

theorem resolvent_continuous (hUN : IsUN bounds E g)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) :
    Continuous (J s) := by
  apply (LipschitzWith.of_dist_le_mul
    (K := ⟨(resolventModulus bounds s)⁻¹, le_of_lt (inv_pos.mpr (resolventModulus_pos hs))⟩) ?_).continuous
  intro x₁ x₂
  simp only [dist_eq_norm]
  exact_mod_cast hUN.resolvent_norm_sub_le hs x₁ x₂

theorem resolvent_parameter_continuousAt (hUN : IsUN bounds E g)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x : H) :
    ContinuousAt (fun s₁ => J s₁ x) s := by
  let xOpt := J s x
  have hdomain : ∀ᶠ s₁ in 𝓝 s, s₁ ∈ envelopeDomain bounds :=
    isOpen_Ioo.mem_nhds hs
  have hmod : ContinuousAt (fun s₁ => resolventModulus bounds s₁) s := by
    unfold resolventModulus
    fun_prop
  have hbound : ∀ᶠ s₁ in 𝓝 s,
      ‖J s₁ x - xOpt‖ ≤ (resolventModulus bounds s₁)⁻¹ * (|s₁ - s| * ‖g xOpt‖) := by
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
  have hm := hmod.inv₀ (ne_of_gt (resolventModulus_pos hs))
  have hc : ContinuousAt
      (fun s₁ => (resolventModulus bounds s₁)⁻¹ * (|s₁ - s| * ‖g xOpt‖)) s :=
    hm.mul (((continuousAt_id.sub continuousAt_const).abs).mul continuousAt_const)
  simpa only [sub_self, abs_zero, zero_mul, mul_zero] using hc.tendsto

/-!
## Envelope maximization
-/

/-- The objective gap controls the squared distance to the resolvent. -/
theorem envelopeObjective_gap (hUN : IsUN bounds E g)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds)
    (x ξ : H) :
    envelopeObjective E g s x ξ + resolventModulus bounds s / 2 * ‖ξ - J s x‖ ^ 2 ≤ M s x := by
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
  have hm : resolventModulus bounds s * ‖ξ - xOpt‖ ^ 2 ≤ ‖ξ - xOpt‖ ^ 2 - 2 * s * D ξ xOpt := by
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
  change envelopeObjective E g s x ξ + resolventModulus bounds s / 2 * ‖ξ - xOpt‖ ^ 2 ≤ envelopeObjective E g s x xOpt
  unfold envelopeObjective
  unfold bregman at hm
  nlinarith

theorem envelopeObjective_le_interiorEnvelope (hUN : IsUN bounds E g)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds)
    (x ξ : H) :
    envelopeObjective E g s x ξ ≤ M s x := by
  have h := hUN.envelopeObjective_gap hs x ξ
  have hnonneg : 0 ≤ resolventModulus bounds s / 2 * ‖ξ - J s x‖ ^ 2 :=
    mul_nonneg (div_nonneg (le_of_lt (resolventModulus_pos hs)) (by norm_num))
      (sq_nonneg _)
  linarith

theorem envelopeObjective_eq_iff (hUN : IsUN bounds E g)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds)
    (x ξ : H) :
    envelopeObjective E g s x ξ = M s x ↔ ξ = J s x := by
  constructor
  · intro he
    have h := hUN.envelopeObjective_gap hs x ξ
    rw [he] at h
    have hm := resolventModulus_pos hs
    have hn : ‖ξ - J s x‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖ξ - J s x‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
  · rintro rfl
    rfl

/-- The stationary point as a trial point gives a lower bound on the envelope. -/
theorem interiorEnvelope_lower (hUN : IsUN bounds E g)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x : H) :
    -(1 / 2 : ℝ) * ‖x - xStar‖ ^ 2 ≤ M s x := by
  simpa [envelopeObjective, stationaryValue, norm_sub_rev] using
    hUN.envelopeObjective_le_interiorEnvelope hs x xStar

/-!
## Spatial and parameter derivatives
-/

/-- The spatial gradient of the envelope is `J s x - x`. -/
theorem hasGradientAt_interiorEnvelope (hUN : IsUN bounds E g)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x : H) :
    HasGradientAt (M s) (J s x - x) x := by
  have hd := GradientMap.hasGradientAt_inverseEnergy
    (resolventPotential E s) (fun x' => x' - s • g x')
    (J s) (resolventModulus bounds s)⁻¹
    (hUN.hasGradientAt_resolventPotential s)
    (hUN.resolvent_equation hs) (hUN.resolvent_continuous hs)
    (hUN.resolvent_norm_sub_le hs) x
  have hn : HasGradientAt (fun x' : H => (1 / 2 : ℝ) * ‖x'‖ ^ 2) x x := by
    simpa using hasGradientAt_quadratic (H := H) 1 0 x
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! (hd.hasFDerivAt.sub hn.hasFDerivAt).sub_const (s * EStar) using 1
  · funext x'
    simp only [interiorEnvelope, envelopeObjective, inverseEnergy, resolventPotential, norm_sub_sq_real, Pi.sub_apply]
    rw [real_inner_comm x' (J s x')]
    ring
  · ext v
    simp [InnerProductSpace.toDual_apply_apply]

/-- The parameter derivative is the energy gap at the resolvent. -/
theorem hasDerivAt_interiorEnvelope (hUN : IsUN bounds E g)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x : H) :
    HasDerivAt (fun s₁ => M s₁ x) (E (J s x) - EStar) s := by
  have he : ContinuousAt (fun s₁ => E (J s₁ x)) s :=
    (hUN.has_gradient (J s x)).continuousAt.comp
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
  have hl := hUN.envelopeObjective_le_interiorEnvelope hs₁ x (J s x)
  have hu := hUN.envelopeObjective_le_interiorEnvelope hs x (J s₁ x)
  let remainder := M s₁ x - M s x - (s₁ - s) * (E (J s x) - EStar)
  have hnonneg : 0 ≤ remainder := by
    dsimp [remainder, interiorEnvelope, envelopeObjective] at hl ⊢
    nlinarith
  have hupper : remainder ≤ (s₁ - s) * (E (J s₁ x) - E (J s x)) := by
    dsimp [remainder, interiorEnvelope, envelopeObjective] at hl hu ⊢
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

/-!
## Proximal identities
-/

/-- The scaled energy gap bounds the proximal objective from below. -/
theorem interiorEnvelope_proximal_lower (hUN : IsUN bounds E g)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds)
    (x ξ : H) :
    s * (E x - EStar) ≤ M s ξ + (1 / 2 : ℝ) * ‖ξ - x‖ ^ 2 := by
  have h := hUN.envelopeObjective_le_interiorEnvelope hs ξ x
  simpa [envelopeObjective, norm_sub_rev, sub_le_iff_le_add] using h

theorem interiorEnvelope_at_step (hUN : IsUN bounds E g)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x : H) :
    M s (x - s • g x) = s * (E x - EStar) - s ^ 2 / 2 * ‖g x‖ ^ 2 := by
  unfold interiorEnvelope envelopeObjective
  rw [hUN.resolvent_apply_step hs]
  simp only [sub_sub_cancel, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- The proximal objective attains the scaled energy gap exactly at the gradient step. -/
theorem interiorEnvelope_proximal_eq_iff (hUN : IsUN bounds E g)
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
theorem interiorEnvelope_proximal_isMinOn_iff (hUN : IsUN bounds E g)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x ξ : H) :
    IsMinOn (fun u => M s u + (1 / 2 : ℝ) * ‖u - x‖ ^ 2) Set.univ ξ ↔ ξ = x - s • g x := by
  have hAt := (hUN.interiorEnvelope_proximal_eq_iff hs x (x - s • g x)).mpr rfl
  rw [isMinOn_univ_iff]
  constructor
  · intro h
    apply (hUN.interiorEnvelope_proximal_eq_iff hs x ξ).mp
    exact le_antisymm ((h (x - s • g x)).trans_eq hAt) (hUN.interiorEnvelope_proximal_lower hs x ξ)
  · rintro rfl u
    rw [hAt]
    exact hUN.interiorEnvelope_proximal_lower hs x u

/-- The minimum proximal value recovers the scaled energy gap. -/
theorem interiorEnvelope_proximal_iInf (hUN : IsUN bounds E g)
    {s : ℝ} (hs : s ∈ envelopeDomain bounds) (x : H) :
    (⨅ ξ : H, M s ξ + (1 / 2 : ℝ) * ‖ξ - x‖ ^ 2) = s * (E x - EStar) := by
  apply IsLeast.csInf_eq
  refine ⟨⟨x - s • g x, (hUN.interiorEnvelope_proximal_eq_iff hs x (x - s • g x)).mpr rfl⟩, ?_⟩
  rintro _ ⟨ξ, rfl⟩
  exact hUN.interiorEnvelope_proximal_lower hs x ξ

end IsUN

omit [CompleteSpace H] in
@[simp] theorem resolvent_zero (g : H → H) (x : H) :
    resolvent g 0 x = x := by
  simp only [resolvent, zero_smul, sub_zero]
  exact Function.leftInverse_invFun Function.injective_id x

omit [CompleteSpace H] in
@[simp] theorem interiorEnvelope_zero (E : H → ℝ) (g : H → H) (x : H) :
    interiorEnvelope E g 0 x = 0 := by
  simp [interiorEnvelope, envelopeObjective]

end UN
