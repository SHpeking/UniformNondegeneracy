module

public import UniformNondegeneracy.Core.Basic
public import UniformNondegeneracy.Analysis.GradientBounds
public import UniformNondegeneracy.Geometry.GradientInverse

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Geometry of UN energies

UN gradients are bi-Lipschitz homeomorphisms with a unique zero. The secant inequalities also give quadratic Bregman bounds.
-/

noncomputable section

namespace UN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-!
## Inverse gradient and stationary point
-/

/-- A chosen inverse of the gradient map. -/
def inverseGradient (E : H → ℝ) : H → H :=
  Function.invFun (gradient E)

/-- The stationary point, obtained by inverting the zero vector. -/
def stationaryPoint (E : H → ℝ) : H :=
  inverseGradient E 0

/-- The stationary energy value. -/
def stationaryValue (E : H → ℝ) : ℝ :=
  E (stationaryPoint E)

variable {bounds : CurvatureBounds} {E : H → ℝ}

local notation "g" => gradient E

local notation "L₊" => bounds.lPlus
local notation "L₋" => bounds.lMinus
local notation "D" => bregman E
local notation "xStar" => stationaryPoint E
local notation "EStar" => stationaryValue E

/-!
## Centered forms of the secant inequalities
-/

/-- Centered norm form of the inner secant inequality. -/
theorem IsUN.inner_centered (hUN : IsUN bounds E) (x₁ x₂ : H) :
    bounds.innerRadius * ‖x₁ - x₂‖ ≤ ‖g x₁ - g x₂ - bounds.innerCenter • (x₁ - x₂)‖ := by
  have hs := hUN.inner_secant x₁ x₂
  rw [← centered_secant_identity] at hs
  change 0 ≤ ‖g x₁ - g x₂ - bounds.innerCenter • (x₁ - x₂)‖ ^ 2 - bounds.innerRadius ^ 2 * ‖x₁ - x₂‖ ^ 2 at hs
  nlinarith [norm_nonneg (g x₁ - g x₂ - bounds.innerCenter • (x₁ - x₂))]

/-- Centered norm form of the outer secant inequality. -/
theorem IsUN.outer_centered (hUN : IsUN bounds E) (x₁ x₂ : H) :
    ‖g x₁ - g x₂ - bounds.outerCenter • (x₁ - x₂)‖ ≤ bounds.outerRadius * ‖x₁ - x₂‖ := by
  have hs := hUN.outer_secant x₁ x₂
  rw [← centered_secant_identity] at hs
  change ‖g x₁ - g x₂ - bounds.outerCenter • (x₁ - x₂)‖ ^ 2 - bounds.outerRadius ^ 2 * ‖x₁ - x₂‖ ^ 2 ≤ 0 at hs
  have hr : 0 ≤ bounds.outerRadius := by
    unfold CurvatureBounds.outerRadius
    linarith [bounds.lPlus_pos, bounds.lMinus_pos]
  have hn := mul_nonneg hr (norm_nonneg (x₁ - x₂))
  nlinarith

/-- Squared inner centered secant inequality. -/
theorem IsUN.inner_centered_sq (hUN : IsUN bounds E) (x₁ x₂ : H) :
    bounds.innerRadius ^ 2 * ‖x₁ - x₂‖ ^ 2 ≤ ‖g x₁ - g x₂ - bounds.innerCenter • (x₁ - x₂)‖ ^ 2 := by
  have h := hUN.inner_centered x₁ x₂
  have hr : 0 ≤ bounds.innerRadius := by
    unfold CurvatureBounds.innerRadius
    linarith [bounds.muPlus_pos, bounds.muMinus_pos]
  have hn := mul_nonneg hr (norm_nonneg (x₁ - x₂))
  nlinarith

/-- Squared outer centered secant inequality. -/
theorem IsUN.outer_centered_sq (hUN : IsUN bounds E) (x₁ x₂ : H) :
    ‖g x₁ - g x₂ - bounds.outerCenter • (x₁ - x₂)‖ ^ 2 ≤ bounds.outerRadius ^ 2 * ‖x₁ - x₂‖ ^ 2 := by
  have h := hUN.outer_centered x₁ x₂
  have hn := norm_nonneg (g x₁ - g x₂ - bounds.outerCenter • (x₁ - x₂))
  nlinarith

/-- The inner secant gives the global lower norm bound, with `muMin = min muPlus muMinus`. -/
theorem IsUN.gradient_lower_bound (hUN : IsUN bounds E) (x₁ x₂ : H) :
    bounds.muMin * ‖x₁ - x₂‖ ≤ ‖g x₁ - g x₂‖ := by
  have h := hUN.inner_centered x₁ x₂
  have ht := norm_sub_le (g x₁ - g x₂) (bounds.innerCenter • (x₁ - x₂))
  rw [norm_smul, Real.norm_eq_abs] at ht
  rw [← bounds.innerRadius_sub_abs_innerCenter]
  nlinarith

/-- The outer secant gives the global Lipschitz norm bound, with `lMax = max lPlus lMinus`. -/
theorem IsUN.gradient_upper_bound (hUN : IsUN bounds E) (x₁ x₂ : H) :
    ‖g x₁ - g x₂‖ ≤ bounds.lMax * ‖x₁ - x₂‖ :=
  norm_le_of_outer_secant _ _ bounds.lPlus_pos.le bounds.lMinus_pos.le (hUN.outer_secant x₁ x₂)

/-- The asymmetric outer curvatures bound the directional secant. -/
theorem IsUN.directional_secant_bounds (hUN : IsUN bounds E) (x₁ x₂ : H) :
    -L₋ * ‖x₁ - x₂‖ ^ 2 ≤ ⟪g x₁ - g x₂, x₁ - x₂⟫ ∧
    ⟪g x₁ - g x₂, x₁ - x₂⟫ ≤ L₊ * ‖x₁ - x₂‖ ^ 2 := by
  have h := hUN.outer_centered x₁ x₂
  have ha := abs_real_inner_le_norm (g x₁ - g x₂ - bounds.outerCenter • (x₁ - x₂)) (x₁ - x₂)
  have ht := mul_le_mul_of_nonneg_right h (norm_nonneg (x₁ - x₂))
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at ha
  have hh := abs_le.mp (ha.trans ht)
  unfold CurvatureBounds.outerCenter CurvatureBounds.outerRadius at hh
  constructor <;> nlinarith [hh.1, hh.2]

/-!
## Global invertibility
-/

theorem IsUN.gradient_lipschitz (hUN : IsUN bounds E) :
    LipschitzWith ⟨bounds.lMax, bounds.lMax_pos.le⟩ g :=
  lipschitzWith_iff_norm_sub_le.mpr hUN.gradient_upper_bound

theorem IsUN.gradient_antilipschitz (hUN : IsUN bounds E) :
    AntilipschitzWith ⟨bounds.muMin⁻¹, inv_nonneg.mpr bounds.muMin_pos.le⟩ g := by
  apply antilipschitzWith_iff_le_mul_dist.mpr
  intro x₁ x₂
  simp only [dist_eq_norm]
  change ‖x₁ - x₂‖ ≤ bounds.muMin⁻¹ * ‖g x₁ - g x₂‖
  rw [inv_mul_eq_div, le_div_iff₀ bounds.muMin_pos]
  simpa only [mul_comm] using hUN.gradient_lower_bound x₁ x₂

theorem IsUN.gradient_continuous (hUN : IsUN bounds E) :
    Continuous g :=
  hUN.gradient_lipschitz.continuous

theorem IsUN.gradient_injective (hUN : IsUN bounds E) :
    Function.Injective g :=
  hUN.gradient_antilipschitz.injective

theorem IsUN.gradient_surjective (hUN : IsUN bounds E) :
    Function.Surjective g := by
  apply GradientMap.surjective_of_bilipschitz E g bounds.muMin bounds.lMax
  · exact hUN.hasGradientAt
  · exact bounds.muMin_pos
  · exact hUN.gradient_lower_bound
  · exact hUN.gradient_upper_bound

theorem IsUN.gradient_bijective (hUN : IsUN bounds E) :
    Function.Bijective g := by
  exact ⟨hUN.gradient_injective, hUN.gradient_surjective⟩

theorem IsUN.gradient_inverseGradient (hUN : IsUN bounds E) (p : H) :
    g (inverseGradient E p) = p := by
  exact Function.rightInverse_invFun hUN.gradient_surjective p

theorem IsUN.inverseGradient_gradient (hUN : IsUN bounds E) (x : H) :
    inverseGradient E (g x) = x := by
  exact Function.leftInverse_invFun hUN.gradient_injective x

/-- The inverse has norm Lipschitz bound `1 / muMin`. -/
theorem IsUN.inverseGradient_bound (hUN : IsUN bounds E) (p₁ p₂ : H) :
    ‖inverseGradient E p₁ - inverseGradient E p₂‖ ≤ bounds.muMin⁻¹ * ‖p₁ - p₂‖ := by
  apply GradientMap.inverse_norm_sub_le g (inverseGradient E) bounds.muMin
  · exact bounds.muMin_pos
  · exact hUN.gradient_lower_bound
  · exact hUN.gradient_inverseGradient

theorem IsUN.inverseGradient_lipschitz (hUN : IsUN bounds E) :
    LipschitzWith ⟨bounds.muMin⁻¹, inv_nonneg.mpr bounds.muMin_pos.le⟩ (inverseGradient E) :=
  lipschitzWith_iff_norm_sub_le.mpr hUN.inverseGradient_bound

theorem IsUN.inverseGradient_continuous (hUN : IsUN bounds E) :
    Continuous (inverseGradient E) :=
  hUN.inverseGradient_lipschitz.continuous

/-- The gradient as a homeomorphism of `H`. -/
def IsUN.gradientHomeomorph (hUN : IsUN bounds E) : H ≃ₜ H where
  toEquiv :=
    { toFun := g
      invFun := inverseGradient E
      left_inv := hUN.inverseGradient_gradient
      right_inv := hUN.gradient_inverseGradient }
  continuous_toFun := hUN.gradient_continuous
  continuous_invFun := hUN.inverseGradient_continuous

theorem IsUN.gradientHomeomorph_apply (hUN : IsUN bounds E) (x : H) :
    hUN.gradientHomeomorph x = g x := by
  rfl

theorem IsUN.gradientHomeomorph_symm_apply (hUN : IsUN bounds E) (p : H) :
    hUN.gradientHomeomorph.symm p = inverseGradient E p := by
  rfl

/-!
## The unique stationary point
-/

theorem IsUN.gradient_stationaryPoint (hUN : IsUN bounds E) :
    g xStar = 0 := by
  exact hUN.gradient_inverseGradient 0

theorem IsUN.gradient_eq_zero_iff (hUN : IsUN bounds E) (x : H) :
    g x = 0 ↔ x = xStar := by
  constructor
  · intro h
    exact hUN.gradient_injective (h.trans hUN.gradient_stationaryPoint.symm)
  · rintro rfl
    exact hUN.gradient_stationaryPoint

/-- Existence and uniqueness of a zero of the gradient. -/
theorem IsUN.unique_stationaryPoint (hUN : IsUN bounds E) :
    ∃! x, g x = 0 := by
  exact ⟨xStar, hUN.gradient_stationaryPoint,
    fun x h => (hUN.gradient_eq_zero_iff x).mp h⟩

/-!
## Basic Bregman identities and one-sided bounds
-/

theorem IsUN.bregman_stationaryPoint (hUN : IsUN bounds E) (x : H) :
    D x xStar = E x - EStar := by
  simp [bregman, stationaryValue, hUN.gradient_stationaryPoint]

/-- The negative outer curvature gives the lower quadratic Bregman bound. -/
theorem IsUN.bregman_lower (hUN : IsUN bounds E) (x₁ x₂ : H) :
    -(L₋ / 2) * ‖x₁ - x₂‖ ^ 2 ≤ D x₁ x₂ := by
  have h := GradientMap.taylor_lower_bound_of_inner E g (-L₋)
    hUN.hasGradientAt (fun x₁ x₂ => (hUN.directional_secant_bounds x₁ x₂).1) x₂ (x₁ - x₂)
  simpa only [add_sub_cancel, bregman, neg_div] using h

/-- The positive outer curvature gives the upper quadratic Bregman bound. -/
theorem IsUN.bregman_upper (hUN : IsUN bounds E) (x₁ x₂ : H) :
    D x₁ x₂ ≤ (L₊ / 2) * ‖x₁ - x₂‖ ^ 2 := by
  have h := GradientMap.taylor_upper_bound_of_inner E g L₊
    hUN.hasGradientAt (fun x₁ x₂ => (hUN.directional_secant_bounds x₁ x₂).2) x₂ (x₁ - x₂)
  simpa only [add_sub_cancel, bregman] using h

theorem IsUN.bregman_bounds (hUN : IsUN bounds E) (x₁ x₂ : H) :
    -(L₋ / 2) * ‖x₁ - x₂‖ ^ 2 ≤ D x₁ x₂ ∧
    D x₁ x₂ ≤ L₊ / 2 * ‖x₁ - x₂‖ ^ 2 := by
  exact ⟨hUN.bregman_lower x₁ x₂, hUN.bregman_upper x₁ x₂⟩

theorem IsUN.hasBregmanBounds (hUN : IsUN bounds E) :
    HasBregmanBounds L₊ L₋ E :=
  ⟨hUN.bregman_lower, hUN.bregman_upper⟩

end UN
