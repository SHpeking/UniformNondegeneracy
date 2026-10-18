module

public import UniformNondegeneracy.Core.Basic
public import UniformNondegeneracy.Analysis.Bregman
public import UniformNondegeneracy.Geometry.GradientInverse

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Consequences of the UN secant assumptions

The data defined here depend on the energy and gradient, not on a chosen curvature certificate. Theorems in the `IsUN` namespace supply their intended geometric interpretation under the UN hypotheses.

In particular, bijectivity is a consequence of the secants and the gradient identity, obtained from `GradientMap.surjective_of_bounds`. No surjectivity or homeomorphism assumption is added to `IsUN`.
-/

noncomputable section

namespace UN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-!
## Constructions independent of curvature certificates
-/

/-- A chosen inverse of the gradient map. This is a total definition for any map; its inverse identities are proved below under `IsUN`. -/
def inverseGradient (g : H → H) : H → H :=
  Function.invFun g

/-- The distinguished stationary point, obtained by inverting the zero vector. The UN assumptions establish that this point is the unique zero of `g`. -/
def stationaryPoint (g : H → H) : H :=
  inverseGradient g 0

/-- The energy at the distinguished stationary point. -/
def stationaryValue (E : H → ℝ) (g : H → H) : ℝ :=
  E (stationaryPoint g)

variable {bounds : CurvatureBounds} {E : H → ℝ} {g : H → H}

local notation "L₊" => bounds.lPlus
local notation "L₋" => bounds.lMinus
local notation "D" => bregman E g
local notation "xStar" => stationaryPoint g
local notation "EStar" => stationaryValue E g

omit [CompleteSpace H] in
/-- Completing the square in a two-sided secant expression. -/
theorem centered_secant_identity (u v : H) (a b : ℝ) :
    ‖u - ((a - b) / 2) • v‖ ^ 2 - ((a + b) / 2) ^ 2 * ‖v‖ ^ 2 = ⟪u + b • v, u - a • v⟫ := by
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_sub_right, inner_add_left, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm v u]
  ring

/-!
## Centered forms of the secant inequalities
-/

/-- Centered norm form of the inner secant inequality. Expand the squared norm, use `IsUN.inner_secant`, and take nonnegative square roots. -/
theorem IsUN.inner_centered (hUN : IsUN bounds E g) (x₁ x₂ : H) :
    bounds.innerRadius * ‖x₁ - x₂‖ ≤ ‖g x₁ - g x₂ - bounds.innerCenter • (x₁ - x₂)‖ := by
  have hs := hUN.inner_secant x₁ x₂
  rw [← centered_secant_identity] at hs
  change 0 ≤ ‖g x₁ - g x₂ - bounds.innerCenter • (x₁ - x₂)‖ ^ 2 - bounds.innerRadius ^ 2 * ‖x₁ - x₂‖ ^ 2 at hs
  nlinarith [norm_nonneg (g x₁ - g x₂ - bounds.innerCenter • (x₁ - x₂))]

/-- Centered norm form of the outer secant inequality. -/
theorem IsUN.outer_centered (hUN : IsUN bounds E g) (x₁ x₂ : H) :
    ‖g x₁ - g x₂ - bounds.outerCenter • (x₁ - x₂)‖ ≤ bounds.outerRadius * ‖x₁ - x₂‖ := by
  have hs := hUN.outer_secant x₁ x₂
  rw [← centered_secant_identity] at hs
  change ‖g x₁ - g x₂ - bounds.outerCenter • (x₁ - x₂)‖ ^ 2 - bounds.outerRadius ^ 2 * ‖x₁ - x₂‖ ^ 2 ≤ 0 at hs
  have hr : 0 ≤ bounds.outerRadius := by
    unfold CurvatureBounds.outerRadius
    linarith [bounds.lPlus_pos, bounds.lMinus_pos]
  have hn := mul_nonneg hr (norm_nonneg (x₁ - x₂))
  nlinarith

/-- Squared form, convenient for the later refined secant and envelope algebra. -/
theorem IsUN.inner_centered_sq (hUN : IsUN bounds E g) (x₁ x₂ : H) :
    bounds.innerRadius ^ 2 * ‖x₁ - x₂‖ ^ 2 ≤ ‖g x₁ - g x₂ - bounds.innerCenter • (x₁ - x₂)‖ ^ 2 := by
  have h := hUN.inner_centered x₁ x₂
  have hr : 0 ≤ bounds.innerRadius := by
    unfold CurvatureBounds.innerRadius
    linarith [bounds.muPlus_pos, bounds.muMinus_pos]
  have hn := mul_nonneg hr (norm_nonneg (x₁ - x₂))
  nlinarith

/-- Squared outer centered secant inequality. -/
theorem IsUN.outer_centered_sq (hUN : IsUN bounds E g) (x₁ x₂ : H) :
    ‖g x₁ - g x₂ - bounds.outerCenter • (x₁ - x₂)‖ ^ 2 ≤ bounds.outerRadius ^ 2 * ‖x₁ - x₂‖ ^ 2 := by
  have h := hUN.outer_centered x₁ x₂
  have hn := norm_nonneg (g x₁ - g x₂ - bounds.outerCenter • (x₁ - x₂))
  nlinarith

/-- The inner secant gives the global lower norm bound, with `muMin = min muPlus muMinus`. -/
theorem IsUN.lower_norm_sub_le (hUN : IsUN bounds E g) (x₁ x₂ : H) :
    bounds.muMin * ‖x₁ - x₂‖ ≤ ‖g x₁ - g x₂‖ := by
  have h := hUN.inner_centered x₁ x₂
  have ht := norm_sub_le (g x₁ - g x₂) (bounds.innerCenter • (x₁ - x₂))
  rw [norm_smul, Real.norm_eq_abs] at ht
  rw [← bounds.innerRadius_sub_abs_innerCenter]
  nlinarith

/-- The outer secant gives the global Lipschitz norm bound, with `lMax = max lPlus lMinus`. -/
theorem IsUN.norm_sub_le_upper (hUN : IsUN bounds E g) (x₁ x₂ : H) :
    ‖g x₁ - g x₂‖ ≤ bounds.lMax * ‖x₁ - x₂‖ := by
  have h := hUN.outer_centered x₁ x₂
  have ht := norm_add_le (g x₁ - g x₂ - bounds.outerCenter • (x₁ - x₂)) (bounds.outerCenter • (x₁ - x₂))
  rw [sub_add_cancel, norm_smul, Real.norm_eq_abs] at ht
  rw [← bounds.outerRadius_add_abs_outerCenter]
  nlinarith

/-- The asymmetric outer curvatures bound the directional secant. -/
theorem IsUN.outer_inner_bounds (hUN : IsUN bounds E g) (x₁ x₂ : H) :
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

/-- Continuity follows from the upper norm bound. -/
theorem IsUN.gradient_continuous (hUN : IsUN bounds E g) :
    Continuous g := by
  have hLip : LipschitzWith ⟨bounds.lMax, le_of_lt bounds.lMax_pos⟩ g := by
    apply LipschitzWith.of_dist_le_mul
    intro x₁ x₂
    simp only [dist_eq_norm]
    exact_mod_cast hUN.norm_sub_le_upper x₁ x₂
  exact hLip.continuous

/-- Injectivity follows from the positive lower norm bound. -/
theorem IsUN.gradient_injective (hUN : IsUN bounds E g) :
    Function.Injective g := by
  apply GradientMap.injective_of_lower_bound g bounds.muMin
  · -- Positivity of the minimum of the two positive inner bounds.
    exact bounds.muMin_pos
  · exact hUN.lower_norm_sub_le

/-- The only global inversion input is the independent Hilbert-space theorem for gradients with two-sided Lipschitz bounds. The remaining scalar side goals follow from the positivity and ordering fields of `CurvatureBounds`. -/
theorem IsUN.gradient_surjective (hUN : IsUN bounds E g) :
    Function.Surjective g := by
  apply GradientMap.surjective_of_bounds E g bounds.muMin bounds.lMax
  · exact hUN.has_gradient
  · -- `0 < min muPlus muMinus`.
    exact bounds.muMin_pos
  · -- `min muPlus muMinus ≤ max lPlus lMinus`.
    exact bounds.muMin_le_lMax
  · exact hUN.lower_norm_sub_le
  · exact hUN.norm_sub_le_upper

/-- The gradient is globally bijective under the secant-only UN assumptions. -/
theorem IsUN.gradient_bijective (hUN : IsUN bounds E g) :
    Function.Bijective g := by
  exact ⟨hUN.gradient_injective, hUN.gradient_surjective⟩

/-- Applying the gradient after its chosen inverse gives the target. -/
theorem IsUN.gradient_inverseGradient (hUN : IsUN bounds E g) (p : H) :
    g (inverseGradient g p) = p := by
  exact Function.rightInverse_invFun hUN.gradient_surjective p

/-- Applying the chosen inverse after the gradient gives the original point. -/
theorem IsUN.inverseGradient_gradient (hUN : IsUN bounds E g) (x : H) :
    inverseGradient g (g x) = x := by
  exact Function.leftInverse_invFun hUN.gradient_injective x

/-- The inverse has norm Lipschitz bound `1 / muMin`. -/
theorem IsUN.inverse_norm_sub_le (hUN : IsUN bounds E g) (p₁ p₂ : H) :
    ‖inverseGradient g p₁ - inverseGradient g p₂‖ ≤ bounds.muMin⁻¹ * ‖p₁ - p₂‖ := by
  apply GradientMap.inverse_norm_sub_le g (inverseGradient g) bounds.muMin
  · exact bounds.muMin_pos
  · exact hUN.lower_norm_sub_le
  · exact hUN.gradient_inverseGradient

/-- Continuity of the inverse follows from its reciprocal norm bound. -/
theorem IsUN.inverseGradient_continuous (hUN : IsUN bounds E g) :
    Continuous (inverseGradient g) := by
  have hLip : LipschitzWith ⟨bounds.muMin⁻¹, inv_nonneg.mpr (le_of_lt bounds.muMin_pos)⟩ (inverseGradient g) := by
    apply LipschitzWith.of_dist_le_mul
    intro x₁ x₂
    simp only [dist_eq_norm]
    exact_mod_cast hUN.inverse_norm_sub_le x₁ x₂
  exact hLip.continuous

/-- The gradient, now equipped with its proved continuous inverse. This is an actual structure construction; all mathematical properties are theorem fields. -/
def IsUN.gradientHomeomorph (hUN : IsUN bounds E g) : H ≃ₜ H where
  toEquiv :=
    { toFun := g
      invFun := inverseGradient g
      left_inv := hUN.inverseGradient_gradient
      right_inv := hUN.gradient_inverseGradient }
  continuous_toFun := hUN.gradient_continuous
  continuous_invFun := hUN.inverseGradient_continuous

/-- The bundled homeomorphism has exactly the supplied gradient as its map. -/
theorem IsUN.gradientHomeomorph_apply (hUN : IsUN bounds E g) (x : H) :
    hUN.gradientHomeomorph x = g x := by
  rfl

/-- The inverse of the bundled homeomorphism is the certificate-independent chosen inverse. -/
theorem IsUN.gradientHomeomorph_symm_apply (hUN : IsUN bounds E g) (p : H) :
    hUN.gradientHomeomorph.symm p = inverseGradient g p := by
  rfl

/-!
## The unique stationary point
-/

/-- The distinguished point is stationary. -/
theorem IsUN.gradient_stationaryPoint (hUN : IsUN bounds E g) :
    g xStar = 0 := by
  exact hUN.gradient_inverseGradient 0

/-- Every stationary point is the distinguished stationary point. -/
theorem IsUN.gradient_eq_zero_iff (hUN : IsUN bounds E g) (x : H) :
    g x = 0 ↔ x = xStar := by
  constructor
  · intro h
    exact hUN.gradient_injective (h.trans hUN.gradient_stationaryPoint.symm)
  · rintro rfl
    exact hUN.gradient_stationaryPoint

/-- Existence and uniqueness of a zero of the gradient. -/
theorem IsUN.unique_stationaryPoint (hUN : IsUN bounds E g) :
    ∃! x, g x = 0 := by
  exact ⟨xStar, hUN.gradient_stationaryPoint,
    fun x h => (hUN.gradient_eq_zero_iff x).mp h⟩

/-!
## Basic Bregman identities and one-sided bounds
-/

/-- At the stationary point, the Bregman difference is the energy difference. -/
theorem IsUN.bregman_stationaryPoint (hUN : IsUN bounds E g) (x : H) :
    D x xStar = E x - EStar := by
  simp [bregman, stationaryValue, hUN.gradient_stationaryPoint]

/-- The negative-side outer bound gives the lower quadratic Bregman estimate. This uses the one-sided directional consequence of the outer secant and integration along a segment; it retains the asymmetric constant `lMinus`. -/
theorem IsUN.bregman_lower (hUN : IsUN bounds E g) (x₁ x₂ : H) :
    -(L₋ / 2) * ‖x₁ - x₂‖ ^ 2 ≤ D x₁ x₂ := by
  have h := GradientMap.taylor_lower_bound_of_inner E g (-L₋)
    hUN.has_gradient (fun x₁ x₂ => (hUN.outer_inner_bounds x₁ x₂).1) x₂ (x₁ - x₂)
  simpa only [add_sub_cancel, bregman, neg_div] using h

/-- The positive-side outer bound gives the upper quadratic Bregman estimate. -/
theorem IsUN.bregman_upper (hUN : IsUN bounds E g) (x₁ x₂ : H) :
    D x₁ x₂ ≤ (L₊ / 2) * ‖x₁ - x₂‖ ^ 2 := by
  have h := GradientMap.taylor_upper_bound_of_inner E g L₊
    hUN.has_gradient (fun x₁ x₂ => (hUN.outer_inner_bounds x₁ x₂).2) x₂ (x₁ - x₂)
  simpa only [add_sub_cancel, bregman] using h

theorem IsUN.bregman_bounds (hUN : IsUN bounds E g) (x₁ x₂ : H) :
    -(L₋ / 2) * ‖x₁ - x₂‖ ^ 2 ≤ D x₁ x₂ ∧
    D x₁ x₂ ≤ L₊ / 2 * ‖x₁ - x₂‖ ^ 2 := by
  exact ⟨hUN.bregman_lower x₁ x₂, hUN.bregman_upper x₁ x₂⟩

/-- The intrinsic outer curvatures give a general quadratic Bregman certificate. -/
theorem IsUN.hasBregmanBounds (hUN : IsUN bounds E g) :
    HasBregmanBounds E g L₊ L₋ :=
  ⟨hUN.bregman_lower, hUN.bregman_upper⟩

end UN
