module

public import UniformNondegeneracy.DAI.Transforms

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Normalizing descent–ascent inequalities

Subtracting the quadratic with curvature `Λ.center` and dividing by `Λ.radius` sends both scales to one. The two weights transform separately and coincide when the original DAI is balanced.
-/

noncomputable section

namespace UN.DAI

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Remove the quadratic with curvature `Λ.center` and divide by `Λ.radius`. -/
def normalizedEnergy (E : H → ℝ) (Λ : Scales) (x : H) : ℝ :=
  UN.quadraticShift E Λ.center 0 x / Λ.radius

/-- The two weights after centering the energy and normalizing its scales. -/
def normalizedWeights (Λ : Scales) (ρ : Weights) : Weights where
  plus := ρ.plus * Λ.minus / Λ.radius
  minus := ρ.minus * Λ.plus / Λ.radius
  plus_nonneg := div_nonneg (mul_nonneg ρ.plus_nonneg Λ.minus_pos.le) Λ.radius_pos.le
  minus_nonneg := div_nonneg (mul_nonneg ρ.minus_nonneg Λ.plus_pos.le) Λ.radius_pos.le

theorem normalizedWeights_product (Λ : Scales) (ρ : Weights) :
    (normalizedWeights Λ ρ).plus * (normalizedWeights Λ ρ).minus =
      ρ.plus * ρ.minus * (Λ.plus * Λ.minus / Λ.radius ^ 2) := by
  dsimp [normalizedWeights]
  ring

/-- The common coefficient of a normalized balanced DAI. -/
def normalizedWeight (Λ : Scales) (ρ : Weights) : ℝ :=
  (normalizedWeights Λ ρ).plus

theorem normalizedWeight_nonneg (Λ : Scales) (ρ : Weights) : 0 ≤ normalizedWeight Λ ρ :=
  (normalizedWeights Λ ρ).plus_nonneg

theorem normalizedWeight_eq (Λ : Scales) (ρ : Weights) (hBalanced : ρ.Balanced Λ) :
    normalizedWeight Λ ρ = ρ.minus * Λ.plus / Λ.radius := by
  dsimp [normalizedWeight, normalizedWeights]
  rw [hBalanced]

theorem normalizedWeights_eq_symmetric (Λ : Scales) (ρ : Weights) (hBalanced : ρ.Balanced Λ) :
    normalizedWeights Λ ρ = Weights.symmetric (normalizedWeight Λ ρ) (normalizedWeight_nonneg Λ ρ) := by
  dsimp [normalizedWeights, Weights.symmetric, normalizedWeight]
  congr 1
  exact (normalizedWeight_eq Λ ρ hBalanced).symm

theorem normalizedWeight_sq (Λ : Scales) (ρ : Weights) (hBalanced : ρ.Balanced Λ) :
    normalizedWeight Λ ρ ^ 2 = ρ.plus * ρ.minus * (Λ.plus * Λ.minus / Λ.radius ^ 2) := by
  have h := normalizedWeights_product Λ ρ
  simpa only [normalizedWeights_eq_symmetric Λ ρ hBalanced, Weights.symmetric, pow_two] using h

theorem hasGradientAt_normalizedEnergy {E : H → ℝ} {x : H}
    (hE : DifferentiableAt ℝ E x) (Λ : Scales) :
    HasGradientAt (normalizedEnergy E Λ) (Λ.radius⁻¹ • (gradient E x - Λ.center • x)) x := by
  have hShift := hasGradientAt_quadraticShift hE Λ.center (0 : H)
  convert hasGradientAt_const_mul hShift.differentiableAt Λ.radius⁻¹ using 1
  · ext y
    simp only [normalizedEnergy, div_eq_mul_inv]
    ring
  · rw [hShift.gradient]
    simp

theorem gradient_normalizedEnergy {E : H → ℝ} (hE : Differentiable ℝ E) (Λ : Scales) :
    gradient (normalizedEnergy E Λ) = fun x => Λ.radius⁻¹ • (gradient E x - Λ.center • x) :=
  gradient_eq fun x => hasGradientAt_normalizedEnergy (hE x) Λ

theorem bregman_normalized {E : H → ℝ} (hE : Differentiable ℝ E) (Λ : Scales) (x₁ x₂ : H) :
    bregman (normalizedEnergy E Λ) x₁ x₂ =
      (bregman E x₁ x₂ - Λ.center / 2 * ‖x₁ - x₂‖ ^ 2) / Λ.radius := by
  have hShift : Differentiable ℝ (UN.quadraticShift E Λ.center 0) :=
    fun x => (hasGradientAt_quadraticShift (hE x) Λ.center 0).differentiableAt
  have hEnergy : normalizedEnergy E Λ = fun x => Λ.radius⁻¹ * UN.quadraticShift E Λ.center 0 x := by
    funext x
    simp [normalizedEnergy, div_eq_mul_inv, mul_comm]
  rw [hEnergy, bregman_const_mul hShift, bregman_quadraticShift hE]
  ring

theorem phiPlus_normalized {E : H → ℝ} (hE : Differentiable ℝ E) (Λ : Scales) (x₁ x₂ : H) :
    phiPlus (normalizedEnergy E Λ) Scales.unit x₁ x₂ =
      Λ.plus / Λ.radius * phiPlus E Λ x₁ x₂ := by
  simp only [phiPlus, bregman_normalized hE, Scales.tauPlus, Scales.unit, div_one, one_mul]
  dsimp [Scales.radius, Scales.center, Scales.difference]
  field_simp [Λ.plus_pos.ne', (add_pos Λ.plus_pos Λ.minus_pos).ne']
  ring

theorem phiMinus_normalized {E : H → ℝ} (hE : Differentiable ℝ E) (Λ : Scales) (x₁ x₂ : H) :
    phiMinus (normalizedEnergy E Λ) Scales.unit x₁ x₂ =
      Λ.minus / Λ.radius * phiMinus E Λ x₁ x₂ := by
  simp only [phiMinus, bregman_normalized hE, Scales.tauMinus, Scales.unit, div_one, one_mul]
  dsimp [Scales.radius, Scales.center, Scales.difference]
  field_simp [Λ.minus_pos.ne', (add_pos Λ.plus_pos Λ.minus_pos).ne']
  ring

theorem descentStep_normalized {E : H → ℝ} (hE : Differentiable ℝ E) (Λ : Scales) (x : H) :
    descentStep (gradient (normalizedEnergy E Λ)) Scales.unit x = (Λ.plus / Λ.radius) • descentStep (gradient E) Λ x := by
  simp only [descentStep, gradientStep, Scales.tauPlus, Scales.unit, div_one,
    gradient_normalizedEnergy hE, smul_sub, smul_smul]
  have h₁ : Λ.plus / Λ.radius * (1 / Λ.plus) = Λ.radius⁻¹ := by field_simp [Λ.plus_pos.ne']
  have h₂ : 1 + Λ.radius⁻¹ * Λ.center = Λ.plus / Λ.radius := by
    dsimp [Scales.radius, Scales.center, Scales.difference]
    field_simp [(add_pos Λ.plus_pos Λ.minus_pos).ne']
    ring
  rw [h₁, ← h₂]
  module

theorem ascentStep_normalized {E : H → ℝ} (hE : Differentiable ℝ E) (Λ : Scales) (x : H) :
    ascentStep (gradient (normalizedEnergy E Λ)) Scales.unit x = (Λ.minus / Λ.radius) • ascentStep (gradient E) Λ x := by
  simp only [ascentStep, gradientStep, Scales.tauMinus, Scales.unit, div_one, neg_smul,
    gradient_normalizedEnergy hE, smul_sub, smul_add, smul_smul, sub_neg_eq_add]
  have h₁ : Λ.minus / Λ.radius * (1 / Λ.minus) = Λ.radius⁻¹ := by field_simp [Λ.minus_pos.ne']
  have h₂ : 1 - Λ.radius⁻¹ * Λ.center = Λ.minus / Λ.radius := by
    dsimp [Scales.radius, Scales.center, Scales.difference]
    field_simp [(add_pos Λ.plus_pos Λ.minus_pos).ne']
    ring
  rw [h₁, ← h₂]
  module

theorem step_inner_normalized {E : H → ℝ} (hE : Differentiable ℝ E) (Λ : Scales) (x y z : H) :
    ⟪descentStep (gradient (normalizedEnergy E Λ)) Scales.unit x - descentStep (gradient (normalizedEnergy E Λ)) Scales.unit y,
      ascentStep (gradient (normalizedEnergy E Λ)) Scales.unit x - ascentStep (gradient (normalizedEnergy E Λ)) Scales.unit z⟫ =
      Λ.plus * Λ.minus / Λ.radius ^ 2 * ⟪descentStep (gradient E) Λ x - descentStep (gradient E) Λ y, ascentStep (gradient E) Λ x - ascentStep (gradient E) Λ z⟫ := by
  rw [descentStep_normalized hE, descentStep_normalized hE, ascentStep_normalized hE, ascentStep_normalized hE]
  simp only [← smul_sub, real_inner_smul_left, real_inner_smul_right]
  ring

omit [CompleteSpace H] in
/-- At unit scales the two-point step product is the difference of squared norms. -/
theorem step_inner_unit (g : H → H) (x₁ x₂ : H) :
    ⟪descentStep g Scales.unit x₁ - descentStep g Scales.unit x₂,
      ascentStep g Scales.unit x₁ - ascentStep g Scales.unit x₂⟫ =
      ‖x₁ - x₂‖ ^ 2 - ‖g x₁ - g x₂‖ ^ 2 := by
  simp only [descentStep, ascentStep, gradientStep, Scales.unit, Scales.tauPlus, Scales.tauMinus,
    div_one, one_smul, neg_smul, sub_neg_eq_add]
  rw [show x₁ - g x₁ - (x₂ - g x₂) = (x₁ - x₂) - (g x₁ - g x₂) by abel,
    show x₁ + g x₁ - (x₂ + g x₂) = (x₁ - x₂) + (g x₁ - g x₂) by abel]
  have hIdentity (u v : H) : ⟪u - v, u + v⟫ = ‖u‖ ^ 2 - ‖v‖ ^ 2 := by
    simp only [inner_sub_left, inner_add_right, real_inner_self_eq_norm_sq, real_inner_comm u v]
    ring
  exact hIdentity (x₁ - x₂) (g x₁ - g x₂)

end UN.DAI

namespace UN.HasDAI

open DAI

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {E : H → ℝ} {Λ : Scales} {ρ : Weights}

/-- Centering and positive rescaling give a DAI with unit scales. -/
theorem normalized (hDAI : HasDAI Λ ρ E) :
    HasDAI Scales.unit (normalizedWeights Λ ρ) (normalizedEnergy E Λ) := by
  have hLower : -Λ.minus < Λ.center := by
    dsimp [Scales.center, Scales.difference]
    linarith [Λ.plus_pos, Λ.minus_pos]
  have hUpper : Λ.center < Λ.plus := by
    dsimp [Scales.center, Scales.difference]
    linarith [Λ.plus_pos, Λ.minus_pos]
  have hPlus : Λ.plus - Λ.center = Λ.radius := by
    dsimp [Scales.center, Scales.difference, Scales.radius]
    ring
  have hMinus : Λ.minus + Λ.center = Λ.radius := by
    dsimp [Scales.center, Scales.difference, Scales.radius]
    ring
  have hScales :
      (Λ.shift Λ.center hLower hUpper).scale Λ.radius⁻¹ (inv_pos.mpr Λ.radius_pos) = Scales.unit := by
    simp only [Scales.scale, Scales.shift, Scales.unit, hPlus, hMinus, inv_mul_cancel₀ Λ.radius_pos.ne']
  have hWeights : ρ.quadraticShift Λ Λ.center hLower hUpper = normalizedWeights Λ ρ := by
    simp only [Weights.quadraticShift, normalizedWeights, hPlus, hMinus]
  have hEnergy : (fun x => Λ.radius⁻¹ * UN.quadraticShift E Λ.center 0 x) = normalizedEnergy E Λ := by
    funext x
    simp [normalizedEnergy, div_eq_mul_inv, mul_comm]
  simpa only [hScales, hWeights, hEnergy] using
    (hDAI.quadraticShift Λ.center hLower hUpper 0).scale Λ.radius⁻¹ (inv_pos.mpr Λ.radius_pos)

/-- Balanced DAI normalizes to unit scales and equal weights. -/
theorem normalized_of_balanced (hDAI : HasDAI Λ ρ E) (hBalanced : ρ.Balanced Λ) :
    HasDAI Scales.unit (Weights.symmetric (normalizedWeight Λ ρ) (normalizedWeight_nonneg Λ ρ))
      (normalizedEnergy E Λ) := by
  simpa only [normalizedWeights_eq_symmetric Λ ρ hBalanced] using hDAI.normalized

end UN.HasDAI
