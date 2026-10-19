module

public import UniformNondegeneracy.DAI.Basic

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Centering and rescaling a balanced DAI

Subtracting the quadratic with curvature `Λ.center` and dividing by `Λ.radius` sends the scales to one. Balanced weights become a common scalar coefficient.
-/

noncomputable section

namespace UN.DAI

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Remove the quadratic with curvature `Λ.center` and divide by `Λ.radius`. -/
def normalizedEnergy (E : H → ℝ) (Λ : Scales) (x : H) : ℝ :=
  (E x - Λ.center / 2 * ‖x‖ ^ 2) / Λ.radius

/-- Center and rescale the field in the same way as the energy. -/
def normalizedGradient (g : H → H) (Λ : Scales) (x : H) : H :=
  Λ.radius⁻¹ • (g x - Λ.center • x)

/-- The common coefficient after normalizing a balanced DAI. -/
def normalizedWeight (Λ : Scales) (ρ : Weights) : ℝ :=
  ρ.plus * Λ.minus / Λ.radius

theorem normalizedWeight_nonneg (Λ : Scales) (ρ : Weights) : 0 ≤ normalizedWeight Λ ρ :=
  div_nonneg (mul_nonneg ρ.plus_nonneg Λ.minus_pos.le) Λ.radius_pos.le

theorem normalizedWeight_eq (Λ : Scales) (ρ : Weights) (hBalanced : ρ.Balanced Λ) :
    normalizedWeight Λ ρ = ρ.minus * Λ.plus / Λ.radius := by
  unfold normalizedWeight
  rw [hBalanced]

theorem normalizedWeight_sq (Λ : Scales) (ρ : Weights) (hBalanced : ρ.Balanced Λ) :
    normalizedWeight Λ ρ ^ 2 = ρ.plus * ρ.minus * (Λ.plus * Λ.minus / Λ.radius ^ 2) := by
  rw [pow_two]
  nth_rw 1 [normalizedWeight_eq Λ ρ hBalanced]
  unfold normalizedWeight
  ring

theorem bregman_normalized (E : H → ℝ) (g : H → H) (Λ : Scales) (x₁ x₂ : H) :
    bregman (normalizedEnergy E Λ) (normalizedGradient g Λ) x₁ x₂ =
      (bregman E g x₁ x₂ - Λ.center / 2 * ‖x₁ - x₂‖ ^ 2) / Λ.radius := by
  simp only [bregman, normalizedEnergy, normalizedGradient, real_inner_smul_left, inner_sub_left, inner_sub_right,
    real_inner_self_eq_norm_sq, norm_sub_sq_real, real_inner_comm x₁ x₂]
  ring

theorem hasGradientAt_normalizedEnergy [CompleteSpace H] {E : H → ℝ} {g : H → H}
    (hGrad : ∀ x, HasGradientAt E (g x) x) (Λ : Scales) (x : H) :
    HasGradientAt (normalizedEnergy E Λ) (normalizedGradient g Λ x) x := by
  have hQuad : HasGradientAt (fun x : H => Λ.center / 2 * ‖x‖ ^ 2) (Λ.center • x) x := by
    simpa using hasGradientAt_quadratic Λ.center 0 x
  rw [hasGradientAt_iff_hasFDerivAt]
  convert ((hGrad x).hasFDerivAt.sub hQuad.hasFDerivAt).const_mul Λ.radius⁻¹ using 1
  · ext x
    simp [normalizedEnergy, div_eq_mul_inv, mul_comm]
  · ext v
    simp [normalizedGradient, InnerProductSpace.toDual]

theorem phiPlus_normalized (E : H → ℝ) (g : H → H) (Λ : Scales) (x₁ x₂ : H) :
    phiPlus (normalizedEnergy E Λ) (normalizedGradient g Λ) Scales.unit x₁ x₂ =
      Λ.plus / Λ.radius * phiPlus E g Λ x₁ x₂ := by
  simp only [phiPlus, bregman_normalized, Scales.tauPlus, Scales.unit, div_one, one_mul]
  dsimp [Scales.radius, Scales.center, Scales.difference]
  field_simp [Λ.plus_pos.ne', (add_pos Λ.plus_pos Λ.minus_pos).ne']
  ring

theorem phiMinus_normalized (E : H → ℝ) (g : H → H) (Λ : Scales) (x₁ x₂ : H) :
    phiMinus (normalizedEnergy E Λ) (normalizedGradient g Λ) Scales.unit x₁ x₂ =
      Λ.minus / Λ.radius * phiMinus E g Λ x₁ x₂ := by
  simp only [phiMinus, bregman_normalized, Scales.tauMinus, Scales.unit, div_one, one_mul]
  dsimp [Scales.radius, Scales.center, Scales.difference]
  field_simp [Λ.minus_pos.ne', (add_pos Λ.plus_pos Λ.minus_pos).ne']
  ring

theorem descentStep_normalized (g : H → H) (Λ : Scales) (x : H) :
    descentStep (normalizedGradient g Λ) Scales.unit x = (Λ.plus / Λ.radius) • descentStep g Λ x := by
  simp only [descentStep, gradientStep, Scales.tauPlus, Scales.unit, div_one,
    normalizedGradient, smul_sub, smul_smul]
  have h₁ : Λ.plus / Λ.radius * (1 / Λ.plus) = Λ.radius⁻¹ := by field_simp [Λ.plus_pos.ne']
  have h₂ : 1 + Λ.radius⁻¹ * Λ.center = Λ.plus / Λ.radius := by
    dsimp [Scales.radius, Scales.center, Scales.difference]
    field_simp [(add_pos Λ.plus_pos Λ.minus_pos).ne']
    ring
  rw [h₁, ← h₂]
  module

theorem ascentStep_normalized (g : H → H) (Λ : Scales) (x : H) :
    ascentStep (normalizedGradient g Λ) Scales.unit x = (Λ.minus / Λ.radius) • ascentStep g Λ x := by
  simp only [ascentStep, gradientStep, Scales.tauMinus, Scales.unit, div_one, neg_smul,
    normalizedGradient, smul_sub, smul_add, smul_smul, sub_neg_eq_add]
  have h₁ : Λ.minus / Λ.radius * (1 / Λ.minus) = Λ.radius⁻¹ := by field_simp [Λ.minus_pos.ne']
  have h₂ : 1 - Λ.radius⁻¹ * Λ.center = Λ.minus / Λ.radius := by
    dsimp [Scales.radius, Scales.center, Scales.difference]
    field_simp [(add_pos Λ.plus_pos Λ.minus_pos).ne']
    ring
  rw [h₁, ← h₂]
  module

theorem step_inner_normalized (g : H → H) (Λ : Scales) (x y z : H) :
    ⟪descentStep (normalizedGradient g Λ) Scales.unit x - descentStep (normalizedGradient g Λ) Scales.unit y,
      ascentStep (normalizedGradient g Λ) Scales.unit x - ascentStep (normalizedGradient g Λ) Scales.unit z⟫ =
      Λ.plus * Λ.minus / Λ.radius ^ 2 * ⟪descentStep g Λ x - descentStep g Λ y, ascentStep g Λ x - ascentStep g Λ z⟫ := by
  rw [descentStep_normalized, descentStep_normalized, ascentStep_normalized, ascentStep_normalized]
  simp only [← smul_sub, real_inner_smul_left, real_inner_smul_right]
  ring

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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {E : H → ℝ} {g : H → H} {Λ : Scales} {ρ : Weights}

/-- A balanced DAI becomes a DAI with unit scales and equal weights. -/
theorem normalized (hDAI : HasDAI E g Λ ρ) (hBalanced : ρ.Balanced Λ) :
    HasDAI (normalizedEnergy E Λ) (normalizedGradient g Λ) Scales.unit
      (Weights.symmetric (normalizedWeight Λ ρ) (normalizedWeight_nonneg Λ ρ)) := by
  intro x y z
  rw [step_inner_normalized, phiPlus_normalized, phiMinus_normalized]
  have h := mul_le_mul_of_nonneg_left (hDAI x y z)
    (div_nonneg (mul_nonneg Λ.plus_pos.le Λ.minus_pos.le) (sq_nonneg Λ.radius))
  have hPlus : normalizedWeight Λ ρ * (Λ.plus / Λ.radius) = Λ.plus * Λ.minus / Λ.radius ^ 2 * ρ.plus := by
    unfold normalizedWeight
    ring
  have hMinus : normalizedWeight Λ ρ * (Λ.minus / Λ.radius) = Λ.plus * Λ.minus / Λ.radius ^ 2 * ρ.minus := by
    rw [normalizedWeight_eq Λ ρ hBalanced]
    ring
  dsimp only [Weights.symmetric]
  rw [← mul_assoc (normalizedWeight Λ ρ) (Λ.plus / Λ.radius), hPlus,
    ← mul_assoc (normalizedWeight Λ ρ) (Λ.minus / Λ.radius), hMinus]
  simpa only [mul_add, mul_assoc] using h

end UN.HasDAI
