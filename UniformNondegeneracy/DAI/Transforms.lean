module

public import UniformNondegeneracy.Analysis.EnergyTransforms
public import UniformNondegeneracy.DAI.Basic

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Transformations preserving DAI

Quadratic shifts change the scales and weights. Positive energy scaling changes the scales and preserves the weights.
-/

noncomputable section

namespace UN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {E : H → ℝ} {Λ : DAI.Scales} {ρ : DAI.Weights}

namespace DAI

theorem descentStep_quadraticShift (hE : Differentiable ℝ E) (c : ℝ)
    (hLower : -Λ.minus < c) (hUpper : c < Λ.plus) (x₀ x : H) :
    descentStep (gradient (UN.quadraticShift E c x₀)) (Λ.shift c hLower hUpper) x =
      (Λ.plus / (Λ.plus - c)) • descentStep (gradient E) Λ x - (c / (Λ.plus - c)) • x₀ := by
  apply ext_inner_right ℝ
  intro v
  simp only [descentStep, gradientStep, gradient_quadraticShift hE, Scales.tauPlus,
    Scales.shift, inner_sub_left, real_inner_smul_left]
  field_simp [(sub_pos.mpr hUpper).ne', Λ.plus_pos.ne']
  ring

theorem ascentStep_quadraticShift (hE : Differentiable ℝ E) (c : ℝ)
    (hLower : -Λ.minus < c) (hUpper : c < Λ.plus) (x₀ x : H) :
    ascentStep (gradient (UN.quadraticShift E c x₀)) (Λ.shift c hLower hUpper) x =
      (Λ.minus / (Λ.minus + c)) • ascentStep (gradient E) Λ x + (c / (Λ.minus + c)) • x₀ := by
  apply ext_inner_right ℝ
  intro v
  simp only [ascentStep, gradientStep, gradient_quadraticShift hE, Scales.tauMinus,
    Scales.shift, inner_sub_left, inner_add_left, real_inner_smul_left]
  field_simp [(by linarith : Λ.minus + c ≠ 0), Λ.minus_pos.ne']
  ring

theorem phiPlus_quadraticShift (hE : Differentiable ℝ E) (c : ℝ)
    (hLower : -Λ.minus < c) (hUpper : c < Λ.plus) (x₀ x₁ x₂ : H) :
    phiPlus (UN.quadraticShift E c x₀) (Λ.shift c hLower hUpper) x₁ x₂ =
      Λ.plus / (Λ.plus - c) * phiPlus E Λ x₁ x₂ := by
  rw [phiPlus, bregman_quadraticShift hE]
  dsimp [phiPlus, Scales.tauPlus, Scales.shift]
  field_simp [(sub_pos.mpr hUpper).ne', Λ.plus_pos.ne']
  ring

theorem phiMinus_quadraticShift (hE : Differentiable ℝ E) (c : ℝ)
    (hLower : -Λ.minus < c) (hUpper : c < Λ.plus) (x₀ x₁ x₂ : H) :
    phiMinus (UN.quadraticShift E c x₀) (Λ.shift c hLower hUpper) x₁ x₂ =
      Λ.minus / (Λ.minus + c) * phiMinus E Λ x₁ x₂ := by
  rw [phiMinus, bregman_quadraticShift hE]
  dsimp [phiMinus, Scales.tauMinus, Scales.shift]
  field_simp [(by linarith : Λ.minus + c ≠ 0), Λ.minus_pos.ne']
  ring

theorem step_inner_quadraticShift (hE : Differentiable ℝ E) (c : ℝ)
    (hLower : -Λ.minus < c) (hUpper : c < Λ.plus) (x₀ x y z : H) :
    let Λ' := Λ.shift c hLower hUpper
    let g' := gradient (UN.quadraticShift E c x₀)
    ⟪descentStep g' Λ' x - descentStep g' Λ' y, ascentStep g' Λ' x - ascentStep g' Λ' z⟫ =
      (Λ.plus / (Λ.plus - c) * (Λ.minus / (Λ.minus + c))) *
        ⟪descentStep (gradient E) Λ x - descentStep (gradient E) Λ y,
          ascentStep (gradient E) Λ x - ascentStep (gradient E) Λ z⟫ := by
  dsimp only
  simp only [descentStep_quadraticShift hE, ascentStep_quadraticShift hE,
    sub_sub_sub_cancel_right, add_sub_add_right_eq_sub, ← smul_sub,
    real_inner_smul_left, real_inner_smul_right]
  ring

theorem descentStep_scale (hE : Differentiable ℝ E) (Λ : Scales) (a : ℝ) (ha : 0 < a) (x : H) :
    descentStep (gradient (fun x => a * E x)) (Λ.scale a ha) x = descentStep (gradient E) Λ x := by
  simp [descentStep, gradientStep, gradient_const_mul hE, Scales.tauPlus,
    Scales.scale, smul_smul, mul_inv_rev, ha.ne']

theorem ascentStep_scale (hE : Differentiable ℝ E) (Λ : Scales) (a : ℝ) (ha : 0 < a) (x : H) :
    ascentStep (gradient (fun x => a * E x)) (Λ.scale a ha) x = ascentStep (gradient E) Λ x := by
  simp [ascentStep, gradientStep, gradient_const_mul hE, Scales.tauMinus,
    Scales.scale, smul_smul, mul_inv_rev, ha.ne']

theorem phiPlus_scale (hE : Differentiable ℝ E) (Λ : Scales) (a : ℝ) (ha : 0 < a) (x₁ x₂ : H) :
    phiPlus (fun x => a * E x) (Λ.scale a ha) x₁ x₂ = phiPlus E Λ x₁ x₂ := by
  simp only [phiPlus, bregman_const_mul hE, Scales.tauPlus, Scales.scale]
  field_simp [ha.ne', Λ.plus_pos.ne']

theorem phiMinus_scale (hE : Differentiable ℝ E) (Λ : Scales) (a : ℝ) (ha : 0 < a) (x₁ x₂ : H) :
    phiMinus (fun x => a * E x) (Λ.scale a ha) x₁ x₂ = phiMinus E Λ x₁ x₂ := by
  simp only [phiMinus, bregman_const_mul hE, Scales.tauMinus, Scales.scale]
  field_simp [ha.ne', Λ.minus_pos.ne']

end DAI

open DAI

namespace HasDAI

/-- Subtracting a quadratic preserves DAI with shifted scales and rescaled weights. -/
theorem quadraticShift (hDAI : HasDAI Λ ρ E) (c : ℝ)
    (hLower : -Λ.minus < c) (hUpper : c < Λ.plus) (x₀ : H) :
    HasDAI (Λ.shift c hLower hUpper) (ρ.quadraticShift Λ c hLower hUpper) (UN.quadraticShift E c x₀) := by
  refine ⟨hDAI.contDiff.sub (contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))), ?_⟩
  intro x y z
  rw [step_inner_quadraticShift hDAI.differentiable, phiPlus_quadraticShift hDAI.differentiable,
    phiMinus_quadraticShift hDAI.differentiable]
  have hFactor : 0 ≤ Λ.plus / (Λ.plus - c) * (Λ.minus / (Λ.minus + c)) :=
    mul_nonneg (div_nonneg Λ.plus_pos.le (sub_pos.mpr hUpper).le)
      (div_nonneg Λ.minus_pos.le (by linarith))
  convert mul_le_mul_of_nonneg_left (hDAI.apply x y z) hFactor using 1
  dsimp [Weights.quadraticShift]
  ring

/-- Positive energy scaling preserves DAI when the scales are multiplied by the same factor. -/
theorem scale (hDAI : HasDAI Λ ρ E) (a : ℝ) (ha : 0 < a) :
    HasDAI (Λ.scale a ha) ρ (fun x => a * E x) := by
  refine ⟨contDiff_const.mul hDAI.contDiff, ?_⟩
  intro x y z
  simpa only [descentStep_scale hDAI.differentiable, ascentStep_scale hDAI.differentiable,
    phiPlus_scale hDAI.differentiable, phiMinus_scale hDAI.differentiable] using hDAI.apply x y z

end HasDAI

/-- The quadratic-shift transformation of DAI is reversible. -/
theorem hasDAI_quadraticShift_iff (c : ℝ)
    (hLower : -Λ.minus < c) (hUpper : c < Λ.plus) (x₀ : H) :
    HasDAI (Λ.shift c hLower hUpper) (ρ.quadraticShift Λ c hLower hUpper) (UN.quadraticShift E c x₀) ↔
      HasDAI Λ ρ E := by
  constructor
  · intro hDAI
    have hLower' : -(Λ.shift c hLower hUpper).minus < -c := by
      dsimp [Scales.shift]
      linarith [Λ.minus_pos]
    have hUpper' : -c < (Λ.shift c hLower hUpper).plus := by
      dsimp [Scales.shift]
      linarith [Λ.plus_pos]
    have hScales : (Λ.shift c hLower hUpper).shift (-c) hLower' hUpper' = Λ := by
      cases Λ
      simp [Scales.shift]
    have hWeights :
        (ρ.quadraticShift Λ c hLower hUpper).quadraticShift (Λ.shift c hLower hUpper) (-c) hLower' hUpper' = ρ := by
      cases ρ
      simp [Weights.quadraticShift, Scales.shift, Λ.plus_pos.ne', Λ.minus_pos.ne',
        (sub_pos.mpr hUpper).ne', (by linarith : Λ.minus + c ≠ 0)]
    simpa only [hScales, hWeights, quadraticShift_quadraticShift, add_neg_cancel, quadraticShift_zero] using
      hDAI.quadraticShift (-c) hLower' hUpper' x₀
  · exact fun hDAI => hDAI.quadraticShift c hLower hUpper x₀

end UN
