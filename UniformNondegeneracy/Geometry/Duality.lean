module

public import UniformNondegeneracy.Geometry.Basic

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Dual energy and Bregman estimates

The dual is defined using the inverse gradient, not a convex conjugate. Its differentiability is proved by a quadratic remainder estimate, so neither a Hessian nor differentiability of the inverse map is assumed.
-/

open Filter Asymptotics
open scoped Topology

noncomputable section

namespace UN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

namespace GradientMap

/-- The inverse energy is differentiable even when its inverse map has no derivative. -/
theorem hasGradientAt_inverseEnergy
    (E : H → ℝ) (g gInv : H → H) (LInv : ℝ)
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (hRight : ∀ p, g (gInv p) = p)
    (hContinuous : Continuous gInv)
    (hLip : ∀ p₁ p₂, ‖gInv p₁ - gInv p₂‖ ≤ LInv * ‖p₁ - p₂‖)
    (p : H) :
    HasGradientAt (fun p₁ => ⟪p₁, gInv p₁⟫ - E (gInv p₁)) (gInv p) p := by
  apply hasGradientAt_iff_isLittleO.mpr
  have hinv : (fun p₁ => gInv p₁ - gInv p) =O[𝓝 p] (fun p₁ => p₁ - p) :=
    isBigO_of_le' _ (fun p₁ => hLip p₁ p)
  have hrem := (hasGradientAt_iff_isLittleO.mp (hGrad (gInv p))).comp_tendsto
    (hContinuous.tendsto p)
  simp only [hRight, Function.comp_def] at hrem
  have hsmall : (fun p₁ => ‖gInv p₁ - gInv p‖) =o[𝓝 p] (fun _ => (1 : ℝ)) := by
    apply (isLittleO_one_iff ℝ).mpr
    simpa using ((hContinuous.tendsto p).sub_const (gInv p)).norm
  have hinner : (fun p₁ => ⟪p₁ - p, gInv p₁ - gInv p⟫) =o[𝓝 p] (fun p₁ => p₁ - p) := by
    have hprod := hsmall.mul_isBigO (isBigO_refl (fun p₁ : H => ‖p₁ - p‖) (𝓝 p))
    simp only [one_mul] at hprod
    apply (isBigO_of_le (𝓝 p) (fun p₁ => ?_)).trans_isLittleO hprod |>.of_norm_right
    simpa only [Real.norm_eq_abs, abs_mul, abs_norm, mul_comm] using
      norm_inner_le_norm (𝕜 := ℝ) (p₁ - p) (gInv p₁ - gInv p)
  convert hinner.sub (hrem.trans_isBigO hinv) using 1
  ext p₁
  simp only [inner_sub_left, inner_sub_right]
  rw [real_inner_comm (gInv p) p₁, real_inner_comm (gInv p) p]
  ring

end GradientMap

/-- Dual energy $E^\sharp(p)=\langle p,g^{-1}(p)\rangle-E(g^{-1}(p))$, evaluated at the dual point `p`. -/
def dualEnergy (E : H → ℝ) (g : H → H) (p : H) : ℝ :=
  ⟪p, inverseGradient g p⟫ - E (inverseGradient g p)

omit [CompleteSpace H] in
private lemma reciprocal_secant (x p : H) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ⟪x + (1 / b) • p, x - (1 / a) • p⟫ = -(⟪p + b • x, p - a • x⟫) / (a * b) := by
  simp only [inner_add_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm x p]
  field_simp; ring

namespace IsUN

variable {bounds : CurvatureBounds} {E : H → ℝ} {g : H → H}

local notation "μ₊" => bounds.muPlus
local notation "μ₋" => bounds.muMinus
local notation "L₊" => bounds.lPlus
local notation "L₋" => bounds.lMinus
local notation "D" => bregman E g
local notation "xStar" => stationaryPoint g
local notation "EStar" => stationaryValue E g
local notation "Esharp" => dualEnergy E g
local notation "gInv" => inverseGradient g

theorem hasGradientAt_dualEnergy (hUN : IsUN bounds E g) (p : H) :
    HasGradientAt Esharp (gInv p) p := by
  exact GradientMap.hasGradientAt_inverseEnergy E g gInv
    bounds.muMin⁻¹ hUN.has_gradient hUN.gradient_inverseGradient
    hUN.inverseGradient_continuous hUN.inverse_norm_sub_le p

theorem dual (hUN : IsUN bounds E g) :
    IsUN bounds.dual Esharp gInv := by
  refine ⟨hUN.hasGradientAt_dualEnergy, ?_, ?_⟩
  · intro p₁ p₂
    change 0 ≤ ⟪gInv p₁ - gInv p₂ + (1 / L₋) • (p₁ - p₂), gInv p₁ - gInv p₂ - (1 / L₊) • (p₁ - p₂)⟫
    rw [reciprocal_secant _ _ _ _ bounds.lPlus_pos.ne' bounds.lMinus_pos.ne']
    apply div_nonneg _ (mul_pos bounds.lPlus_pos bounds.lMinus_pos).le
    have h := hUN.outer_secant (gInv p₁) (gInv p₂)
    simpa only [hUN.gradient_inverseGradient, neg_nonneg] using h
  · intro p₁ p₂
    change ⟪gInv p₁ - gInv p₂ + (1 / μ₋) • (p₁ - p₂), gInv p₁ - gInv p₂ - (1 / μ₊) • (p₁ - p₂)⟫ ≤ 0
    rw [reciprocal_secant _ _ _ _ bounds.muPlus_pos.ne' bounds.muMinus_pos.ne']
    apply div_nonpos_of_nonpos_of_nonneg _ (mul_pos bounds.muPlus_pos bounds.muMinus_pos).le
    have h := hUN.inner_secant (gInv p₁) (gInv p₂)
    simpa only [hUN.gradient_inverseGradient, neg_nonpos] using h

theorem dualEnergy_dualEnergy (hUN : IsUN bounds E g) :
    dualEnergy Esharp gInv = E := by
  funext x
  have hinv : inverseGradient gInv x = g x := by
    simpa only [hUN.inverseGradient_gradient] using hUN.dual.inverseGradient_gradient (g x)
  simp only [dualEnergy, hinv, hUN.inverseGradient_gradient]
  rw [real_inner_comm x (g x)]
  ring

theorem bregman_reciprocity (hUN : IsUN bounds E g) (x₁ x₂ : H) :
    D x₁ x₂ = bregman Esharp gInv (g x₂) (g x₁) := by
  simp only [bregman, dualEnergy, hUN.inverseGradient_gradient, inner_sub_right]
  rw [real_inner_comm x₁ (g x₂), real_inner_comm x₁ (g x₁)]
  ring

theorem dual_bregman_bounds (hUN : IsUN bounds E g) (p₁ p₂ : H) :
    -(1 / (2 * μ₋)) * ‖p₁ - p₂‖ ^ 2 ≤ bregman Esharp gInv p₁ p₂ ∧
    bregman Esharp gInv p₁ p₂ ≤ (1 / (2 * μ₊)) * ‖p₁ - p₂‖ ^ 2 := by
  simpa only [CurvatureBounds.dual, div_eq_mul_inv, mul_inv_rev, one_mul] using hUN.dual.bregman_bounds p₁ p₂

/-- The two signed PL estimates; energy may lie on either side of its stationary value. PL stands for Polyak–Łojasiewicz. -/
theorem signedPL (hUN : IsUN bounds E g) (x : H) :
    -(‖g x‖ ^ 2 / (2 * μ₋)) ≤ E x - EStar ∧
    E x - EStar ≤ ‖g x‖ ^ 2 / (2 * μ₊) := by
  have h := hUN.dual_bregman_bounds (g xStar) (g x)
  rw [← hUN.bregman_reciprocity, hUN.bregman_stationaryPoint] at h
  simpa only [hUN.gradient_stationaryPoint, zero_sub, norm_neg,
    one_div, neg_mul, div_eq_mul_inv, mul_comm, one_mul, mul_neg] using h

/-- The general Bregman interpolation estimate applied to the inverse-gradient energy. -/
theorem dual_bregman_interpolation (hUN : IsUN bounds E g) (p₁ p₂ : H) :
    bregman Esharp gInv p₁ p₂ ≤
      (‖p₁ - p₂‖ ^ 2 + 2 * μ₋ * ⟪p₁ - p₂, gInv p₁ - gInv p₂⟫ - μ₊ * μ₋ * ‖gInv p₁ - gInv p₂‖ ^ 2) / (2 * (μ₊ + μ₋)) := by
  have h := hUN.dual.hasBregmanBounds.interpolation_upper
    (add_pos (one_div_pos.mpr bounds.muPlus_pos) (one_div_pos.mpr bounds.muMinus_pos)) p₁ p₂
  convert h using 1
  dsimp [CurvatureBounds.dual]
  field_simp [bounds.muPlus_pos.ne', bounds.muMinus_pos.ne', (add_pos bounds.muPlus_pos bounds.muMinus_pos).ne']
  field_simp [(add_pos bounds.muMinus_pos bounds.muPlus_pos).ne']
  ring

theorem refined_inner_secant (hUN : IsUN bounds E g) (x₁ x₂ : H) :
    2 * bounds.innerRadius * |D x₁ x₂ - D x₂ x₁| ≤
      ‖g x₁ - g x₂ - bounds.innerCenter • (x₁ - x₂)‖ ^ 2 - bounds.innerRadius ^ 2 * ‖x₁ - x₂‖ ^ 2 := by
  have h1 := hUN.dual_bregman_interpolation (g x₁) (g x₂)
  have h2 := hUN.dual_bregman_interpolation (g x₂) (g x₁)
  rw [← hUN.bregman_reciprocity, hUN.inverseGradient_gradient, hUN.inverseGradient_gradient] at h1 h2
  have hnormg : ‖g x₂ - g x₁‖ = ‖g x₁ - g x₂‖ := norm_sub_rev _ _
  have hnormx : ‖x₂ - x₁‖ = ‖x₁ - x₂‖ := norm_sub_rev _ _
  have hinner : ⟪g x₂ - g x₁, x₂ - x₁⟫ = ⟪g x₁ - g x₂, x₁ - x₂⟫ := by
    rw [← neg_sub (g x₁) (g x₂), ← neg_sub x₁ x₂, inner_neg_neg]
  rw [hnormg, hnormx, hinner] at h2
  have hmuP := bounds.muPlus_pos
  have hmuM := bounds.muMinus_pos
  have hpos : 0 < 2 * (μ₊ + μ₋) := by
    positivity
  have h1' := (le_div_iff₀ hpos).mp h1
  have h2' := (le_div_iff₀ hpos).mp h2
  have hsum := bregman_add_reverse E g x₁ x₂
  have hrad : 0 ≤ 2 * bounds.innerRadius := by
    dsimp [CurvatureBounds.innerRadius]; positivity
  rw [← abs_of_nonneg hrad, ← abs_mul, abs_le]
  rw [norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right,
    CurvatureBounds.innerCenter, CurvatureBounds.innerRadius]
  rw [← hsum] at h1' h2' ⊢
  constructor <;> nlinarith only [h1', h2']

end IsUN
end UN
