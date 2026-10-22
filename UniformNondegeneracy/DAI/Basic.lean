module

public import UniformNondegeneracy.Analysis.GradientBounds
public import UniformNondegeneracy.DAI.Steps

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Descent–ascent inequalities
-/

noncomputable section

namespace UN

open DAI

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

namespace DAI

/-- Φ₊: the Bregman difference of the descent potential. -/
def phiPlus (E : H → ℝ) (Λ : Scales) (x₁ x₂ : H) : ℝ :=
  ‖x₁ - x₂‖ ^ 2 / 2 - Λ.tauPlus * bregman E x₁ x₂

/-- Φ₋: the Bregman difference of the ascent potential. -/
def phiMinus (E : H → ℝ) (Λ : Scales) (x₁ x₂ : H) : ℝ :=
  ‖x₁ - x₂‖ ^ 2 / 2 + Λ.tauMinus * bregman E x₁ x₂

theorem hasGradientAt_phiPlus {E : H → ℝ} {x₁ : H}
    (hE : DifferentiableAt ℝ E x₁) (Λ : Scales) (x₂ : H) :
    HasGradientAt (fun x => phiPlus E Λ x x₂)
      (descentStep (gradient E) Λ x₁ - descentStep (gradient E) Λ x₂) x₁ := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hb := (hE.hasGradientAt.hasFDerivAt.sub_const (E x₂)).sub
    ((innerSL ℝ (gradient E x₂)).hasFDerivAt.comp x₁ ((hasFDerivAt_id x₁).sub_const x₂))
  convert ((hasGradientAt_quadratic 1 x₂ x₁).hasFDerivAt).sub (hb.const_mul Λ.tauPlus) using 1
  · ext x
    simp [phiPlus, bregman]
    ring
  · ext v
    simp [descentStep, gradientStep, InnerProductSpace.toDual]
    ring

theorem hasGradientAt_phiMinus {E : H → ℝ} {x₁ : H}
    (hE : DifferentiableAt ℝ E x₁) (Λ : Scales) (x₂ : H) :
    HasGradientAt (fun x => phiMinus E Λ x x₂)
      (ascentStep (gradient E) Λ x₁ - ascentStep (gradient E) Λ x₂) x₁ := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hb := (hE.hasGradientAt.hasFDerivAt.sub_const (E x₂)).sub
    ((innerSL ℝ (gradient E x₂)).hasFDerivAt.comp x₁ ((hasFDerivAt_id x₁).sub_const x₂))
  convert ((hasGradientAt_quadratic 1 x₂ x₁).hasFDerivAt).add (hb.const_mul Λ.tauMinus) using 1
  · ext x
    simp [phiMinus, bregman]
    ring
  · ext v
    simp [ascentStep, gradientStep, InnerProductSpace.toDual]
    ring

theorem phiPlus_add_reverse (E : H → ℝ) (Λ : Scales) (x₁ x₂ : H) :
    phiPlus E Λ x₁ x₂ + phiPlus E Λ x₂ x₁ = ⟪descentStep (gradient E) Λ x₁ - descentStep (gradient E) Λ x₂, x₁ - x₂⟫ := by
  unfold phiPlus bregman descentStep gradientStep
  simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm x₂ x₁]
  ring

theorem phiMinus_add_reverse (E : H → ℝ) (Λ : Scales) (x₁ x₂ : H) :
    phiMinus E Λ x₁ x₂ + phiMinus E Λ x₂ x₁ = ⟪ascentStep (gradient E) Λ x₁ - ascentStep (gradient E) Λ x₂, x₁ - x₂⟫ := by
  unfold phiMinus bregman ascentStep gradientStep
  simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm x₂ x₁]
  ring

theorem phiPlus_three_point (E : H → ℝ) (Λ : Scales) (x₃ x₁ x₂ : H) :
    phiPlus E Λ x₃ x₂ =
      phiPlus E Λ x₁ x₂ + ⟪descentStep (gradient E) Λ x₁ - descentStep (gradient E) Λ x₂, x₃ - x₁⟫ + phiPlus E Λ x₃ x₁ := by
  unfold phiPlus bregman descentStep gradientStep
  simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right, real_inner_smul_left]
  simp only [real_inner_comm x₃ x₁, real_inner_comm x₂ x₁, real_inner_comm x₂ x₃, real_inner_self_eq_norm_sq]
  ring

theorem phiMinus_three_point (E : H → ℝ) (Λ : Scales) (x₃ x₁ x₂ : H) :
    phiMinus E Λ x₃ x₂ =
      phiMinus E Λ x₁ x₂ + ⟪ascentStep (gradient E) Λ x₁ - ascentStep (gradient E) Λ x₂, x₃ - x₁⟫ + phiMinus E Λ x₃ x₁ := by
  unfold phiMinus bregman ascentStep gradientStep
  simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right, real_inner_smul_left]
  simp only [real_inner_comm x₃ x₁, real_inner_comm x₂ x₁, real_inner_comm x₂ x₃, real_inner_self_eq_norm_sq]
  ring

end DAI

/-- A continuously differentiable energy whose gradient satisfies the descent–ascent inequality. -/
structure HasDAI (Λ : Scales) (ρ : Weights) (E : H → ℝ) : Prop where
  contDiff : ContDiff ℝ 1 E
  inequality : ∀ x y z,
    ⟪descentStep (gradient E) Λ x - descentStep (gradient E) Λ y,
      ascentStep (gradient E) Λ x - ascentStep (gradient E) Λ z⟫ ≤
      ρ.plus * phiPlus E Λ x y + ρ.minus * phiMinus E Λ x z

namespace HasDAI

variable {E : H → ℝ} {Λ : Scales} {ρ : Weights}

theorem differentiable (hDAI : HasDAI Λ ρ E) : Differentiable ℝ E :=
  hDAI.contDiff.differentiable one_ne_zero

theorem hasGradientAt (hDAI : HasDAI Λ ρ E) (x : H) : HasGradientAt E (gradient E x) x :=
  (hDAI.differentiable x).hasGradientAt

theorem apply (hDAI : HasDAI Λ ρ E) (x y z : H) :
    ⟪descentStep (gradient E) Λ x - descentStep (gradient E) Λ y,
      ascentStep (gradient E) Λ x - ascentStep (gradient E) Λ z⟫ ≤
      ρ.plus * phiPlus E Λ x y + ρ.minus * phiMinus E Λ x z :=
  hDAI.inequality x y z

/-- Positive DAI weights give Bregman bounds by setting one anchor equal to the base point. -/
theorem hasBregmanBounds (hDAI : HasDAI Λ ρ E)
    (hPlus : 0 < ρ.plus) (hMinus : 0 < ρ.minus) :
    HasBregmanBounds Λ.plus Λ.minus E := by
  constructor
  · intro x₁ x₂
    have hPhi : 0 ≤ phiMinus E Λ x₁ x₂ :=
      nonneg_of_mul_nonneg_right (by simpa [phiPlus] using hDAI.apply x₁ x₁ x₂) hMinus
    have h := mul_le_mul_of_nonneg_left hPhi Λ.minus_pos.le
    have hScale : Λ.minus * Λ.tauMinus = 1 := by dsimp [Scales.tauMinus]; field_simp [Λ.minus_pos.ne']
    dsimp [phiMinus] at h
    rw [mul_add, ← mul_assoc, hScale, one_mul] at h
    linarith
  · intro x₁ x₂
    have hPhi : 0 ≤ phiPlus E Λ x₁ x₂ :=
      nonneg_of_mul_nonneg_right (by simpa [phiMinus] using hDAI.apply x₁ x₂ x₁) hPlus
    have h := mul_le_mul_of_nonneg_left hPhi Λ.plus_pos.le
    have hScale : Λ.plus * Λ.tauPlus = 1 := by dsimp [Scales.tauPlus]; field_simp [Λ.plus_pos.ne']
    dsimp [phiPlus] at h
    rw [mul_sub, ← mul_assoc, hScale, one_mul] at h
    linarith

end HasDAI

namespace HasBregmanBounds

variable {E : H → ℝ} {Λ : Scales}

theorem phiPlus_nonneg (hBounds : HasBregmanBounds Λ.plus Λ.minus E) (x₁ x₂ : H) :
    0 ≤ phiPlus E Λ x₁ x₂ := by
  have h := mul_le_mul_of_nonneg_left (hBounds.upper x₁ x₂) (Λ.tauPlus_pos.le)
  have hn : Λ.tauPlus * (Λ.plus / 2 * ‖x₁ - x₂‖ ^ 2) = ‖x₁ - x₂‖ ^ 2 / 2 := by
    dsimp [Scales.tauPlus]
    field_simp [ne_of_gt Λ.plus_pos, ne_of_gt Λ.minus_pos]
  unfold phiPlus
  linarith

theorem phiMinus_nonneg (hBounds : HasBregmanBounds Λ.plus Λ.minus E) (x₁ x₂ : H) :
    0 ≤ phiMinus E Λ x₁ x₂ := by
  have h := mul_le_mul_of_nonneg_left (hBounds.lower x₁ x₂) (Λ.tauMinus_pos.le)
  have hn : Λ.tauMinus * (-(Λ.minus / 2) * ‖x₁ - x₂‖ ^ 2) = -‖x₁ - x₂‖ ^ 2 / 2 := by
    dsimp [Scales.tauMinus]
    field_simp [ne_of_gt Λ.plus_pos, ne_of_gt Λ.minus_pos]
  unfold phiMinus
  linarith

/-- Differences of descent images are controlled by `phiPlus`. -/
theorem descentStep_norm_sq_le (hBounds : HasBregmanBounds Λ.plus Λ.minus E) (x₁ x₂ : H) :
    ‖descentStep (gradient E) Λ x₁ - descentStep (gradient E) Λ x₂‖ ^ 2 ≤ 2 * (1 + Λ.minus / Λ.plus) * phiPlus E Λ x₁ x₂ := by
  apply norm_sq_le_of_nonneg_quadratic (fun ξ => phiPlus E Λ ξ x₂) x₁
  · positivity [Λ.plus_pos, Λ.minus_pos]
  · exact fun ξ => hBounds.phiPlus_nonneg ξ x₂
  · intro ξ
    rw [phiPlus_three_point E Λ ξ x₁ x₂]
    have h := mul_le_mul_of_nonneg_left (hBounds.lower ξ x₁) Λ.tauPlus_pos.le
    have hid : -(Λ.tauPlus * (-(Λ.minus / 2) * ‖ξ - x₁‖ ^ 2)) + ‖ξ - x₁‖ ^ 2 / 2 =
        (1 + Λ.minus / Λ.plus) / 2 * ‖ξ - x₁‖ ^ 2 := by
      dsimp [Scales.tauPlus]
      ring
    unfold phiPlus
    linarith

theorem ascentStep_norm_sq_le (hBounds : HasBregmanBounds Λ.plus Λ.minus E) (x₁ x₂ : H) :
    ‖ascentStep (gradient E) Λ x₁ - ascentStep (gradient E) Λ x₂‖ ^ 2 ≤ 2 * (1 + Λ.plus / Λ.minus) * phiMinus E Λ x₁ x₂ := by
  apply norm_sq_le_of_nonneg_quadratic (fun ξ => phiMinus E Λ ξ x₂) x₁
  · positivity [Λ.plus_pos, Λ.minus_pos]
  · exact fun ξ => hBounds.phiMinus_nonneg ξ x₂
  · intro ξ
    rw [phiMinus_three_point E Λ ξ x₁ x₂]
    have h := mul_le_mul_of_nonneg_left (hBounds.upper ξ x₁) Λ.tauMinus_pos.le
    have hid : Λ.tauMinus * (Λ.plus / 2 * ‖ξ - x₁‖ ^ 2) + ‖ξ - x₁‖ ^ 2 / 2 =
        (1 + Λ.plus / Λ.minus) / 2 * ‖ξ - x₁‖ ^ 2 := by
      dsimp [Scales.tauMinus]
      ring
    unfold phiMinus
    linarith

end HasBregmanBounds

end UN
