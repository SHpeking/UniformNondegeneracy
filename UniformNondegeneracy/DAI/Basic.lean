module

public import UniformNondegeneracy.Analysis.Bregman
public import UniformNondegeneracy.DAI.Steps

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Descent–ascent differences and the algebraic DAI interface
-/

noncomputable section

namespace UN

open DAI

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

namespace DAI

/-- Φ₊: the Bregman difference of the descent potential. -/
def phiPlus (E : H → ℝ) (g : H → H) (Λ : Scales) (x₁ x₂ : H) : ℝ :=
  ‖x₁ - x₂‖ ^ 2 / 2 - Λ.tauPlus * bregman E g x₁ x₂

/-- Φ₋: the Bregman difference of the ascent potential. -/
def phiMinus (E : H → ℝ) (g : H → H) (Λ : Scales) (x₁ x₂ : H) : ℝ :=
  ‖x₁ - x₂‖ ^ 2 / 2 + Λ.tauMinus * bregman E g x₁ x₂

end DAI

/-- DAI means descent–ascent inequality. The gradients of Φ are written as differences of explicit update maps, so this predicate is purely algebraic. In `∀ x y z`, `y` is the descent anchor and `z` is the ascent anchor. -/
def HasDAI (E : H → ℝ) (g : H → H) (Λ : Scales) (ρ : Weights) : Prop :=
  ∀ x y z,
    ⟪descentStep g Λ x - descentStep g Λ y, ascentStep g Λ x - ascentStep g Λ z⟫ ≤
      ρ.plus * phiPlus E g Λ x y + ρ.minus * phiMinus E g Λ x z

namespace DAI

theorem hasGradientAt_phiPlus [CompleteSpace H] {E : H → ℝ} {g : H → H}
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (Λ : Scales) (x₁ x₂ : H) :
    HasGradientAt (fun x => phiPlus E g Λ x x₂) (descentStep g Λ x₁ - descentStep g Λ x₂) x₁ := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hb := ((hGrad x₁).hasFDerivAt.sub_const (E x₂)).sub
    ((innerSL ℝ (g x₂)).hasFDerivAt.comp x₁ ((hasFDerivAt_id x₁).sub_const x₂))
  convert ((hasGradientAt_quadratic 1 x₂ x₁).hasFDerivAt).sub (hb.const_mul Λ.tauPlus) using 1
  · ext x
    simp [phiPlus, bregman]
    ring
  · ext v
    simp [descentStep, gradientStep, InnerProductSpace.toDual]
    ring

theorem hasGradientAt_phiMinus [CompleteSpace H] {E : H → ℝ} {g : H → H}
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (Λ : Scales) (x₁ x₂ : H) :
    HasGradientAt (fun x => phiMinus E g Λ x x₂) (ascentStep g Λ x₁ - ascentStep g Λ x₂) x₁ := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hb := ((hGrad x₁).hasFDerivAt.sub_const (E x₂)).sub
    ((innerSL ℝ (g x₂)).hasFDerivAt.comp x₁ ((hasFDerivAt_id x₁).sub_const x₂))
  convert ((hasGradientAt_quadratic 1 x₂ x₁).hasFDerivAt).add (hb.const_mul Λ.tauMinus) using 1
  · ext x
    simp [phiMinus, bregman]
    ring
  · ext v
    simp [ascentStep, gradientStep, InnerProductSpace.toDual]
    ring

theorem phiPlus_three_point (E : H → ℝ) (g : H → H) (Λ : Scales)
    (x₃ x₁ x₂ : H) :
    phiPlus E g Λ x₃ x₂ =
      phiPlus E g Λ x₁ x₂ + ⟪descentStep g Λ x₁ - descentStep g Λ x₂, x₃ - x₁⟫ + phiPlus E g Λ x₃ x₁ := by
  unfold phiPlus bregman descentStep gradientStep
  simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right, real_inner_smul_left]
  simp only [real_inner_comm x₃ x₁, real_inner_comm x₂ x₁, real_inner_comm x₂ x₃, real_inner_self_eq_norm_sq]
  ring

theorem phiMinus_three_point (E : H → ℝ) (g : H → H) (Λ : Scales)
    (x₃ x₁ x₂ : H) :
    phiMinus E g Λ x₃ x₂ =
      phiMinus E g Λ x₁ x₂ + ⟪ascentStep g Λ x₁ - ascentStep g Λ x₂, x₃ - x₁⟫ + phiMinus E g Λ x₃ x₁ := by
  unfold phiMinus bregman ascentStep gradientStep
  simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right, real_inner_smul_left]
  simp only [real_inner_comm x₃ x₁, real_inner_comm x₂ x₁, real_inner_comm x₂ x₃, real_inner_self_eq_norm_sq]
  ring

end DAI

namespace HasBregmanBounds

variable {E : H → ℝ} {g : H → H} {Λ : Scales}

theorem phiPlus_nonneg (hBounds : HasBregmanBounds E g Λ.plus Λ.minus) (x₁ x₂ : H) :
    0 ≤ phiPlus E g Λ x₁ x₂ := by
  have h := mul_le_mul_of_nonneg_left (hBounds.upper x₁ x₂) (Λ.tauPlus_pos.le)
  have hn : Λ.tauPlus * (Λ.plus / 2 * ‖x₁ - x₂‖ ^ 2) = ‖x₁ - x₂‖ ^ 2 / 2 := by
    dsimp [Scales.tauPlus]
    field_simp [ne_of_gt Λ.plus_pos, ne_of_gt Λ.minus_pos]
  unfold phiPlus
  linarith

theorem phiMinus_nonneg (hBounds : HasBregmanBounds E g Λ.plus Λ.minus) (x₁ x₂ : H) :
    0 ≤ phiMinus E g Λ x₁ x₂ := by
  have h := mul_le_mul_of_nonneg_left (hBounds.lower x₁ x₂) (Λ.tauMinus_pos.le)
  have hn : Λ.tauMinus * (-(Λ.minus / 2) * ‖x₁ - x₂‖ ^ 2) = -‖x₁ - x₂‖ ^ 2 / 2 := by
    dsimp [Scales.tauMinus]
    field_simp [ne_of_gt Λ.plus_pos, ne_of_gt Λ.minus_pos]
  unfold phiMinus
  linarith

/-- Trial-point estimate; its proof uses only the global Bregman bounds. -/
theorem descentStep_norm_sq_le (hBounds : HasBregmanBounds E g Λ.plus Λ.minus) (x₁ x₂ : H) :
    ‖descentStep g Λ x₁ - descentStep g Λ x₂‖ ^ 2 ≤ 2 * (1 + Λ.minus / Λ.plus) * phiPlus E g Λ x₁ x₂ := by
  apply norm_sq_le_of_nonneg_quadratic (fun ξ => phiPlus E g Λ ξ x₂) x₁
  · positivity [Λ.plus_pos, Λ.minus_pos]
  · exact fun ξ => hBounds.phiPlus_nonneg ξ x₂
  · intro ξ
    rw [phiPlus_three_point E g Λ ξ x₁ x₂]
    have h := mul_le_mul_of_nonneg_left (hBounds.lower ξ x₁) Λ.tauPlus_pos.le
    have hid : -(Λ.tauPlus * (-(Λ.minus / 2) * ‖ξ - x₁‖ ^ 2)) + ‖ξ - x₁‖ ^ 2 / 2 =
        (1 + Λ.minus / Λ.plus) / 2 * ‖ξ - x₁‖ ^ 2 := by
      dsimp [Scales.tauPlus]
      ring
    unfold phiPlus
    linarith

theorem ascentStep_norm_sq_le (hBounds : HasBregmanBounds E g Λ.plus Λ.minus) (x₁ x₂ : H) :
    ‖ascentStep g Λ x₁ - ascentStep g Λ x₂‖ ^ 2 ≤ 2 * (1 + Λ.plus / Λ.minus) * phiMinus E g Λ x₁ x₂ := by
  apply norm_sq_le_of_nonneg_quadratic (fun ξ => phiMinus E g Λ ξ x₂) x₁
  · positivity [Λ.plus_pos, Λ.minus_pos]
  · exact fun ξ => hBounds.phiMinus_nonneg ξ x₂
  · intro ξ
    rw [phiMinus_three_point E g Λ ξ x₁ x₂]
    have h := mul_le_mul_of_nonneg_left (hBounds.upper ξ x₁) Λ.tauMinus_pos.le
    have hid : Λ.tauMinus * (Λ.plus / 2 * ‖ξ - x₁‖ ^ 2) + ‖ξ - x₁‖ ^ 2 / 2 =
        (1 + Λ.plus / Λ.minus) / 2 * ‖ξ - x₁‖ ^ 2 := by
      dsimp [Scales.tauMinus]
      ring
    unfold phiMinus
    linarith

end HasBregmanBounds

end UN
