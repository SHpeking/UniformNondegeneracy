module

public import UniformNondegeneracy.Analysis.Bregman

@[expose] public section

open scoped RealInnerProductSpace Topology
open Filter Asymptotics

/-!
# Potentials for inverse gradient maps

The inverse energy has gradient `gInv` when `gInv` is a Lipschitz inverse of the gradient of `E`. Its Bregman difference reverses the arguments of the original Bregman difference.
-/

noncomputable section

namespace UN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The inverse energy `⟪p, gInv p⟫ - E (gInv p)`. -/
def inverseEnergy (E : H → ℝ) (gInv : H → H) (p : H) : ℝ :=
  ⟪p, gInv p⟫ - E (gInv p)

variable [CompleteSpace H]

/-- Inverting the gradient reverses the arguments of the Bregman difference. -/
theorem bregman_inverseEnergy {E : H → ℝ} {gInv : H → H}
    (hRight : Function.RightInverse gInv (gradient E))
    (hGradInv : ∀ p, HasGradientAt (inverseEnergy E gInv) (gInv p) p) (p₁ p₂ : H) :
    bregman (inverseEnergy E gInv) p₁ p₂ = bregman E (gInv p₂) (gInv p₁) := by
  simp only [bregman, gradient_eq hGradInv, inverseEnergy, hRight p₁, inner_sub_right]
  simp only [real_inner_comm (gInv p₂)]
  ring

namespace GradientMap

theorem hasGradientAt_inverseEnergy
    (E : H → ℝ) (g gInv : H → H) (LInv : ℝ)
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (hRight : Function.RightInverse gInv g)
    (hLip : ∀ p₁ p₂, ‖gInv p₁ - gInv p₂‖ ≤ LInv * ‖p₁ - p₂‖)
    (p : H) :
    HasGradientAt (inverseEnergy E gInv) (gInv p) p := by
  have hLip' : LipschitzWith ⟨max LInv 0, le_max_right _ _⟩ gInv :=
    lipschitzWith_iff_norm_sub_le.mpr fun p₁ p₂ =>
      (hLip p₁ p₂).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hContinuous := hLip'.continuous
  change HasGradientAt (fun p₁ => ⟪p₁, gInv p₁⟫ - E (gInv p₁)) (gInv p) p
  apply hasGradientAt_iff_isLittleO.mpr
  have hinv : (fun p₁ => gInv p₁ - gInv p) =O[𝓝 p] (fun p₁ => p₁ - p) :=
    isBigO_of_le' _ (fun p₁ => hLip p₁ p)
  have hrem := (hasGradientAt_iff_isLittleO.mp (hGrad (gInv p))).comp_tendsto
    (hContinuous.tendsto p)
  simp only [hRight p, Function.comp_def] at hrem
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

end UN
