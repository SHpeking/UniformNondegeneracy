module

public import UniformNondegeneracy.Geometry.Transforms

@[expose] public section

/-!
# Positive, negative, and indefinite quadratic examples

These examples use the foundational UN interface without DAI or algorithm assumptions.
-/

open scoped RealInnerProductSpace

namespace UN.Examples

noncomputable section

/-- Unit curvature magnitudes on both bands. A certificate does not require both signs to occur. -/
def unitBounds : CurvatureBounds where
  muPlus := 1
  muMinus := 1
  lPlus := 1
  lMinus := 1
  muPlus_pos := by norm_num
  muMinus_pos := by norm_num
  muPlus_le_lPlus := le_rfl
  muMinus_le_lMinus := le_rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The positive quadratic is UN on every real Hilbert space. -/
theorem positive_quadratic_isUN :
    IsUN unitBounds (fun x : H => ‖x‖ ^ 2 / 2) (fun x => x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simpa [div_eq_mul_inv, mul_comm] using hasGradientAt_quadratic (H := H) 1 0 x
  · intro x₁ x₂
    simp [unitBounds]
  · intro x₁ x₂
    simp [unitBounds]

/-- Sign reversal gives the negative quadratic with the same unit certificate. -/
theorem negative_quadratic_isUN :
    IsUN unitBounds (fun x : H => -(‖x‖ ^ 2 / 2)) (fun x => -x) := by
  exact positive_quadratic_isUN.neg

/-- The two-dimensional indefinite quadratic. -/
def saddleEnergy (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (x 0 ^ 2 - x 1 ^ 2) / 2

/-- Its gradient reflects the second coordinate. -/
def saddleGradient (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![x 0, -x 1]

theorem hasGradientAt_saddleEnergy (x : EuclideanSpace ℝ (Fin 2)) :
    HasGradientAt saddleEnergy (saddleGradient x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h₀ := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).hasFDerivAt (x := x)
  have h₁ := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).hasFDerivAt (x := x)
  convert ((h₀.pow 2).sub (h₁.pow 2)).const_mul (1 / 2 : ℝ) using 1
  · ext z
    simp [saddleEnergy, div_eq_mul_inv, mul_comm]
  · ext v
    simp [InnerProductSpace.toDual_apply_apply, PiLp.inner_apply, Fin.sum_univ_two, saddleGradient]
    ring

private theorem saddle_secant (x₁ x₂ : EuclideanSpace ℝ (Fin 2)) :
    ⟪saddleGradient x₁ - saddleGradient x₂ + (x₁ - x₂), saddleGradient x₁ - saddleGradient x₂ - (x₁ - x₂)⟫ = 0 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, saddleGradient]

/-- A UN energy with both positive and negative curvature directions. -/
theorem saddleEnergy_isUN : IsUN unitBounds saddleEnergy saddleGradient := by
  refine ⟨hasGradientAt_saddleEnergy, ?_, ?_⟩
  · intro x₁ x₂
    simpa [unitBounds] using (saddle_secant x₁ x₂).ge
  · intro x₁ x₂
    simpa [unitBounds] using (saddle_secant x₁ x₂).le

end
end UN.Examples
