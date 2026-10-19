module

public import UniformNondegeneracy.DAI.Parameters
public import UniformNondegeneracy.Analysis.GradientSteps

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Descent and ascent maps
-/

noncomputable section
namespace UN.DAI
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Descent with step size `1 / Λ.plus`. -/
def descentStep (g : H → H) (Λ : Scales) (x : H) : H :=
  gradientStep g Λ.tauPlus x

/-- Ascent with step size `1 / Λ.minus`. -/
def ascentStep (g : H → H) (Λ : Scales) (x : H) : H :=
  gradientStep g (-Λ.tauMinus) x

/-- The inner product of descent and ascent differences is the negative curvature secant divided by the product of the scales. -/
theorem step_inner_mul_scales (g : H → H) (Λ : Scales) (x₁ x₂ : H) :
    (Λ.plus * Λ.minus) * ⟪descentStep g Λ x₁ - descentStep g Λ x₂, ascentStep g Λ x₁ - ascentStep g Λ x₂⟫ =
      -⟪g x₁ - g x₂ + Λ.minus • (x₁ - x₂), g x₁ - g x₂ - Λ.plus • (x₁ - x₂)⟫ := by
  have hIdentity (u v : H) :
      (Λ.plus * Λ.minus) * ⟪u - Λ.tauPlus • v, u + Λ.tauMinus • v⟫ = -⟪v + Λ.minus • u, v - Λ.plus • u⟫ := by
    simp only [inner_sub_left, inner_add_left, inner_sub_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_comm u v]
    dsimp [Scales.tauPlus, Scales.tauMinus]
    field_simp [Λ.plus_pos.ne', Λ.minus_pos.ne']
    ring
  have hDown : descentStep g Λ x₁ - descentStep g Λ x₂ = (x₁ - x₂) - Λ.tauPlus • (g x₁ - g x₂) := by
    dsimp [descentStep, gradientStep]
    module
  have hUp : ascentStep g Λ x₁ - ascentStep g Λ x₂ = (x₁ - x₂) + Λ.tauMinus • (g x₁ - g x₂) := by
    dsimp [ascentStep, gradientStep]
    module
  rw [hDown, hUp]
  exact hIdentity (x₁ - x₂) (g x₁ - g x₂)

end UN.DAI
