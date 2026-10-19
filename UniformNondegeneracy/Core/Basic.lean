module

public import UniformNondegeneracy.Core.Parameters

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Secant definition of uniform nondegeneracy
-/

namespace UN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Uniform nondegeneracy of `E` with gradient `g`, given by the inner and outer secant inequalities. -/
structure IsUN (bounds : CurvatureBounds) (E : H → ℝ) (g : H → H) : Prop where
  has_gradient : ∀ x, HasGradientAt E (g x) x

  inner_secant : ∀ x₁ x₂, 0 ≤ ⟪g x₁ - g x₂ + bounds.muMinus • (x₁ - x₂), g x₁ - g x₂ - bounds.muPlus • (x₁ - x₂)⟫
  outer_secant : ∀ x₁ x₂, ⟪g x₁ - g x₂ + bounds.lMinus • (x₁ - x₂), g x₁ - g x₂ - bounds.lPlus • (x₁ - x₂)⟫ ≤ 0

end UN
