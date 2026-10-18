module

public import UniformNondegeneracy.Core.Parameters

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Secant definition of uniform nondegeneracy

`IsUN bounds E g` contains exactly the gradient identity and the two global secant inequalities. In particular, surjectivity and a stationary point are conclusions in `Geometry`, not fields of this predicate.
-/

namespace UN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Uniform nondegeneracy, expressed entirely in first-order terms.

`E : H → ℝ` is the energy and `g : H → H` is its specified gradient. Positive/negative refer to the two curvature bands, not to a splitting of the Hilbert space. -/
structure IsUN (bounds : CurvatureBounds) (E : H → ℝ) (g : H → H) : Prop where
  has_gradient : ∀ x, HasGradientAt E (g x) x

  inner_secant : ∀ x₁ x₂, 0 ≤ ⟪g x₁ - g x₂ + bounds.muMinus • (x₁ - x₂), g x₁ - g x₂ - bounds.muPlus • (x₁ - x₂)⟫
  outer_secant : ∀ x₁ x₂, ⟪g x₁ - g x₂ + bounds.lMinus • (x₁ - x₂), g x₁ - g x₂ - bounds.lPlus • (x₁ - x₂)⟫ ≤ 0

end UN
