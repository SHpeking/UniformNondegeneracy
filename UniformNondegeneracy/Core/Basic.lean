module

public import UniformNondegeneracy.Core.Parameters
public import UniformNondegeneracy.Analysis.GradientBounds

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Secant definition of uniform nondegeneracy
-/

namespace UN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A continuously differentiable energy is UN when its gradient satisfies the inner and outer secant inequalities. -/
structure IsUN (bounds : CurvatureBounds) (E : H → ℝ) : Prop where
  contDiff : ContDiff ℝ 1 E

  inner_secant : ∀ x₁ x₂, 0 ≤ ⟪gradient E x₁ - gradient E x₂ + bounds.muMinus • (x₁ - x₂), gradient E x₁ - gradient E x₂ - bounds.muPlus • (x₁ - x₂)⟫
  outer_secant : ∀ x₁ x₂, ⟪gradient E x₁ - gradient E x₂ + bounds.lMinus • (x₁ - x₂), gradient E x₁ - gradient E x₂ - bounds.lPlus • (x₁ - x₂)⟫ ≤ 0

variable {bounds : CurvatureBounds} {E : H → ℝ}

theorem IsUN.differentiable (hUN : IsUN bounds E) : Differentiable ℝ E :=
  hUN.contDiff.differentiable one_ne_zero

theorem IsUN.hasGradientAt (hUN : IsUN bounds E) (x : H) : HasGradientAt E (gradient E x) x :=
  (hUN.differentiable x).hasGradientAt

/-- Establish UN using an explicitly computed gradient and its secant inequalities. -/
theorem IsUN.of_hasGradient {g : H → H}
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (hInner : ∀ x₁ x₂, 0 ≤ ⟪g x₁ - g x₂ + bounds.muMinus • (x₁ - x₂), g x₁ - g x₂ - bounds.muPlus • (x₁ - x₂)⟫)
    (hOuter : ∀ x₁ x₂, ⟪g x₁ - g x₂ + bounds.lMinus • (x₁ - x₂), g x₁ - g x₂ - bounds.lPlus • (x₁ - x₂)⟫ ≤ 0) :
    IsUN bounds E := by
  have hLip : LipschitzWith ⟨bounds.lMax, bounds.lMax_pos.le⟩ g :=
    lipschitzWith_iff_norm_sub_le.mpr fun x₁ x₂ =>
      norm_le_of_outer_secant _ _ bounds.lPlus_pos.le bounds.lMinus_pos.le (hOuter x₁ x₂)
  have hg := gradient_eq hGrad
  refine ⟨contDiff_one_iff_fderiv.mpr ⟨fun x => (hGrad x).differentiableAt, ?_⟩, ?_, ?_⟩
  · have hDeriv : fderiv ℝ E = fun x => (InnerProductSpace.toDual ℝ H) (g x) :=
      funext fun x => (hGrad x).hasFDerivAt.fderiv
    rw [hDeriv]
    exact (InnerProductSpace.toDual ℝ H).continuous.comp hLip.continuous
  · simpa only [hg] using hInner
  · simpa only [hg] using hOuter

end UN
