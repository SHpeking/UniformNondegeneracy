module

public import UniformNondegeneracy.Core.Basic
public import UniformNondegeneracy.DAI.Secant
public import UniformNondegeneracy.DAI.Weights

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Uniform nondegeneracy from two descent–ascent inequalities

The DAI at the outer scales gives the outer secant and the gradient identity. The DAI at the balanced scales, with weights determined by the maximum band width, gives the inner secant.
-/

namespace UN

open DAI

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
private lemma balanced_secant_identity (bounds : CurvatureBounds) (u v : H) :
    ⟪v + bounds.muMinus • u, v - bounds.muPlus • u⟫ =
      ⟪v + (balancedScales bounds).minus • u, v - (balancedScales bounds).plus • u⟫ +
        bounds.maxBandWidth * (bounds.maxBandWidth + bounds.muPlus + bounds.muMinus) * ‖u‖ ^ 2 := by
  simp only [balancedScales, inner_add_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm u v]
  ring

theorem isUN_of_dais (bounds : CurvatureBounds) {E : H → ℝ} {g : H → H}
    (hOuter : HasDAI E g (outerScales bounds) (outerSecantWeights bounds))
    (hInner : HasDAI E g (balancedScales bounds) (innerSecantWeights bounds)) :
    IsUN bounds E g := by
  refine ⟨?_, ?_, ?_⟩
  · exact (hOuter.hasBregmanBounds (outerSecantWeights_pos bounds).1 (outerSecantWeights_pos bounds).2).hasGradientAt
  · intro x₁ x₂
    have h := (hInner.curvature_secant_bounds_of_balanced (innerSecantWeights_balanced bounds) x₁ x₂).1
    rw [innerSecantWeights_product] at h
    rw [balanced_secant_identity]
    linarith
  · intro x₁ x₂
    exact (hOuter.curvature_secant_bounds_of_balanced (outerSecantWeights_balanced bounds) x₁ x₂).2

end UN
