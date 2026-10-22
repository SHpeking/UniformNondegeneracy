module

public import UniformNondegeneracy.Core.Basic
public import UniformNondegeneracy.Analysis.StrongConvexity

@[expose] public section

/-!
# Strongly convex energies

Strongly convex energies with Lipschitz gradients are UN. The strong convexity and Lipschitz constants give the positive curvature bounds.
-/

open scoped RealInnerProductSpace

namespace UN.Examples

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {E : H → ℝ} {g : H → H} {bounds : CurvatureBounds}

/-- A strongly convex energy with a Lipschitz gradient is UN with the corresponding positive curvature bounds. -/
theorem strongConvexOn_isUN
    (hE : Differentiable ℝ E)
    (hStrong : StrongConvexOn Set.univ bounds.muPlus E)
    (hLip : LipschitzWith ⟨bounds.lPlus, bounds.lPlus_pos.le⟩ (gradient E)) :
    IsUN bounds E := by
  have hLower := strongConvexOn_bregman_lower hE hStrong
  have hBounds := (strongConvexOn_hasBregmanBounds hE hStrong hLip.norm_sub_le).mono le_rfl
    (show -bounds.muPlus ≤ bounds.lMinus by linarith [bounds.muPlus_pos, bounds.lMinus_pos])
  refine ⟨hBounds.contDiff, ?_, ?_⟩
  · intro x₁ x₂
    have h₁ := hLower x₁ x₂
    have h₂ := hLower x₂ x₁
    rw [norm_sub_rev x₂ x₁] at h₂
    have hSum := bregman_add_reverse E x₁ x₂
    have hInner : 0 ≤ ⟪gradient E x₁ - gradient E x₂, x₁ - x₂⟫ - bounds.muPlus * ‖x₁ - x₂‖ ^ 2 := by
      linarith
    have h := mul_nonneg (add_nonneg bounds.muPlus_pos.le bounds.muMinus_pos.le) hInner
    have hSq := sq_nonneg ‖gradient E x₁ - gradient E x₂ - bounds.muPlus • (x₁ - x₂)‖
    generalize gradient E x₁ - gradient E x₂ = u at h hSq ⊢
    generalize x₁ - x₂ = v at h hSq ⊢
    simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right] at hSq
    simp only [inner_add_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm u v]
    nlinarith only [h, hSq]
  · exact hBounds.outer_secant (add_nonneg bounds.lPlus_pos.le bounds.lMinus_pos.le)

/-- Establish UN from an explicitly computed gradient of a strongly convex energy. -/
theorem strongConvexOn_isUN_of_hasGradient
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (hStrong : StrongConvexOn Set.univ bounds.muPlus E)
    (hLip : ∀ x₁ x₂, ‖g x₁ - g x₂‖ ≤ bounds.lPlus * ‖x₁ - x₂‖) :
    IsUN bounds E := by
  apply strongConvexOn_isUN (fun x => (hGrad x).differentiableAt) hStrong
  rw [gradient_eq hGrad]
  exact lipschitzWith_iff_norm_sub_le.mpr hLip

end UN.Examples
