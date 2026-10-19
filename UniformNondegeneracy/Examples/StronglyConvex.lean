module

public import UniformNondegeneracy.Core.Basic
public import UniformNondegeneracy.Analysis.Bregman

@[expose] public section

/-!
# Strongly convex energies

Strongly convex energies with Lipschitz gradients are UN. The strong convexity and Lipschitz constants give the positive curvature bounds.
-/

open scoped RealInnerProductSpace

namespace UN.Examples

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {E : H → ℝ} {g : H → H} {μ : ℝ}

/-- Strong convexity gives a quadratic lower bound for the Bregman difference. -/
private theorem strongConvex_bregman_lower
    (hGrad : ∀ x, HasGradientAt E (g x) x) (hStrong : StrongConvexOn Set.univ μ E)
    (x₁ x₂ : H) :
    μ / 2 * ‖x₁ - x₂‖ ^ 2 ≤ bregman E g x₁ x₂ := by
  let F := fun x => E x - μ / 2 * ‖x‖ ^ 2
  let f := fun s : ℝ => F (s • (x₁ - x₂) + x₂)
  have hF (x : H) := (hGrad x).hasFDerivAt.sub (hasGradientAt_quadratic μ (0 : H) x).hasFDerivAt
  simp only [sub_zero] at hF
  have hConv : ConvexOn ℝ Set.univ f := by
    simpa only [Set.preimage_univ, Function.comp_def, AffineMap.lineMap_apply_module'] using
      (strongConvexOn_iff_convex.mp hStrong).comp_affineMap (AffineMap.lineMap x₂ x₁)
  have hDeriv : HasDerivAt f (⟪g x₂ - μ • x₂, x₁ - x₂⟫) 0 := by
    convert! (hF ((0 : ℝ) • (x₁ - x₂) + x₂)).comp_hasDerivAt 0
      (((hasDerivAt_id (0 : ℝ)).smul_const (x₁ - x₂)).add_const x₂) using 1
    simp [InnerProductSpace.toDual_apply_apply, inner_sub_left, real_inner_smul_left]
  have h := hConv.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hDeriv
  simp only [slope_def_field, f, F, one_smul, zero_smul, zero_add, sub_add_cancel, sub_zero, div_one,
    inner_sub_left, real_inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq] at h
  rw [real_inner_comm x₁ x₂] at h
  simp only [bregman, norm_sub_sq_real, inner_sub_right]
  nlinarith only [h]

variable {bounds : CurvatureBounds}

/-- A strongly convex energy with a Lipschitz gradient is UN with the corresponding positive curvature bounds. -/
theorem strongConvexOn_isUN
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (hStrong : StrongConvexOn Set.univ bounds.muPlus E)
    (hLip : ∀ x₁ x₂, ‖g x₁ - g x₂‖ ≤ bounds.lPlus * ‖x₁ - x₂‖) :
    IsUN bounds E g := by
  have hLower := strongConvex_bregman_lower hGrad hStrong
  have hBounds : HasBregmanBounds E g bounds.lPlus 0 := by
    constructor
    · intro x₁ x₂
      simpa only [zero_div, neg_zero, zero_mul] using
        (mul_nonneg (div_nonneg bounds.muPlus_pos.le (by norm_num)) (sq_nonneg ‖x₁ - x₂‖)).trans (hLower x₁ x₂)
    · intro x₁ x₂
      simpa [bregman] using
        (abs_le.mp (GradientMap.abs_taylor_remainder_le E g bounds.lPlus hGrad hLip x₂ (x₁ - x₂))).2
  have hCoco (x₁ x₂ : H) :
      ‖g x₁ - g x₂‖ ^ 2 ≤ bounds.lPlus * ⟪g x₁ - g x₂, x₁ - x₂⟫ := by
    have h₁ := hBounds.interpolation_upper (by simpa using bounds.lPlus_pos) x₁ x₂
    have h₂ := hBounds.interpolation_upper (by simpa using bounds.lPlus_pos) x₂ x₁
    rw [norm_sub_rev x₂ x₁, norm_sub_rev (g x₂) (g x₁)] at h₂
    have hInner : ⟪x₂ - x₁, g x₂ - g x₁⟫ = ⟪x₁ - x₂, g x₁ - g x₂⟫ := by
      rw [← neg_sub x₁ x₂, ← neg_sub (g x₁) (g x₂), inner_neg_neg]
    rw [hInner] at h₂
    have hDen : 0 < 2 * (bounds.lPlus + 0) := by linarith [bounds.lPlus_pos]
    have hSum := bregman_add_reverse E g x₁ x₂
    rw [real_inner_comm (g x₁ - g x₂) (x₁ - x₂)] at h₁ h₂
    have hScaled := congrArg (fun z : ℝ => bounds.lPlus * z) hSum
    nlinarith only [(le_div_iff₀ hDen).mp h₁, (le_div_iff₀ hDen).mp h₂, hScaled]
  refine ⟨hGrad, ?_, ?_⟩
  · intro x₁ x₂
    have h₁ := hLower x₁ x₂
    have h₂ := hLower x₂ x₁
    rw [norm_sub_rev x₂ x₁] at h₂
    have hSum := bregman_add_reverse E g x₁ x₂
    have hInner : 0 ≤ ⟪g x₁ - g x₂, x₁ - x₂⟫ - bounds.muPlus * ‖x₁ - x₂‖ ^ 2 := by
      linarith
    have h := mul_nonneg (add_nonneg bounds.muPlus_pos.le bounds.muMinus_pos.le) hInner
    have hSq := sq_nonneg ‖g x₁ - g x₂ - bounds.muPlus • (x₁ - x₂)‖
    generalize g x₁ - g x₂ = u at h hSq ⊢
    generalize x₁ - x₂ = v at h hSq ⊢
    simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right] at hSq
    simp only [inner_add_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm u v]
    nlinarith only [h, hSq]
  · intro x₁ x₂
    have hInner : ⟪g x₁ - g x₂, x₁ - x₂⟫ ≤ bounds.lPlus * ‖x₁ - x₂‖ ^ 2 := by
      calc
        _ ≤ ‖g x₁ - g x₂‖ * ‖x₁ - x₂‖ := real_inner_le_norm _ _
        _ ≤ (bounds.lPlus * ‖x₁ - x₂‖) * ‖x₁ - x₂‖ :=
          mul_le_mul_of_nonneg_right (hLip x₁ x₂) (norm_nonneg _)
        _ = _ := by ring
    have h := mul_le_mul_of_nonneg_left hInner bounds.lMinus_pos.le
    have hCo := hCoco x₁ x₂
    generalize g x₁ - g x₂ = u at h hCo ⊢
    generalize x₁ - x₂ = v at h hCo ⊢
    simp only [inner_add_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm u v]
    nlinarith only [h, hCo]

end UN.Examples
