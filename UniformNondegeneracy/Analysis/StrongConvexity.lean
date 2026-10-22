module

public import UniformNondegeneracy.Analysis.GradientBounds
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-!
# Strong convexity and gradient secants

Strong convexity and a Lipschitz gradient give quadratic Bregman bounds and cocoercivity after subtracting the strong convexity modulus.
-/

open scoped RealInnerProductSpace

namespace UN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {E : H → ℝ} {μ L : ℝ}

local notation "g" => gradient E

/-- Strong convexity gives a quadratic lower bound on the Bregman difference. -/
theorem strongConvexOn_bregman_lower
    (hE : Differentiable ℝ E) (hStrong : StrongConvexOn Set.univ μ E)
    (x₁ x₂ : H) :
    μ / 2 * ‖x₁ - x₂‖ ^ 2 ≤ bregman E x₁ x₂ := by
  have hGrad (x : H) := (hE x).hasGradientAt
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

/-- Strong convexity and smoothness bound the Bregman difference from both sides. -/
theorem strongConvexOn_hasBregmanBounds
    (hE : Differentiable ℝ E) (hStrong : StrongConvexOn Set.univ μ E)
    (hLip : ∀ x₁ x₂, ‖g x₁ - g x₂‖ ≤ L * ‖x₁ - x₂‖) :
    HasBregmanBounds L (-μ) E := by
  constructor
  · intro x₁ x₂
    simpa only [neg_div, neg_neg] using strongConvexOn_bregman_lower hE hStrong x₁ x₂
  · intro x₁ x₂
    simpa [bregman] using
      (abs_le.mp (GradientMap.abs_taylor_remainder_le E g L (fun x => (hE x).hasGradientAt) hLip x₂ (x₁ - x₂))).2

/-- Subtracting the strong convexity modulus gives the sharp cocoercivity estimate. -/
theorem strongConvexOn_cocoercive (hμL : μ ≤ L)
    (hE : Differentiable ℝ E) (hStrong : StrongConvexOn Set.univ μ E)
    (hLip : ∀ x₁ x₂, ‖g x₁ - g x₂‖ ≤ L * ‖x₁ - x₂‖) (x₁ x₂ : H) :
    ‖g x₁ - g x₂ - μ • (x₁ - x₂)‖ ^ 2 ≤
      (L - μ) * ⟪g x₁ - g x₂ - μ • (x₁ - x₂), x₁ - x₂⟫ := by
  have h := (strongConvexOn_hasBregmanBounds hE hStrong hLip).outer_secant (by linarith) x₁ x₂
  simp only [neg_smul, ← sub_eq_add_neg] at h
  have hSplit : g x₁ - g x₂ - L • (x₁ - x₂) =
      (g x₁ - g x₂ - μ • (x₁ - x₂)) - (L - μ) • (x₁ - x₂) := by module
  rw [hSplit, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_smul_right] at h
  linarith

end UN
