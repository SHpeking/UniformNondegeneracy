module

public import UniformNondegeneracy.Core.Basic
public import UniformNondegeneracy.Analysis.Taylor

@[expose] public section

/-!
# Scalar and diagonal quadratic energies

Uniform nondegeneracy follows from membership of the quadratic coefficients in the curvature bands.
-/

open scoped RealInnerProductSpace

namespace UN.Examples

noncomputable section

variable {bounds : CurvatureBounds}

private theorem scalar_secant_bounds {σ : ℝ} (hσ : σ ∈ bounds.bands) :
    0 ≤ (σ + bounds.muMinus) * (σ - bounds.muPlus) ∧
    (σ + bounds.lMinus) * (σ - bounds.lPlus) ≤ 0 := by
  rcases hσ with ⟨hLower, hUpper⟩ | ⟨hLower, hUpper⟩
  · constructor
    · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [bounds.muMinus_pos, bounds.muPlus_pos])
    · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith [bounds.muMinus_pos, bounds.lPlus_pos])
  · constructor
    · exact mul_nonneg (by linarith [bounds.muMinus_pos, bounds.muPlus_pos]) (by linarith)
    · exact mul_nonpos_of_nonneg_of_nonpos (by linarith [bounds.muPlus_pos, bounds.lMinus_pos]) (by linarith)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A scalar quadratic is UN when its curvature lies in the prescribed bands. -/
theorem scalar_quadratic_isUN {σ : ℝ} (hσ : σ ∈ bounds.bands) :
    IsUN bounds (fun x : H => σ / 2 * ‖x‖ ^ 2) (fun x => σ • x) := by
  obtain ⟨hInner, hOuter⟩ := scalar_secant_bounds hσ
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simpa only [sub_zero] using hasGradientAt_quadratic σ (0 : H) x
  · intro x₁ x₂
    simpa only [← smul_sub, ← add_smul, ← sub_smul, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, mul_assoc, mul_left_comm] using
      mul_nonneg hInner (sq_nonneg ‖x₁ - x₂‖)
  · intro x₁ x₂
    simpa only [← smul_sub, ← add_smul, ← sub_smul, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, mul_assoc, mul_left_comm] using
      mul_nonpos_of_nonpos_of_nonneg hOuter (sq_nonneg ‖x₁ - x₂‖)

variable {d : ℕ}

/-- The diagonal quadratic with coefficients `σ`. -/
def diagonalQuadratic (σ : Fin d → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, σ i * x i ^ 2

/-- The diagonal linear map with coefficients `σ`. -/
def diagonalGradient (σ : Fin d → ℝ) (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => σ i * x i)

theorem hasGradientAt_diagonalQuadratic (σ : Fin d → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    HasGradientAt (diagonalQuadratic σ) (diagonalGradient σ x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hCoord (i : Fin d) :=
    (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).hasFDerivAt (x := x)).pow 2).const_mul (σ i)
  convert (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hCoord i)).const_mul (1 / 2 : ℝ) using 1
  · rfl
  · ext v
    simp [InnerProductSpace.toDual_apply_apply, PiLp.inner_apply, diagonalGradient, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

private theorem diagonal_secant (σ : Fin d → ℝ) (a b : ℝ) (x₁ x₂ : EuclideanSpace ℝ (Fin d)) :
    ⟪diagonalGradient σ x₁ - diagonalGradient σ x₂ + b • (x₁ - x₂), diagonalGradient σ x₁ - diagonalGradient σ x₂ - a • (x₁ - x₂)⟫ =
      ∑ i, (σ i + b) * (σ i - a) * (x₁ i - x₂ i) ^ 2 := by
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simp [diagonalGradient]
  ring

/-- A diagonal quadratic is UN when every coefficient lies in the prescribed bands. -/
theorem diagonalQuadratic_isUN {σ : Fin d → ℝ} (hσ : ∀ i, σ i ∈ bounds.bands) :
    IsUN bounds (diagonalQuadratic σ) (diagonalGradient σ) := by
  refine ⟨hasGradientAt_diagonalQuadratic σ, ?_, ?_⟩
  · intro x₁ x₂
    rw [diagonal_secant]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (scalar_secant_bounds (hσ i)).1 (sq_nonneg _))
  · intro x₁ x₂
    rw [diagonal_secant]
    exact Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonpos_of_nonneg (scalar_secant_bounds (hσ i)).2 (sq_nonneg _))

end
end UN.Examples
