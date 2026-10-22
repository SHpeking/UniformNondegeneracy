module

public import UniformNondegeneracy.Geometry.Spectral
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Eigenspace.Matrix

@[expose] public section

/-!
# Scalar and diagonal quadratic energies

The general theorem for self-adjoint quadratics gives UN for scalar and diagonal coefficients in the curvature bands.
-/

open scoped RealInnerProductSpace

namespace UN.Examples

noncomputable section

variable {bounds : CurvatureBounds}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A scalar quadratic is UN when its curvature lies in the prescribed bands. -/
theorem scalar_quadratic_isUN {σ : ℝ} (hσ : σ ∈ bounds.bands) :
    IsUN bounds (fun x : H => σ / 2 * ‖x‖ ^ 2) := by
  let A := algebraMap ℝ (H →L[ℝ] H) σ
  have hA : IsSelfAdjoint A := (IsSelfAdjoint.all σ).algebraMap _
  have hSpectrum : spectrum ℝ A ⊆ bounds.bands := by
    calc
      spectrum ℝ (algebraMap ℝ (H →L[ℝ] H) σ) ⊆ spectrum ℝ σ :=
        AlgHom.spectrum_apply_subset (Algebra.ofId ℝ (H →L[ℝ] H)) σ
      _ = {σ} := spectrum.scalar_eq (A := ℝ) σ
      _ ⊆ bounds.bands := Set.singleton_subset_iff.mpr hσ
  convert SelfAdjointOperator.quadratic_isUN hA hSpectrum using 1
  funext x
  simp only [A, ContinuousLinearMap.algebraMap_apply, real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

variable {d : ℕ}

/-- The diagonal quadratic with coefficients `σ`. -/
def diagonalQuadratic (σ : Fin d → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, σ i * x i ^ 2

/-- A diagonal quadratic is UN when every coefficient lies in the prescribed bands. -/
theorem diagonalQuadratic_isUN {σ : Fin d → ℝ} (hσ : ∀ i, σ i ∈ bounds.bands) :
    IsUN bounds (diagonalQuadratic σ) := by
  let A := (Matrix.toEuclideanLin (Matrix.diagonal σ)).toContinuousLinearMap
  have hA : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_diagonal σ))
  have hSpectrum : spectrum ℝ A ⊆ bounds.bands := by
    rw [ContinuousLinearMap.spectrum_eq]
    change spectrum ℝ (Matrix.toEuclideanLin (Matrix.diagonal σ)) ⊆ bounds.bands
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.spectrum_toLin, spectrum_diagonal]
    exact Set.range_subset_iff.mpr hσ
  convert SelfAdjointOperator.quadratic_isUN hA hSpectrum using 1
  funext x
  simp [A, diagonalQuadratic, Matrix.toEuclideanLin, Matrix.toLpLin_apply, PiLp.inner_apply, Matrix.mulVec_diagonal, pow_two, mul_left_comm]

end
end UN.Examples
