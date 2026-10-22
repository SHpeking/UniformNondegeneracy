module

public import UniformNondegeneracy.Analysis.GlobalInverse
public import UniformNondegeneracy.Analysis.SelfAdjointSpectrum
public import UniformNondegeneracy.Geometry.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section

/-!
# Spectral characterization of uniform nondegeneracy

For twice continuously differentiable energies, the UN secant inequalities are equivalent to containment of the Hessian spectrum in the curvature bands.
-/

noncomputable section

open Set Filter Topology
open scoped RealInnerProductSpace

namespace UN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {bounds : CurvatureBounds} {E : H → ℝ} {g : H → H}

/-- The Hessian is self-adjoint wherever the gradient is differentiable. -/
theorem GradientMap.hessian_selfAdjoint
    (hGrad : ∀ x, HasGradientAt E (g x) x) {x : H} (hg : DifferentiableAt ℝ g x) :
    IsSelfAdjoint (fderiv ℝ g x) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro v w
  have h := second_derivative_symmetric (fun y => (hGrad y).hasFDerivAt)
    ((InnerProductSpace.toDual ℝ H).toContinuousLinearEquiv.hasFDerivAt.comp x hg.hasFDerivAt) v w
  change ⟪(fderiv ℝ g x) v, w⟫ = ⟪(fderiv ℝ g x) w, v⟫ at h
  change ⟪(fderiv ℝ g x) v, w⟫ = ⟪v, (fderiv ℝ g x) w⟫
  exact h.trans (real_inner_comm _ _)

omit [CompleteSpace H] in
private theorem lower_bound_derivative {F : H → H} {A : H →L[ℝ] H} {x : H} {μ : ℝ}
    (hF : HasFDerivAt F A x) (hLower : ∀ x₁ x₂, μ * ‖x₁ - x₂‖ ≤ ‖F x₁ - F x₂‖) (v : H) :
    μ * ‖v‖ ≤ ‖A v‖ := by
  have hLine : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hF' : HasFDerivAt F A (x + (0 : ℝ) • v) := by simpa using hF
  have h := hF'.comp_hasDerivAt (0 : ℝ) hLine
  apply ge_of_tendsto h.tendsto_slope.norm
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := hs
  have hl := hLower (x + s • v) x
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at hl
  simp only [slope_def_module, Function.comp_apply, sub_zero, zero_smul, add_zero, norm_smul, Real.norm_eq_abs, abs_inv]
  rw [inv_mul_eq_div, le_div_iff₀ (abs_pos.mpr hs0)]
  nlinarith

omit [CompleteSpace H] in
private theorem hasFDerivAt_shift {x : H} (hg : DifferentiableAt ℝ g x) (c : ℝ) :
    HasFDerivAt (fun x => g x - c • x) (fderiv ℝ g x - algebraMap ℝ (H →L[ℝ] H) c) x := by
  change HasFDerivAt (g - c • id) (fderiv ℝ g x - algebraMap ℝ (H →L[ℝ] H) c) x
  rw [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.one_def]
  exact hg.hasFDerivAt.sub ((hasFDerivAt_id x).const_smul c)

omit [CompleteSpace H] in
private theorem shift_sub (c : ℝ) (x₁ x₂ : H) :
    (g x₁ - c • x₁) - (g x₂ - c • x₂) = g x₁ - g x₂ - c • (x₁ - x₂) := by
  module

/-- UN secant bounds place the Hessian spectrum in the same curvature bands. -/
theorem IsUN.spectral_bounds (hUN : IsUN bounds E) {x : H}
    (hg : DifferentiableAt ℝ (gradient E) x) :
    spectrum ℝ (fderiv ℝ (gradient E) x) ⊆ bounds.bands := by
  have hSym := GradientMap.hessian_selfAdjoint hUN.hasGradientAt hg
  have hInner := (SelfAdjointOperator.centered_gap_iff hSym bounds.innerCenter bounds.innerRadius_pos).mpr
    (lower_bound_derivative (hasFDerivAt_shift hg bounds.innerCenter)
      (fun x₁ x₂ => by simpa only [shift_sub] using hUN.inner_centered x₁ x₂))
  have hOuter := (SelfAdjointOperator.interval_iff hSym bounds.outerCenter bounds.outerRadius_pos.le).mpr (by
    have hNorm := (hasFDerivAt_shift hg bounds.outerCenter).le_of_lip' bounds.outerRadius_pos.le
      (Eventually.of_forall fun x₁ => by simpa only [shift_sub] using hUN.outer_centered x₁ x)
    exact (ContinuousLinearMap.opNorm_le_iff bounds.outerRadius_pos.le).mp hNorm)
  intro σ hσ
  exact (bounds.mem_bands_iff_centered σ).mpr ⟨hOuter σ hσ, hInner σ hσ⟩

private theorem lower_secant_of_derivative_bound
    (hg : ContDiff ℝ 1 g) (hSym : ∀ x, IsSelfAdjoint (fderiv ℝ g x))
    (c : ℝ) {r : ℝ} (hr : 0 < r)
    (hLower : ∀ x v, r * ‖v‖ ≤ ‖(fderiv ℝ g x) v - c • v‖) (x₁ x₂ : H) :
    r * ‖x₁ - x₂‖ ≤ ‖g x₁ - g x₂ - c • (x₁ - x₂)‖ := by
  let B (x : H) := fderiv ℝ g x - algebraMap ℝ (H →L[ℝ] H) c
  have hUnit (x : H) : IsUnit (B x) :=
    SelfAdjointOperator.isUnit_of_lower_bound
      ((hSym x).sub (by simp [IsSelfAdjoint, Algebra.algebraMap_eq_smul_one])) hr (hLower x)
  let A (x : H) := ContinuousLinearEquiv.ofUnit (hUnit x).unit
  have hA (x : H) : (A x : H →L[ℝ] H) = B x := (hUnit x).unit_spec
  have hDeriv (x : H) : HasFDerivAt (fun x => g x - c • x) (A x : H →L[ℝ] H) x := by
    rw [hA]
    exact hasFDerivAt_shift (hg.differentiable one_ne_zero x) c
  have hBound (x : H) : ‖(A x).symm.toContinuousLinearMap‖ ≤ (⟨r⁻¹, inv_nonneg.mpr hr.le⟩ : NNReal) := by
    apply (A x).symm.toContinuousLinearMap.opNorm_le_bound (inv_nonneg.mpr hr.le)
    intro v
    have h := hLower x ((A x).symm v)
    change r * ‖(A x).symm v‖ ≤ ‖(B x) ((A x).symm v)‖ at h
    rw [← hA] at h
    change r * ‖(A x).symm v‖ ≤ ‖(A x) ((A x).symm v)‖ at h
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    change ‖(A x).symm v‖ ≤ r⁻¹ * ‖v‖
    rw [inv_mul_eq_div, le_div_iff₀ hr]
    simpa only [mul_comm] using h
  have hCont : ContDiff ℝ 1 (fun x => g x - c • x) := hg.sub (contDiff_id.const_smul c)
  have h := (GlobalInverse.bijective_and_antilipschitz hCont hDeriv hBound).2.le_mul_dist x₁ x₂
  simp only [dist_eq_norm, shift_sub] at h
  change ‖x₁ - x₂‖ ≤ r⁻¹ * ‖g x₁ - g x₂ - c • (x₁ - x₂)‖ at h
  rw [inv_mul_eq_div, le_div_iff₀ hr] at h
  simpa only [mul_comm] using h

/-- Spectral bounds on a continuously differentiable gradient imply the global UN secant inequalities. -/
theorem GradientMap.isUN_of_spectral_bounds
    (hGrad : ∀ x, HasGradientAt E (g x) x) (hg : ContDiff ℝ 1 g)
    (hSpectrum : ∀ x, spectrum ℝ (fderiv ℝ g x) ⊆ bounds.bands) :
    IsUN bounds E := by
  have hSym (x : H) := GradientMap.hessian_selfAdjoint hGrad (hg.differentiable one_ne_zero x)
  have hInner (x : H) := (SelfAdjointOperator.centered_gap_iff (hSym x) bounds.innerCenter bounds.innerRadius_pos).mp
    (fun σ hσ => ((bounds.mem_bands_iff_centered σ).mp (hSpectrum x hσ)).2)
  have hOuter (x : H) := (SelfAdjointOperator.interval_iff (hSym x) bounds.outerCenter bounds.outerRadius_pos.le).mp
    (fun σ hσ => ((bounds.mem_bands_iff_centered σ).mp (hSpectrum x hσ)).1)
  apply IsUN.of_hasGradient hGrad
  · intro x₁ x₂
    have h := lower_secant_of_derivative_bound hg hSym bounds.innerCenter bounds.innerRadius_pos hInner x₁ x₂
    rw [← centered_secant_identity]
    change 0 ≤ ‖g x₁ - g x₂ - bounds.innerCenter • (x₁ - x₂)‖ ^ 2 - bounds.innerRadius ^ 2 * ‖x₁ - x₂‖ ^ 2
    nlinarith [mul_nonneg bounds.innerRadius_pos.le (norm_nonneg (x₁ - x₂))]
  · intro x₁ x₂
    have h := (convex_univ : Convex ℝ (univ : Set H)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x _ => (hasFDerivAt_shift (hg.differentiable one_ne_zero x) bounds.outerCenter).hasFDerivWithinAt)
      (fun x _ => ContinuousLinearMap.opNorm_le_bound _ bounds.outerRadius_pos.le (hOuter x))
      (mem_univ x₂) (mem_univ x₁)
    rw [shift_sub] at h
    rw [← centered_secant_identity]
    change ‖g x₁ - g x₂ - bounds.outerCenter • (x₁ - x₂)‖ ^ 2 - bounds.outerRadius ^ 2 * ‖x₁ - x₂‖ ^ 2 ≤ 0
    nlinarith [norm_nonneg (g x₁ - g x₂ - bounds.outerCenter • (x₁ - x₂))]

/-- For a C² energy, centered squared secant bounds are equivalent to the corresponding Hessian spectral bounds. -/
theorem centered_secant_iff_spectral_bounds (hE : ContDiff ℝ 2 E) (c a : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    (∀ x₁ x₂, a * ‖x₁ - x₂‖ ^ 2 ≤ ‖gradient E x₁ - gradient E x₂ - c • (x₁ - x₂)‖ ^ 2 ∧
      ‖gradient E x₁ - gradient E x₂ - c • (x₁ - x₂)‖ ^ 2 ≤ R ^ 2 * ‖x₁ - x₂‖ ^ 2) ↔
    (∀ x σ, σ ∈ spectrum ℝ (fderiv ℝ (gradient E) x) → a ≤ (σ - c) ^ 2 ∧ (σ - c) ^ 2 ≤ R ^ 2) := by
  have hg := contDiff_gradient hE
  have hGrad := fun x => (hE.differentiable (by norm_num) x).hasGradientAt
  have hSym (x : H) := GradientMap.hessian_selfAdjoint hGrad (hg.differentiable one_ne_zero x)
  constructor
  · intro hSecant
    have hUpper (x₁ x₂ : H) : ‖gradient E x₁ - gradient E x₂ - c • (x₁ - x₂)‖ ≤ R * ‖x₁ - x₂‖ := by
      have h := (hSecant x₁ x₂).2
      nlinarith [norm_nonneg (gradient E x₁ - gradient E x₂ - c • (x₁ - x₂)), mul_nonneg hR (norm_nonneg (x₁ - x₂))]
    intro x σ hσ
    have hInterval := (SelfAdjointOperator.interval_iff (hSym x) c hR).mpr (by
      have hNorm := (hasFDerivAt_shift (hg.differentiable one_ne_zero x) c).le_of_lip' hR
        (Eventually.of_forall fun x₁ => by simpa only [shift_sub] using hUpper x₁ x)
      exact (ContinuousLinearMap.opNorm_le_iff hR).mp hNorm)
    refine ⟨?_, ?_⟩
    · by_cases ha : 0 < a
      · have hLower (x₁ x₂ : H) : Real.sqrt a * ‖x₁ - x₂‖ ≤ ‖gradient E x₁ - gradient E x₂ - c • (x₁ - x₂)‖ := by
          have h := (hSecant x₁ x₂).1
          have hs := Real.sq_sqrt ha.le
          nlinarith [norm_nonneg (gradient E x₁ - gradient E x₂ - c • (x₁ - x₂)), mul_nonneg (Real.sqrt_nonneg a) (norm_nonneg (x₁ - x₂))]
        have hGap := (SelfAdjointOperator.centered_gap_iff (hSym x) c (Real.sqrt_pos.mpr ha)).mpr
          (lower_bound_derivative (hasFDerivAt_shift (hg.differentiable one_ne_zero x) c)
            (fun x₁ x₂ => by simpa only [shift_sub] using hLower x₁ x₂))
        have h := hGap σ hσ
        nlinarith [Real.sq_sqrt ha.le, sq_abs (σ - c), Real.sqrt_nonneg a]
      · exact (le_of_not_gt ha).trans (sq_nonneg _)
    · have h := hInterval σ hσ
      nlinarith [sq_abs (σ - c), abs_nonneg (σ - c)]
  · intro hSpectrum
    have hUpper (x : H) := (SelfAdjointOperator.interval_iff (hSym x) c hR).mp (by
      intro σ hσ
      have h := (hSpectrum x σ hσ).2
      nlinarith [sq_abs (σ - c), abs_nonneg (σ - c)])
    intro x₁ x₂
    refine ⟨?_, ?_⟩
    · by_cases ha : 0 < a
      · have hLower (x : H) := (SelfAdjointOperator.centered_gap_iff (hSym x) c (Real.sqrt_pos.mpr ha)).mp (by
          intro σ hσ
          have h := (hSpectrum x σ hσ).1
          nlinarith [Real.sq_sqrt ha.le, sq_abs (σ - c), abs_nonneg (σ - c), Real.sqrt_nonneg a])
        have h := lower_secant_of_derivative_bound hg hSym c (Real.sqrt_pos.mpr ha) hLower x₁ x₂
        have hs := Real.sq_sqrt ha.le
        nlinarith [norm_nonneg (gradient E x₁ - gradient E x₂ - c • (x₁ - x₂)), mul_nonneg (Real.sqrt_nonneg a) (norm_nonneg (x₁ - x₂))]
      · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt ha) (sq_nonneg _)).trans (sq_nonneg _)
    · have h := (convex_univ : Convex ℝ (univ : Set H)).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun x _ => (hasFDerivAt_shift (hg.differentiable one_ne_zero x) c).hasFDerivWithinAt)
        (fun x _ => ContinuousLinearMap.opNorm_le_bound _ hR (hUpper x)) (mem_univ x₂) (mem_univ x₁)
      rw [shift_sub] at h
      nlinarith [norm_nonneg (gradient E x₁ - gradient E x₂ - c • (x₁ - x₂)), mul_nonneg hR (norm_nonneg (x₁ - x₂))]

/-- Hessian spectral bounds imply UN for a twice continuously differentiable energy. -/
theorem isUN_of_spectral_bounds (hE : ContDiff ℝ 2 E)
    (hSpectrum : ∀ x, spectrum ℝ (fderiv ℝ (gradient E) x) ⊆ bounds.bands) :
    IsUN bounds E := by
  have hGrad := fun x => (hE.differentiable (by norm_num) x).hasGradientAt
  exact GradientMap.isUN_of_spectral_bounds hGrad (contDiff_gradient hE) hSpectrum

/-- A twice continuously differentiable energy is UN exactly when its Hessian spectrum lies in the curvature bands. -/
theorem isUN_iff_spectral_bounds (hE : ContDiff ℝ 2 E) :
    IsUN bounds E ↔ ∀ x, spectrum ℝ (fderiv ℝ (gradient E) x) ⊆ bounds.bands := by
  have hg := contDiff_gradient hE
  exact ⟨fun hUN x => hUN.spectral_bounds (hg.differentiable one_ne_zero x), isUN_of_spectral_bounds hE⟩

/-- For a linear gradient, UN follows from a single operator spectrum. -/
theorem isUN_of_linear_gradient {A : H →L[ℝ] H}
    (hGrad : ∀ x, HasGradientAt E (A x) x) (hSpectrum : spectrum ℝ A ⊆ bounds.bands) :
    IsUN bounds E := by
  apply GradientMap.isUN_of_spectral_bounds hGrad A.contDiff
  intro x
  simpa only [A.fderiv] using hSpectrum

/-- A self-adjoint quadratic is UN when its operator spectrum lies in the curvature bands. -/
theorem SelfAdjointOperator.quadratic_isUN {A : H →L[ℝ] H}
    (hA : IsSelfAdjoint A) (hSpectrum : spectrum ℝ A ⊆ bounds.bands) :
    IsUN bounds (fun x => (1 / 2 : ℝ) * ⟪A x, x⟫) := by
  apply isUN_of_linear_gradient (hSpectrum := hSpectrum)
  intro x
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (A.hasFDerivAt.inner ℝ (hasFDerivAt_id x)).const_mul (1 / 2 : ℝ) using 1
  · rfl
  · ext v
    change ⟪A x, v⟫ = (1 / 2 : ℝ) * (⟪A x, v⟫ + ⟪A v, x⟫)
    have h := hA.isSymmetric v x
    change ⟪A v, x⟫ = ⟪v, A x⟫ at h
    rw [h, real_inner_comm v (A x)]
    ring

end UN
