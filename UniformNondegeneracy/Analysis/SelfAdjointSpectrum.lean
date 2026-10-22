module

public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Spectral bounds for self-adjoint operators

Spectral intervals and gaps correspond to upper and lower norm bounds. Scalar shifts give the corresponding centered inequalities.
-/

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace

namespace UN.SelfAdjointOperator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {A : H →L[ℝ] H}

omit [CompleteSpace H] in
/-- A symmetric operator is bounded by its quadratic form on unit vectors. -/
theorem norm_le_of_unit_inner {T : H →L[ℝ] H} (hT : T.IsSymmetric) {C : ℝ} (hC : 0 ≤ C)
    (hBound : ∀ h, ‖h‖ = 1 → |⟪T h, h⟫| ≤ C) :
    ‖T‖ ≤ C := by
  rw [T.norm_eq_iSup_rayleighQuotient hT]
  apply ciSup_le
  intro h
  by_cases hh : h = 0
  · simpa [hh] using hC
  have hn : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh
  have hu : ‖‖h‖⁻¹ • h‖ = 1 := by simp [norm_smul, hn]
  rw [← T.rayleigh_smul h (inv_ne_zero hn)]
  simpa only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real, hu, one_pow, div_one] using hBound (‖h‖⁻¹ • h) hu

/-- A self-adjoint operator has norm at most `L` exactly when its spectrum lies in `[-L, L]`. -/
theorem norm_le_iff (hA : IsSelfAdjoint A) {L : ℝ} (hL : 0 ≤ L) :
    ‖A‖ ≤ L ↔ ∀ σ ∈ spectrum ℝ A, |σ| ≤ L := by
  constructor
  · intro h σ hσ
    have hσ' := quasispectrum.norm_le_norm_of_mem (spectrum_subset_quasispectrum ℝ A hσ)
    calc
      |σ| ≤ ‖A‖ := by simpa only [Real.norm_eq_abs] using hσ'
      _ ≤ L := h
  · intro h
    have hRadius : spectralRadius ℝ A ≤ ENNReal.ofReal L := by
      rw [spectralRadius_eq_of_unital]
      refine iSup₂_le fun σ hσ => ?_
      have hσ' : ‖σ‖ ≤ L := by simpa only [Real.norm_eq_abs] using h σ hσ
      simpa only [ofReal_norm, enorm_eq_nnnorm] using ENNReal.ofReal_le_ofReal hσ'
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hRadius
    simpa only [A.spectralRadius_eq_nnnorm hA, ENNReal.coe_toReal, coe_nnnorm, ENNReal.toReal_ofReal hL] using h

/-- A positive lower norm bound makes a self-adjoint operator invertible. -/
theorem isUnit_of_lower_bound (hA : IsSelfAdjoint A) {μ : ℝ} (hμ : 0 < μ)
    (hLower : ∀ v, μ * ‖v‖ ≤ ‖A v‖) :
    IsUnit A := by
  have hAnti : AntilipschitzWith ⟨μ⁻¹, inv_nonneg.mpr hμ.le⟩ A :=
    A.antilipschitz_of_bound fun v => by
      change ‖v‖ ≤ μ⁻¹ * ‖A v‖
      rw [inv_mul_eq_div, le_div_iff₀ hμ]
      simpa only [mul_comm] using hLower v
  rw [ContinuousLinearMap.isUnit_iff_bijective, A.bijective_iff_dense_range_and_antilipschitz]
  refine ⟨?_, ⟨_, hAnti⟩⟩
  rw [Submodule.topologicalClosure_eq_top_iff, hA.isSymmetric.orthogonal_range]
  exact LinearMap.ker_eq_bot.mpr hAnti.injective

/-- Every spectral value admits unit vectors with arbitrarily small eigenvector residual. -/
theorem exists_unit_approx_eigenvector (hA : IsSelfAdjoint A) {σ : ℝ}
    (hσ : σ ∈ spectrum ℝ A) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : H, ‖v‖ = 1 ∧ ‖A v - σ • v‖ < ε := by
  by_contra! h
  have hLower (v : H) : ε * ‖v‖ ≤ ‖A v - σ • v‖ := by
    by_cases hv : v = 0
    · simp [hv]
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hunit : ‖‖v‖⁻¹ • v‖ = 1 := by simp [norm_smul, hn]
    have hh := h (‖v‖⁻¹ • v) hunit
    rw [map_smul, smul_comm σ, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _), inv_mul_eq_div] at hh
    exact (le_div_iff₀ (norm_pos_iff.mpr hv)).mp hh
  have hShift : IsSelfAdjoint (A - algebraMap ℝ (H →L[ℝ] H) σ) :=
    hA.sub (by simp [IsSelfAdjoint, Algebra.algebraMap_eq_smul_one])
  have hUnit := isUnit_of_lower_bound hShift hε hLower
  apply (spectrum.notMem_iff.mpr ?_) hσ
  rw [← neg_sub A]
  exact hUnit.neg

/-- A spectral value admits unit vectors whose eigenvector residual tends to zero. -/
theorem exists_approx_eigenvectors (hA : IsSelfAdjoint A) {σ : ℝ}
    (hσ : σ ∈ spectrum ℝ A) :
    ∃ v : ℕ → H, (∀ n, ‖v n‖ = 1) ∧ Tendsto (fun n => A (v n) - σ • v n) atTop (𝓝 0) := by
  have h (n : ℕ) := exists_unit_approx_eigenvector hA hσ (show 0 < 1 / ((n : ℝ) + 1) by positivity)
  choose v hv hsmall using h
  refine ⟨v, hv, squeeze_zero_norm (fun n => (hsmall n).le) tendsto_one_div_add_atTop_nhds_zero_nat⟩

/-- A nonnegative quadratic form in a self-adjoint operator is nonnegative on its spectrum. -/
theorem quadratic_nonneg_on_spectrum (hA : IsSelfAdjoint A) {σ : ℝ} (hσ : σ ∈ spectrum ℝ A)
    {a b c : ℝ} (hBound : ∀ v, 0 ≤ a * ‖A v‖ ^ 2 + b * ⟪A v, v⟫ + c * ‖v‖ ^ 2) :
    0 ≤ a * σ ^ 2 + b * σ + c := by
  obtain ⟨v, hv, hResidual⟩ := exists_approx_eigenvectors hA hσ
  have hNorm : Tendsto (fun n => ‖A (v n) - σ • v n‖) atTop (𝓝 0) := by
    simpa using hResidual.norm
  have hInner : Tendsto (fun n => ⟪A (v n) - σ • v n, v n⟫) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ hNorm
    intro n
    simpa [hv n] using abs_real_inner_le_norm (A (v n) - σ • v n) (v n)
  have hRayleigh : Tendsto (fun n => ⟪A (v n), v n⟫) atTop (𝓝 σ) := by
    convert hInner.add_const σ using 1
    · ext n
      simp [inner_sub_left, real_inner_smul_left, hv n]
    · simp
  have hSquare : Tendsto (fun n => ‖A (v n)‖ ^ 2) atTop (𝓝 (σ ^ 2)) := by
    convert ((hNorm.pow 2).add (hRayleigh.const_mul (2 * σ))).sub_const (σ ^ 2) using 1
    · ext n
      simp [norm_sub_sq_real, norm_smul, real_inner_smul_right, hv n, Real.norm_eq_abs, sq_abs]
      ring
    · congr 1
      ring
  have h := ((hSquare.const_mul a).add (hRayleigh.const_mul b)).add_const c
  apply ge_of_tendsto h
  filter_upwards [] with n
  simpa only [hv n, one_pow, mul_one] using hBound (v n)

/-- A spectral gap bounds the inverse operator norm. -/
theorem inverse_norm_le (hA : IsSelfAdjoint A) {μ : ℝ} (hμ : 0 < μ)
    (hGap : ∀ σ ∈ spectrum ℝ A, μ ≤ |σ|) :
    IsUnit A ∧ ‖Ring.inverse A‖ ≤ μ⁻¹ := by
  have hUnit : IsUnit A := spectrum.isUnit_of_zero_notMem ℝ (by
    intro h
    have := hGap 0 h
    simp only [abs_zero] at this
    linarith)
  refine ⟨hUnit, (norm_le_iff hA.ringInverse (inv_nonneg.mpr hμ.le)).mpr ?_⟩
  intro σ hσ
  have hInv : Ring.inverse A = ↑hUnit.unit⁻¹ := Ring.inverse_unit hUnit.unit
  rw [hInv] at hσ
  have hσ0 : σ ≠ 0 := spectrum.ne_zero_of_mem_of_unit hσ
  have hσ' : σ⁻¹ ∈ spectrum ℝ A := by
    simpa only [hUnit.unit_spec] using spectrum.inv₀_mem_iff.mpr hσ
  have h := hGap σ⁻¹ hσ'
  rw [abs_inv] at h
  exact (le_inv_comm₀ (abs_pos.mpr hσ0) hμ).mpr h

/-- A spectral gap is equivalent to the corresponding lower norm bound. -/
theorem gap_iff (hA : IsSelfAdjoint A) {μ : ℝ} (hμ : 0 < μ) :
    (∀ σ ∈ spectrum ℝ A, μ ≤ |σ|) ↔ ∀ v, μ * ‖v‖ ≤ ‖A v‖ := by
  constructor
  · intro hGap v
    obtain ⟨hUnit, hInv⟩ := inverse_norm_le hA hμ hGap
    have h := (Ring.inverse A).le_opNorm (A v)
    have hCancel : (Ring.inverse A) (A v) = v := by
      have := congrArg (fun T : H →L[ℝ] H => T v) (Ring.inverse_mul_cancel A hUnit)
      simpa using this
    rw [hCancel] at h
    have h' := h.trans (mul_le_mul_of_nonneg_right hInv (norm_nonneg _))
    rw [inv_mul_eq_div, le_div_iff₀ hμ] at h'
    simpa only [mul_comm] using h'
  · intro hLower σ hσ
    by_contra! hlt
    have hShift : IsSelfAdjoint (A - algebraMap ℝ (H →L[ℝ] H) σ) :=
      hA.sub (by simp [IsSelfAdjoint, Algebra.algebraMap_eq_smul_one])
    have hUnit := isUnit_of_lower_bound hShift (sub_pos.mpr hlt) (fun v => by
      have ht := norm_add_le (A v - σ • v) (σ • v)
      rw [sub_add_cancel, norm_smul, Real.norm_eq_abs] at ht
      have hl := hLower v
      simp only [sub_apply, ContinuousLinearMap.algebraMap_apply]
      nlinarith)
    apply (spectrum.notMem_iff.mpr ?_) hσ
    rw [← neg_sub A]
    exact hUnit.neg

omit [CompleteSpace H] in
private theorem mem_spectrum_sub_iff (c σ : ℝ) :
    σ ∈ spectrum ℝ (A - algebraMap ℝ (H →L[ℝ] H) c) ↔ σ + c ∈ spectrum ℝ A := by
  simpa only [sub_eq_add_neg, add_comm] using (spectrum.add_mem_iff (a := A) (r := σ) (s := c)).symm

/-- A spectral interval is equivalent to an upper bound after subtracting its center. -/
theorem interval_iff (hA : IsSelfAdjoint A) (c : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (∀ σ ∈ spectrum ℝ A, |σ - c| ≤ r) ↔ ∀ v, ‖A v - c • v‖ ≤ r * ‖v‖ := by
  have hShift : IsSelfAdjoint (A - algebraMap ℝ (H →L[ℝ] H) c) :=
    hA.sub (by simp [IsSelfAdjoint, Algebra.algebraMap_eq_smul_one])
  change _ ↔ ∀ v, ‖(A - algebraMap ℝ (H →L[ℝ] H) c) v‖ ≤ r * ‖v‖
  rw [← ContinuousLinearMap.opNorm_le_iff hr, norm_le_iff hShift hr]
  constructor
  · intro h σ hσ
    simpa only [add_sub_cancel_right] using h (σ + c) ((mem_spectrum_sub_iff c σ).mp hσ)
  · intro h σ hσ
    apply h (σ - c)
    exact (mem_spectrum_sub_iff c (σ - c)).mpr (by simpa using hσ)

/-- A spectral gap is equivalent to a lower bound after subtracting its center. -/
theorem centered_gap_iff (hA : IsSelfAdjoint A) (c : ℝ) {r : ℝ} (hr : 0 < r) :
    (∀ σ ∈ spectrum ℝ A, r ≤ |σ - c|) ↔ ∀ v, r * ‖v‖ ≤ ‖A v - c • v‖ := by
  have hShift : IsSelfAdjoint (A - algebraMap ℝ (H →L[ℝ] H) c) :=
    hA.sub (by simp [IsSelfAdjoint, Algebra.algebraMap_eq_smul_one])
  change _ ↔ ∀ v, r * ‖v‖ ≤ ‖(A - algebraMap ℝ (H →L[ℝ] H) c) v‖
  rw [← gap_iff hShift hr]
  constructor
  · intro h σ hσ
    simpa only [add_sub_cancel_right] using h (σ + c) ((mem_spectrum_sub_iff c σ).mp hσ)
  · intro h σ hσ
    apply h (σ - c)
    exact (mem_spectrum_sub_iff c (σ - c)).mpr (by simpa using hσ)

end UN.SelfAdjointOperator
