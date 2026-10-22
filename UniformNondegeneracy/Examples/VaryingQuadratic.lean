module

public import UniformNondegeneracy.Geometry.Limits
public import UniformNondegeneracy.Geometry.Spectral
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Star

@[expose] public section

/-!
# Radially varying quadratic forms

A self-adjoint operator family whose spectral gap dominates its radial variation defines a UN energy. Rotating quadratic forms are a special case.
-/

noncomputable section

open Set Filter Topology InnerProductSpace
open scoped RealInnerProductSpace

namespace UN.Examples

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The energy `E(x) = Q_{‖x‖}(x)` from the quadratic forms `Qᵣ(v) = ⟪A(r)v,v⟫ / 2`. -/
def varyingQuadratic (A : ℝ → H →L[ℝ] H) (x : H) : ℝ :=
  (1 / 2 : ℝ) * ⟪A ‖x‖ x, x⟫

@[simp] theorem varyingQuadratic_zero (A : ℝ → H →L[ℝ] H) : varyingQuadratic A 0 = 0 := by
  simp [varyingQuadratic]

/-- The Hessian perturbation bound from the first two radial derivatives. -/
def radialVariation (A : ℝ → H →L[ℝ] H) (r : ℝ) : ℝ :=
  2 * r * ‖deriv A r‖ + r ^ 2 / 2 * ‖deriv (deriv A) r‖

/-- Regularization of the energy by replacing `‖x‖` with `√(‖x‖² + ε²)`. -/
def VaryingQuadratic.regularizedEnergy (A : ℝ → H →L[ℝ] H) (ε : ℝ) (x : H) : ℝ :=
  (1 / 2 : ℝ) * ⟪A (Real.sqrt (‖x‖ ^ 2 + ε ^ 2)) x, x⟫

/-- The Hessian of the regularized energy for a C² self-adjoint family and `ε > 0`. -/
def VaryingQuadratic.regularizedHessian (A : ℝ → H →L[ℝ] H) (ε : ℝ) (x : H) : H →L[ℝ] H :=
  let R := Real.sqrt (‖x‖ ^ 2 + ε ^ 2)
  let v := R⁻¹ • x
  A R + R • (rankOne ℝ (deriv A R v) v + rankOne ℝ v (deriv A R v) +
    (⟪v, deriv A R v⟫ / 2) • (1 - rankOne ℝ v v)) +
    (R ^ 2 / 2 * ⟪v, deriv (deriv A) R v⟫) • rankOne ℝ v v

open VaryingQuadratic

private def radialCorrection (B : H →L[ℝ] H) (v : H) : H →L[ℝ] H :=
  rankOne ℝ (B v) v + rankOne ℝ v (B v) + (⟪v, B v⟫ / 2) • (1 - rankOne ℝ v v)

private lemma radialCorrection_symmetric (B : H →L[ℝ] H) (v : H) :
    (radialCorrection B v).IsSymmetric := by
  intro x y
  simp only [radialCorrection, ContinuousLinearMap.coe_coe, add_apply, smul_apply, sub_apply, one_apply_eq_self, rankOne_apply]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm]
  ring

private lemma norm_radialCorrection_le (B : H →L[ℝ] H) {v : H} (hv : ‖v‖ ≤ 1) :
    ‖radialCorrection B v‖ ≤ 2 * ‖B‖ := by
  apply SelfAdjointOperator.norm_le_of_unit_inner (radialCorrection_symmetric B v) (by positivity)
  intro h hh
  let a := ⟪v, h⟫
  let q := a ^ 2
  let w := (2 * a) • h + ((1 - q) / 2) • v
  have ha : |a| ≤ 1 := by
    calc
      |a| ≤ ‖v‖ * ‖h‖ := abs_real_inner_le_norm v h
      _ ≤ 1 := by simpa [hh] using hv
  have hq0 : 0 ≤ q := sq_nonneg a
  have hq1 : q ≤ 1 := by
    obtain ⟨ha₁, ha₂⟩ := abs_le.mp ha
    dsimp [q]
    nlinarith
  have hvSq : ‖v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg v]
  have hwSq : ‖w‖ ^ 2 = 6 * q - 2 * q ^ 2 + (1 - q) ^ 2 / 4 * ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    dsimp [w]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    simp only [real_inner_self_eq_norm_sq, hh, one_pow]
    dsimp [a, q]
    rw [real_inner_comm h v]
    ring
  have hw : ‖w‖ ≤ 2 := by
    have h₁ := mul_nonneg (sq_nonneg (1 - q)) (sub_nonneg.mpr hvSq)
    have h₂ := mul_nonneg (sub_nonneg.mpr hq1) (show 0 ≤ 15 - 7 * q by linarith)
    nlinarith [norm_nonneg w]
  have hInner : ⟪radialCorrection B v h, h⟫ = ⟪B v, w⟫ := by
    simp only [radialCorrection, add_apply, smul_apply, sub_apply, one_apply_eq_self, rankOne_apply, inner_add_left, inner_add_right, inner_sub_left, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hh, one_pow, w, a, q]
    rw [real_inner_comm (B v) v]
    ring
  rw [hInner]
  calc
    |⟪B v, w⟫| ≤ ‖B v‖ * ‖w‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖B‖ * ‖v‖) * 2 := mul_le_mul (B.le_opNorm v) hw (norm_nonneg _) (by positivity)
    _ ≤ 2 * ‖B‖ := by nlinarith [mul_le_mul_of_nonneg_left hv (norm_nonneg B)]

private def regularizedRadius (ε : ℝ) (x : H) : ℝ := Real.sqrt (‖x‖ ^ 2 + ε ^ 2)

private def regularizedGradient (A : ℝ → H →L[ℝ] H) (ε : ℝ) (x : H) : H :=
  let R := regularizedRadius ε x
  A R x + (⟪deriv A R x, x⟫ / (2 * R)) • x

omit [InnerProductSpace ℝ H] in
private lemma regularizedRadius_pos {ε : ℝ} (hε : 0 < ε) (x : H) : 0 < regularizedRadius ε x :=
  Real.sqrt_pos.mpr (by positivity)

omit [InnerProductSpace ℝ H] in
private lemma norm_le_regularizedRadius (ε : ℝ) (x : H) : ‖x‖ ≤ regularizedRadius ε x := by
  apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
  nlinarith [sq_nonneg ε]

private lemma hasFDerivAt_regularizedRadius {ε : ℝ} (hε : 0 < ε) (x : H) :
    HasFDerivAt (regularizedRadius ε) ((regularizedRadius ε x)⁻¹ • innerSL ℝ x) x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const (ε ^ 2)).sqrt (by positivity)
  apply h.congr_fderiv
  ext v
  simp only [two_smul, add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul, mul_inv_rev, one_div]
  dsimp [regularizedRadius]
  ring

private lemma contDiff_regularizedRadius {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 2 (regularizedRadius ε : H → ℝ) :=
  ((contDiff_norm_sq ℝ).add contDiff_const).sqrt (fun _ => by positivity)

variable [CompleteSpace H]

private lemma isSelfAdjoint_deriv {A : ℝ → H →L[ℝ] H}
    (hSym : ∀ r > 0, IsSelfAdjoint (A r)) {r : ℝ} (hr : 0 < r) (hA : DifferentiableAt ℝ A r) :
    IsSelfAdjoint (deriv A r) := by
  have hEq : A =ᶠ[𝓝 r] fun s => star (A s) := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact (hSym s hs).star_eq.symm
  exact (hA.hasDerivAt.star.congr_of_eventuallyEq hEq).unique hA.hasDerivAt

omit [CompleteSpace H] in
private lemma hasFDerivAt_radialFamily {A : ℝ → H →L[ℝ] H} {ε : ℝ} (hε : 0 < ε) (x : H)
    (hA : DifferentiableAt ℝ A (regularizedRadius ε x)) :
    HasFDerivAt (fun y => A (regularizedRadius ε y))
      (((regularizedRadius ε x)⁻¹ • innerSL ℝ x).smulRight (deriv A (regularizedRadius ε x))) x := by
  apply (hA.hasDerivAt.hasFDerivAt.comp x (hasFDerivAt_regularizedRadius hε x)).congr_fderiv
  ext v
  rfl

private lemma hasGradientAt_regularizedEnergy {A : ℝ → H →L[ℝ] H} {ε : ℝ} (hε : 0 < ε)
    (hA : ContDiffOn ℝ 2 A (Ioi 0)) (hSym : ∀ r > 0, IsSelfAdjoint (A r)) (x : H) :
    HasGradientAt (regularizedEnergy A ε) (regularizedGradient A ε x) x := by
  have hR := regularizedRadius_pos hε x
  have hA' := ((hA.differentiableOn (by norm_num)) _ hR).differentiableAt (isOpen_Ioi.mem_nhds hR)
  have hAx := (hasFDerivAt_radialFamily hε x hA').clm_apply (hasFDerivAt_id x)
  rw [hasGradientAt_iff_hasFDerivAt]
  apply ((hAx.inner ℝ (hasFDerivAt_id x)).const_mul (1 / 2 : ℝ)).congr_fderiv
  ext v
  change (1 / 2 : ℝ) * (⟪A (regularizedRadius ε x) x, v⟫ +
    ⟪A (regularizedRadius ε x) v + ((regularizedRadius ε x)⁻¹ * ⟪x, v⟫) • deriv A (regularizedRadius ε x) x, x⟫) =
      ⟪regularizedGradient A ε x, v⟫
  have h := (hSym _ hR).isSymmetric v x
  change ⟪A (regularizedRadius ε x) v, x⟫ = ⟪v, A (regularizedRadius ε x) x⟫ at h
  simp only [regularizedGradient, inner_add_left, real_inner_smul_left, h, real_inner_comm v (A (regularizedRadius ε x) x)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

omit [CompleteSpace H] in
private lemma contDiff_regularizedGradient {A : ℝ → H →L[ℝ] H} {ε : ℝ} (hε : 0 < ε)
    (hA : ContDiffOn ℝ 2 A (Ioi 0)) :
    ContDiff ℝ 1 (regularizedGradient A ε) := by
  have hA' : ContDiffOn ℝ 1 (deriv A) (Ioi 0) := hA.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hA₁ : ContDiffOn ℝ 1 A (Ioi 0) := hA.of_le (by norm_num)
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hR := regularizedRadius_pos hε x
  have hRadius : ContDiffAt ℝ 1 (regularizedRadius ε : H → ℝ) x :=
    ((contDiff_regularizedRadius hε).of_le (by norm_num)).contDiffAt
  have hAR := (hA₁.contDiffAt (isOpen_Ioi.mem_nhds hR)).comp x hRadius
  have hBR := (hA'.contDiffAt (isOpen_Ioi.mem_nhds hR)).comp x hRadius
  have hDen : ContDiffAt ℝ 1 (fun y => 2 * regularizedRadius ε y) x := contDiffAt_const.mul hRadius
  exact (hAR.clm_apply contDiffAt_id).add
    ((((hBR.clm_apply contDiffAt_id).inner ℝ contDiffAt_id).div hDen (by positivity)).smul contDiffAt_id)

private lemma hasFDerivAt_regularizedGradient {A : ℝ → H →L[ℝ] H} {ε : ℝ} (hε : 0 < ε)
    (hA : ContDiffOn ℝ 2 A (Ioi 0)) (hSym : ∀ r > 0, IsSelfAdjoint (A r)) (x : H) :
    HasFDerivAt (regularizedGradient A ε) (regularizedHessian A ε x) x := by
  let R := regularizedRadius ε x
  let B := deriv A R
  let C := deriv (deriv A) R
  have hR : 0 < R := regularizedRadius_pos hε x
  have hA' := ((hA.differentiableOn (by norm_num)) _ hR).differentiableAt (isOpen_Ioi.mem_nhds hR)
  have hB : ContDiffOn ℝ 1 (deriv A) (Ioi 0) := hA.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hB' := ((hB.differentiableOn one_ne_zero) _ hR).differentiableAt (isOpen_Ioi.mem_nhds hR)
  have hAx := (hasFDerivAt_radialFamily hε x hA').clm_apply (hasFDerivAt_id x)
  have hBx := (hasFDerivAt_radialFamily hε x hB').clm_apply (hasFDerivAt_id x)
  have hQ := hBx.inner ℝ (hasFDerivAt_id x)
  have hInv := (hasDerivAt_inv hR.ne').comp_hasFDerivAt x (hasFDerivAt_regularizedRadius hε x)
  have hα := (hQ.mul hInv).const_mul (1 / 2 : ℝ)
  have hSum := hAx.add (hα.smul (hasFDerivAt_id x))
  refine (hSum.congr_fderiv ?_).congr_of_eventuallyEq ?_
  · ext v
    apply ext_inner_right ℝ
    intro w
    change ⟪(A R v + (R⁻¹ * ⟪x, v⟫) • B x) +
      (((1 / 2 : ℝ) * (⟪B x, x⟫ * R⁻¹)) • v +
      ((1 / 2 : ℝ) * (⟪B x, x⟫ * (-(R ^ 2)⁻¹ * (R⁻¹ * ⟪x, v⟫)) +
        R⁻¹ * (⟪B x, v⟫ + ⟪B v + (R⁻¹ * ⟪x, v⟫) • C x, x⟫))) • x), w⟫ =
          ⟪regularizedHessian A ε x v, w⟫
    have hSymB := (isSelfAdjoint_deriv hSym hR hA').isSymmetric v x
    change ⟪B v, x⟫ = ⟪v, B x⟫ at hSymB
    change _ = ⟪(A R + R • radialCorrection B (R⁻¹ • x) + (R ^ 2 / 2 * ⟪R⁻¹ • x, C (R⁻¹ • x)⟫) • rankOne ℝ (R⁻¹ • x) (R⁻¹ • x)) v, w⟫
    simp only [radialCorrection, add_apply, smul_apply, sub_apply, one_apply_eq_self, rankOne_apply, map_smul, inner_add_left, inner_sub_left, real_inner_smul_left, real_inner_smul_right]
    rw [hSymB]
    simp only [real_inner_comm]
    field_simp [hR.ne']
    ring
  · filter_upwards [] with y
    change A (regularizedRadius ε y) y +
      (⟪deriv A (regularizedRadius ε y) y, y⟫ / (2 * regularizedRadius ε y)) • y =
        A (regularizedRadius ε y) y +
          ((1 / 2 : ℝ) * (⟪deriv A (regularizedRadius ε y) y, y⟫ * (regularizedRadius ε y)⁻¹)) • y
    congr 2
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- Differentiating the gradient gives the regularized Hessian. -/
theorem VaryingQuadratic.hessian_regularizedEnergy {A : ℝ → H →L[ℝ] H} {ε : ℝ} (hε : 0 < ε)
    (hA : ContDiffOn ℝ 2 A (Ioi 0)) (hSym : ∀ r > 0, IsSelfAdjoint (A r)) (x : H) :
    fderiv ℝ (gradient (regularizedEnergy A ε)) x = regularizedHessian A ε x := by
  rw [gradient_eq (hasGradientAt_regularizedEnergy hε hA hSym)]
  exact (hasFDerivAt_regularizedGradient hε hA hSym x).fderiv

omit [CompleteSpace H] in
private lemma norm_regularizedHessian_sub_le (A : ℝ → H →L[ℝ] H) {ε : ℝ} (hε : 0 < ε) (x : H) :
    ‖regularizedHessian A ε x - A (regularizedRadius ε x)‖ ≤ radialVariation A (regularizedRadius ε x) := by
  let r := regularizedRadius ε x
  let v := r⁻¹ • x
  have hr : 0 < r := regularizedRadius_pos hε x
  have hv : ‖v‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_eq_div]
    exact (div_le_one hr).mpr (norm_le_regularizedRadius ε x)
  let B := deriv A r
  let C := deriv (deriv A) r
  have hvSq : ‖v‖ * ‖v‖ ≤ 1 := by nlinarith [norm_nonneg v]
  have hInner : |⟪v, C v⟫| ≤ ‖C‖ := by
    calc
      |⟪v, C v⟫| ≤ ‖v‖ * ‖C v‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖v‖ * (‖C‖ * ‖v‖) := mul_le_mul_of_nonneg_left (C.le_opNorm v) (norm_nonneg v)
      _ ≤ ‖C‖ := by nlinarith [mul_le_mul_of_nonneg_left hvSq (norm_nonneg C)]
  have hFirst : ‖r • radialCorrection B v‖ ≤ r * (2 * ‖B‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (norm_radialCorrection_le B hv) hr.le
  have hSecond : ‖(r ^ 2 / 2 * ⟪v, C v⟫) • rankOne ℝ v v‖ ≤ r ^ 2 / 2 * ‖C‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ r ^ 2 / 2), norm_rankOne]
    calc
      r ^ 2 / 2 * |⟪v, C v⟫| * (‖v‖ * ‖v‖) ≤ (r ^ 2 / 2 * ‖C‖) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hInner (by positivity)) hvSq (by positivity) (by positivity)
      _ = _ := mul_one _
  calc
    ‖regularizedHessian A ε x - A r‖ =
        ‖r • radialCorrection B v + (r ^ 2 / 2 * ⟪v, C v⟫) • rankOne ℝ v v‖ := by
      congr 1
      change A r + r • radialCorrection B v + (r ^ 2 / 2 * ⟪v, C v⟫) • rankOne ℝ v v - A r = _
      abel
    _ ≤ ‖r • radialCorrection B v‖ + ‖(r ^ 2 / 2 * ⟪v, C v⟫) • rankOne ℝ v v‖ := norm_add_le _ _
    _ ≤ r * (2 * ‖B‖) + r ^ 2 / 2 * ‖C‖ := add_le_add hFirst hSecond
    _ = radialVariation A r := by dsimp [radialVariation, B, C]; ring

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
private lemma tendsto_regularizedRadius (x : H) :
    Tendsto (fun ε : ℝ => regularizedRadius ε x) (𝓝 0) (𝓝 ‖x‖) := by
  have h : Continuous (fun ε : ℝ => Real.sqrt (‖x‖ ^ 2 + ε ^ 2)) :=
    (continuous_const.add (continuous_id.pow 2)).sqrt
  simpa [regularizedRadius] using h.tendsto 0

omit [CompleteSpace H] in
private lemma tendsto_regularizedEnergy {A : ℝ → H →L[ℝ] H}
    (hA : ContDiffOn ℝ 2 A (Ioi 0)) (x : H) :
    Tendsto (fun ε : ℝ => regularizedEnergy A ε x) (𝓝 0) (𝓝 (varyingQuadratic A x)) := by
  by_cases hx : x = 0
  · subst x
    simp [regularizedEnergy]
  have hR := tendsto_regularizedRadius x
  have hAR := (hA.continuousOn.continuousAt (isOpen_Ioi.mem_nhds (norm_pos_iff.mpr hx))).tendsto.comp hR
  exact tendsto_const_nhds.mul ((hAR.eval_const x).inner tendsto_const_nhds)

omit [CompleteSpace H] in
private lemma tendsto_regularizedGradient {A : ℝ → H →L[ℝ] H}
    (hA : ContDiffOn ℝ 2 A (Ioi 0)) (x : H) :
    Tendsto (fun ε : ℝ => regularizedGradient A ε x) (𝓝 0)
      (𝓝 (A ‖x‖ x + (⟪deriv A ‖x‖ x, x⟫ / (2 * ‖x‖)) • x)) := by
  by_cases hx : x = 0
  · subst x
    simp [regularizedGradient]
  have hR := tendsto_regularizedRadius x
  have hAR := (hA.continuousOn.continuousAt (isOpen_Ioi.mem_nhds (norm_pos_iff.mpr hx))).tendsto.comp hR
  have hB : ContDiffOn ℝ 1 (deriv A) (Ioi 0) := hA.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hBR := (hB.continuousOn.continuousAt (isOpen_Ioi.mem_nhds (norm_pos_iff.mpr hx))).tendsto.comp hR
  exact (hAR.eval_const x).add
    ((((hBR.eval_const x).inner tendsto_const_nhds).div
      (tendsto_const_nhds.mul hR) (by positivity)).smul tendsto_const_nhds)

/-- Uniform Hessian bounds for the regularizations give UN for the varying quadratic energy. -/
theorem varyingQuadratic_isUN_of_regularized_hessian_bounds {A : ℝ → H →L[ℝ] H} {μ L : ℝ}
    (hμ : 0 < μ) (hμL : μ ≤ L)
    (hA : ContDiffOn ℝ 2 A (Ioi 0)) (hSym : ∀ r > 0, IsSelfAdjoint (A r))
    (hBounds : ∀ ε > 0, ∀ x h,
      μ * ‖h‖ ≤ ‖regularizedHessian A ε x h‖ ∧
      ‖regularizedHessian A ε x h‖ ≤ L * ‖h‖) :
    IsUN (CurvatureBounds.symmetric μ L hμ hμL) (varyingQuadratic A) := by
  apply isUN_of_pointwise_limit (l := 𝓝[>] (0 : ℝ)) (Eᵢ := regularizedEnergy A)
    (g := fun x => A ‖x‖ x + (⟪deriv A ‖x‖ x, x⟫ / (2 * ‖x‖)) • x)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hGrad := hasGradientAt_regularizedEnergy hε hA hSym
    have hg := contDiff_regularizedGradient hε hA
    apply GradientMap.isUN_of_spectral_bounds hGrad hg
    intro x
    let T := regularizedHessian A ε x
    have hTBounds (h : H) : μ * ‖h‖ ≤ ‖T h‖ ∧ ‖T h‖ ≤ L * ‖h‖ :=
      hBounds ε hε x h
    have hDeriv := hasFDerivAt_regularizedGradient hε hA hSym x
    have hT : IsSelfAdjoint T := by
      dsimp [T]
      rw [← hDeriv.fderiv]
      exact GradientMap.hessian_selfAdjoint hGrad (hg.differentiable one_ne_zero x)
    have hNorm : ‖T‖ ≤ L := T.opNorm_le_bound (hμ.le.trans hμL) (fun h => (hTBounds h).2)
    rw [hDeriv.fderiv]
    intro σ hσ
    have hu := (SelfAdjointOperator.norm_le_iff hT (hμ.le.trans hμL)).mp hNorm σ hσ
    have hl := (SelfAdjointOperator.gap_iff hT hμ).mpr (fun h => (hTBounds h).1) σ hσ
    rw [CurvatureBounds.mem_bands_iff_centered]
    simpa [CurvatureBounds.symmetric, CurvatureBounds.outerCenter, CurvatureBounds.outerRadius, CurvatureBounds.innerCenter, CurvatureBounds.innerRadius] using And.intro hu hl
  · intro x
    exact (tendsto_regularizedEnergy hA x).mono_left nhdsWithin_le_nhds
  · intro x
    apply ((tendsto_regularizedGradient hA x).mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hasGradientAt_regularizedEnergy hε hA hSym x).gradient.symm

/-- Radially varying quadratic forms define a UN energy when their spectral gap dominates their variation. -/
theorem varyingQuadratic_isUN {A : ℝ → H →L[ℝ] H} {μ M : ℝ}
    (hμ : 0 < μ) (hμM : μ ≤ M)
    (hA : ContDiffOn ℝ 2 A (Ioi 0)) (hSym : ∀ r > 0, IsSelfAdjoint (A r))
    (hUpper : ∀ r > 0, ‖A r‖ ≤ M)
    (hLower : ∀ r > 0, ∀ v, (μ + radialVariation A r) * ‖v‖ ≤ ‖A r v‖) :
    IsUN (CurvatureBounds.symmetric μ (2 * M - μ) hμ (by linarith)) (varyingQuadratic A) := by
  apply varyingQuadratic_isUN_of_regularized_hessian_bounds hμ (by linarith) hA hSym
  intro ε hε x h
  let r := regularizedRadius ε x
  have hr : 0 < r := regularizedRadius_pos hε x
  let T := regularizedHessian A ε x
  have hDifference : ‖(T - A r) h‖ ≤ radialVariation A r * ‖h‖ :=
    ((T - A r).le_opNorm h).trans
      (mul_le_mul_of_nonneg_right (norm_regularizedHessian_sub_le A hε x) (norm_nonneg h))
  have hAu : ‖A r h‖ ≤ M * ‖h‖ :=
    ((A r).le_opNorm h).trans (mul_le_mul_of_nonneg_right (hUpper r hr) (norm_nonneg h))
  have hl := hLower r hr h
  have h₁ := norm_add_le ((T - A r) h) (A r h)
  have h₂ := norm_sub_le (T h) ((T - A r) h)
  simp only [sub_apply, sub_add_cancel, sub_sub_cancel] at hDifference h₁ h₂
  constructor <;> nlinarith

end UN.Examples
