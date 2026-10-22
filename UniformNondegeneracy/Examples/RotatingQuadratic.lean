module

public import UniformNondegeneracy.Examples.VaryingQuadratic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-!
# Logarithmically rotating quadratic forms

Conjugating a self-adjoint operator by `exp (log ‖x‖ • Ω)` gives a UN energy when its first two commutators with the skew-adjoint generator are sufficiently small.

Operator conjugation supplies the radial derivatives, and a rank-one perturbation estimate controls the regularized Hessians. The criterion for varying quadratics passes these bounds to the energy.
-/

noncomputable section

open Set Filter Topology InnerProductSpace
open scoped RealInnerProductSpace

namespace UN.Examples

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A quadratic form rotated through logarithmic radius by the generator `Ω`. -/
def rotatingQuadratic (A Ω : H →L[ℝ] H) (x : H) : ℝ :=
  let y := NormedSpace.exp (Real.log ‖x‖ • Ω) x
  (1 / 2 : ℝ) * ⟪A y, y⟫

@[simp] theorem rotatingQuadratic_zero (A Ω : H →L[ℝ] H) : rotatingQuadratic A Ω 0 = 0 := by
  simp [rotatingQuadratic]

/-- The squared Hessian perturbation bound in terms of the first two commutators. -/
def rotationErrorSq (A Ω : H →L[ℝ] H) : ℝ :=
  let C₁ := Ω * A - A * Ω
  let C₂ := Ω * C₁ - C₁ * Ω
  (7 / 3 : ℝ) * ‖C₁‖ ^ 2 + (3 / 2 : ℝ) * ‖C₁‖ * ‖C₂‖ + (1 / 4 : ℝ) * ‖C₂‖ ^ 2

private def rotationCorrection (C₁ : H →L[ℝ] H) (v : H) : H →L[ℝ] H :=
  -(rankOne ℝ (C₁ v) v + rankOne ℝ v (C₁ v)) - (⟪v, C₁ v⟫ / 2) • 1 + ⟪v, C₁ v⟫ • rankOne ℝ v v

private lemma rotationCorrection_symmetric (C₁ : H →L[ℝ] H) (v : H) :
    (rotationCorrection C₁ v).IsSymmetric := by
  intro x y
  simp only [rotationCorrection, ContinuousLinearMap.coe_coe, add_apply, neg_apply, sub_apply, smul_apply, one_apply_eq_self, rankOne_apply, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_neg_left, inner_neg_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm]
  ring

private lemma norm_rotationCorrection_le (C₁ : H →L[ℝ] H) {v : H} (hv : ‖v‖ ≤ 1) :
    ‖rotationCorrection C₁ v‖ ≤ Real.sqrt (7 / 3) * ‖C₁‖ := by
  apply SelfAdjointOperator.norm_le_of_unit_inner (rotationCorrection_symmetric C₁ v) (by positivity)
  intro h hh
  let α := ⟪v, h⟫
  let q := α ^ 2
  let w := (q - 1 / 2) • v - (2 * α) • h
  have hn : ‖v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg v]
  have hwSq : ‖w‖ ^ 2 = (q - 1 / 2) ^ 2 * ‖v‖ ^ 2 + 6 * q - 4 * q ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    dsimp [w]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    simp only [real_inner_self_eq_norm_sq, hh, one_pow]
    dsimp [q, α]
    rw [real_inner_comm h v]
    ring
  have hw : ‖w‖ ≤ Real.sqrt (7 / 3) := by
    have h₁ := mul_nonneg (sq_nonneg (q - 1 / 2)) (sub_nonneg.mpr hn)
    have h₂ := sq_nonneg (q - 5 / 6)
    have h₃ := Real.sq_sqrt (show (0 : ℝ) ≤ 7 / 3 by norm_num)
    nlinarith [norm_nonneg w, Real.sqrt_nonneg (7 / 3)]
  have hInner : ⟪rotationCorrection C₁ v h, h⟫ = ⟪C₁ v, w⟫ := by
    simp only [rotationCorrection, add_apply, neg_apply, sub_apply, smul_apply, one_apply_eq_self, rankOne_apply, inner_add_left, inner_neg_left, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hh, one_pow, w, q, α]
    simp only [real_inner_comm]
    ring
  rw [hInner]
  calc
    |⟪C₁ v, w⟫| ≤ ‖C₁ v‖ * ‖w‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖C₁‖ * Real.sqrt (7 / 3) :=
      mul_le_mul ((C₁.le_opNorm v).trans (mul_le_of_le_one_right (norm_nonneg C₁) hv))
        hw (norm_nonneg _) (norm_nonneg _)
    _ = _ := mul_comm _ _

variable [CompleteSpace H]

private lemma norm_rotationCorrection_anticommutator_le (C₁ : H →L[ℝ] H) {v : H} (hv : ‖v‖ ≤ 1) :
    ‖rotationCorrection C₁ v * rankOne ℝ v v + rankOne ℝ v v * rotationCorrection C₁ v‖ ≤ 3 * ‖C₁‖ := by
  let T := rotationCorrection C₁ v
  let P := rankOne ℝ v v
  have hSym : (T * P + P * T).IsSymmetric := by
    have hT : IsSelfAdjoint T := (rotationCorrection_symmetric C₁ v).isSelfAdjoint
    have hP : IsSelfAdjoint P := (isSymmetric_rankOne_self v).isSelfAdjoint
    apply IsSelfAdjoint.isSymmetric
    simp only [IsSelfAdjoint, star_add, star_mul, hT.star_eq, hP.star_eq, add_comm]
  apply SelfAdjointOperator.norm_le_of_unit_inner hSym (by positivity)
  intro h hh
  let n := ‖v‖ ^ 2
  let α := ⟪v, h⟫
  let q := α ^ 2
  let w := (2 * (n - 3 / 2) * q) • v - (2 * n * α) • h
  have hn0 : 0 ≤ n := sq_nonneg _
  have hn1 : n ≤ 1 := by dsimp [n]; nlinarith [norm_nonneg v]
  have hq0 : 0 ≤ q := sq_nonneg _
  have hqn : q ≤ n := by
    have hα : |α| ≤ ‖v‖ := by simpa [α, hh] using abs_real_inner_le_norm v h
    dsimp [q, n]
    nlinarith [sq_abs α, abs_nonneg α, norm_nonneg v]
  have hqSq : q ^ 2 ≤ n ^ 2 := by nlinarith
  have hwSq : ‖w‖ ^ 2 = n * (4 * n ^ 2 - 20 * n + 21) * q ^ 2 + 4 * n ^ 2 * q := by
    rw [← real_inner_self_eq_norm_sq]
    dsimp [w]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    simp only [real_inner_self_eq_norm_sq, hh, one_pow]
    dsimp [q, α, n]
    rw [real_inner_comm h v]
    ring
  have hw : ‖w‖ ≤ 3 := by
    have hCoeff : 0 ≤ n * (4 * n ^ 2 - 20 * n + 21) := by
      apply mul_nonneg hn0
      nlinarith [sq_nonneg n]
    have h₁ := mul_le_mul_of_nonneg_left hqSq hCoeff
    have h₂ := mul_le_mul_of_nonneg_left hqn (show 0 ≤ 4 * n ^ 2 by positivity)
    have hk0 : 0 ≤ n * (5 - 2 * n) := mul_nonneg hn0 (by linarith)
    have hk3 : n * (5 - 2 * n) ≤ 3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (show 0 ≤ 3 - 2 * n by linarith)]
    have hkSq : (n * (5 - 2 * n)) ^ 2 ≤ 9 := by nlinarith
    have h₃ := mul_le_mul_of_nonneg_left hkSq hn0
    nlinarith [norm_nonneg w]
  have hInner : ⟪(T * P + P * T) h, h⟫ = ⟪C₁ v, w⟫ := by
    simp only [T, P, rotationCorrection, add_apply, mul_apply_eq_comp, neg_apply, sub_apply, smul_apply, one_apply_eq_self, rankOne_apply, inner_add_left, inner_add_right, inner_neg_left, inner_neg_right, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, w, q, α, n]
    simp only [real_inner_comm]
    ring
  rw [hInner]
  calc
    |⟪C₁ v, w⟫| ≤ ‖C₁ v‖ * ‖w‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖C₁‖ * 3 :=
      mul_le_mul ((C₁.le_opNorm v).trans (mul_le_of_le_one_right (norm_nonneg C₁) hv))
        hw (norm_nonneg _) (norm_nonneg _)
    _ = _ := mul_comm _ _

private lemma norm_rotationPerturbation_le (C₁ C₂ : H →L[ℝ] H) {v : H} (hv : ‖v‖ ≤ 1) :
    ‖rotationCorrection C₁ v + (⟪v, C₂ v⟫ / 2) • rankOne ℝ v v‖ ≤
      Real.sqrt ((7 / 3 : ℝ) * ‖C₁‖ ^ 2 + (3 / 2 : ℝ) * ‖C₁‖ * ‖C₂‖ + (1 / 4 : ℝ) * ‖C₂‖ ^ 2) := by
  let T := rotationCorrection C₁ v
  let P := rankOne ℝ v v
  let η := ⟪v, C₂ v⟫ / 2
  let K := T * P + P * T
  let R := (7 / 3 : ℝ) * ‖C₁‖ ^ 2 + (3 / 2 : ℝ) * ‖C₁‖ * ‖C₂‖ + (1 / 4 : ℝ) * ‖C₂‖ ^ 2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hP : ‖P‖ ≤ 1 := by rw [norm_rankOne]; nlinarith [norm_nonneg v]
  have hη : |η| ≤ ‖C₂‖ / 2 := by
    have hInner : |⟪v, C₂ v⟫| ≤ ‖C₂‖ := by
      calc
        |⟪v, C₂ v⟫| ≤ ‖v‖ * ‖C₂ v‖ := abs_real_inner_le_norm _ _
        _ ≤ 1 * ‖C₂‖ := mul_le_mul hv
          ((C₂.le_opNorm v).trans (mul_le_of_le_one_right (norm_nonneg C₂) hv))
          (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    simpa only [η, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      div_le_div_of_nonneg_right hInner (by norm_num)
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro h
  have hTBound : ‖T h‖ ≤ (Real.sqrt (7 / 3) * ‖C₁‖) * ‖h‖ :=
    (T.le_opNorm h).trans (mul_le_mul_of_nonneg_right (norm_rotationCorrection_le C₁ hv) (norm_nonneg h))
  have hTSq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hTBound
  simp only [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 7 / 3 by norm_num)] at hTSq
  have hKBound : |⟪K h, h⟫| ≤ 3 * ‖C₁‖ * ‖h‖ ^ 2 := by
    calc
      |⟪K h, h⟫| ≤ ‖K h‖ * ‖h‖ := abs_real_inner_le_norm _ _
      _ ≤ ((3 * ‖C₁‖) * ‖h‖) * ‖h‖ :=
        mul_le_mul_of_nonneg_right
          ((K.le_opNorm h).trans (mul_le_mul_of_nonneg_right
            (norm_rotationCorrection_anticommutator_le C₁ hv) (norm_nonneg h))) (norm_nonneg h)
      _ = _ := by ring
  have hCross : η * ⟪K h, h⟫ ≤ (‖C₂‖ / 2) * (3 * ‖C₁‖ * ‖h‖ ^ 2) := by
    calc
      η * ⟪K h, h⟫ ≤ |η * ⟪K h, h⟫| := le_abs_self _
      _ = |η| * |⟪K h, h⟫| := abs_mul _ _
      _ ≤ _ := mul_le_mul hη hKBound (abs_nonneg _) (by positivity)
  have hPBound : ‖η • P h‖ ≤ (‖C₂‖ / 2) * ‖h‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hη ((P.le_opNorm h).trans (by nlinarith [norm_nonneg h]))
      (norm_nonneg _) (by positivity)
  have hPSq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hPBound
  have hSquare : ‖(T + η • P) h‖ ^ 2 = ‖T h‖ ^ 2 + η * ⟪K h, h⟫ + ‖η • P h‖ ^ 2 := by
    have hT := rotationCorrection_symmetric C₁ v (P h) h
    have hP := isSymmetric_rankOne_self (𝕜 := ℝ) v (T h) h
    change ⟪T (P h), h⟫ = ⟪P h, T h⟫ at hT
    change ⟪P (T h), h⟫ = ⟪T h, P h⟫ at hP
    simp only [← real_inner_self_eq_norm_sq, add_apply, smul_apply, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, K, mul_apply_eq_comp, hT, hP]
    rw [real_inner_comm (P h) (T h)]
    ring
  change ‖(T + η • P) h‖ ≤ Real.sqrt R * ‖h‖
  have hSq : ‖(T + η • P) h‖ ^ 2 ≤ R * ‖h‖ ^ 2 := by
    dsimp [R]
    nlinarith only [hSquare, hTSq, hCross, hPSq]
  have hRoot : (Real.sqrt R * ‖h‖) ^ 2 = R * ‖h‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt hR]
  nlinarith [norm_nonneg ((T + η • P) h), mul_nonneg (Real.sqrt_nonneg R) (norm_nonneg h)]

private def operatorOrbit (Ω A : H →L[ℝ] H) (s : ℝ) : H →L[ℝ] H :=
  NormedSpace.exp (s • (-Ω)) * A * NormedSpace.exp (s • Ω)

private lemma exp_rotation_unitary {Ω : H →L[ℝ] H} (hΩ : star Ω = -Ω) (s : ℝ) :
    NormedSpace.exp (s • Ω) ∈ unitary (H →L[ℝ] H) := by
  let : NormedAlgebra ℚ (H →L[ℝ] H) := .restrictScalars ℚ ℝ _
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  change star (s • Ω) = -(s • Ω)
  simp [hΩ]

private lemma star_exp_rotation {Ω : H →L[ℝ] H} (hΩ : star Ω = -Ω) (s : ℝ) :
    star (NormedSpace.exp (s • Ω)) = NormedSpace.exp (s • (-Ω)) := by
  simp [NormedSpace.star_exp, hΩ]

private lemma operatorOrbit_selfAdjoint {Ω A : H →L[ℝ] H}
    (hΩ : star Ω = -Ω) (hA : IsSelfAdjoint A) (s : ℝ) :
    IsSelfAdjoint (operatorOrbit Ω A s) := by
  rw [operatorOrbit, ← star_exp_rotation hΩ]
  exact hA.conjugate' _

private lemma norm_operatorOrbit {Ω : H →L[ℝ] H} (hΩ : star Ω = -Ω) (A : H →L[ℝ] H) (s : ℝ) :
    ‖operatorOrbit Ω A s‖ = ‖A‖ := by
  rw [operatorOrbit, ← star_exp_rotation hΩ, CStarRing.norm_mul_mem_unitary _ (exp_rotation_unitary hΩ s)]
  exact CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem (exp_rotation_unitary hΩ s))

private lemma operatorOrbit_lower_bound {Ω A : H →L[ℝ] H} {m : ℝ}
    (hΩ : star Ω = -Ω) (hLower : ∀ v, m * ‖v‖ ≤ ‖A v‖) (s : ℝ) (v : H) :
    m * ‖v‖ ≤ ‖operatorOrbit Ω A s v‖ := by
  have hU := exp_rotation_unitary hΩ s
  rw [operatorOrbit, ← star_exp_rotation hΩ]
  simp only [mul_apply_eq_comp, ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.star_mem hU)]
  simpa only [ContinuousLinearMap.norm_map_of_mem_unitary hU] using
    hLower (NormedSpace.exp (s • Ω) v)

private lemma hasDerivAt_operatorOrbit (Ω A : H →L[ℝ] H) (s : ℝ) :
    HasDerivAt (operatorOrbit Ω A) (-(operatorOrbit Ω (Ω * A - A * Ω) s)) s := by
  have h := ((hasDerivAt_exp_smul_const (-Ω) s).mul_const A).mul (hasDerivAt_exp_smul_const' Ω s)
  convert h using 1
  · rfl
  · dsimp [operatorOrbit]
    noncomm_ring

private lemma contDiff_operatorOrbit (Ω A : H →L[ℝ] H) : ContDiff ℝ 2 (operatorOrbit Ω A) := by
  have hExp : ContDiff ℝ 2 (NormedSpace.exp : (H →L[ℝ] H) → H →L[ℝ] H) :=
    contDiff_iff_contDiffAt.mpr (fun _ => (NormedSpace.exp_analytic (𝕂 := ℝ) _).contDiffAt)
  exact ((hExp.comp (contDiff_id.smul contDiff_const)).mul contDiff_const).mul
    (hExp.comp (contDiff_id.smul contDiff_const))

private def rotatingFamily (A Ω : H →L[ℝ] H) (r : ℝ) : H →L[ℝ] H :=
  operatorOrbit Ω A (Real.log r)

private lemma contDiffOn_rotatingFamily (A Ω : H →L[ℝ] H) :
    ContDiffOn ℝ 2 (rotatingFamily A Ω) (Ioi 0) :=
  (contDiff_operatorOrbit Ω A).comp_contDiffOn
    (Real.contDiffOn_log.mono (fun _ hr => ne_of_gt hr))

private lemma hasDerivAt_rotatingFamily (A Ω : H →L[ℝ] H) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (rotatingFamily A Ω) (-r⁻¹ • rotatingFamily (Ω * A - A * Ω) Ω r) r := by
  change HasDerivAt (operatorOrbit Ω A ∘ Real.log) _ r
  simpa only [rotatingFamily, smul_neg, neg_smul] using
    (hasDerivAt_operatorOrbit Ω A (Real.log r)).scomp r (Real.hasDerivAt_log hr.ne')

private lemma deriv_rotatingFamily (A Ω : H →L[ℝ] H) {r : ℝ} (hr : 0 < r) :
    deriv (rotatingFamily A Ω) r = -r⁻¹ • rotatingFamily (Ω * A - A * Ω) Ω r :=
  (hasDerivAt_rotatingFamily A Ω hr).deriv

private lemma deriv₂_rotatingFamily (A Ω : H →L[ℝ] H) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (rotatingFamily A Ω)) r =
      (r ^ 2)⁻¹ • (rotatingFamily (Ω * A - A * Ω) Ω r +
        rotatingFamily (Ω * (Ω * A - A * Ω) - (Ω * A - A * Ω) * Ω) Ω r) := by
  have hEq : deriv (rotatingFamily A Ω) =ᶠ[𝓝 r]
      fun s => -s⁻¹ • rotatingFamily (Ω * A - A * Ω) Ω s := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact deriv_rotatingFamily A Ω hs
  rw [hEq.deriv_eq]
  have h := ((hasDerivAt_inv hr.ne').neg.smul (hasDerivAt_rotatingFamily (Ω * A - A * Ω) Ω hr)).deriv
  convert h using 1
  simp only [Pi.neg_apply, neg_neg, smul_neg, neg_smul, smul_smul, smul_add]
  module

private lemma rotatingFamily_regularizedHessian (A Ω : H →L[ℝ] H) {ε : ℝ} (hε : 0 < ε) (x : H) :
    let r := Real.sqrt (‖x‖ ^ 2 + ε ^ 2)
    let v := r⁻¹ • x
    VaryingQuadratic.regularizedHessian (rotatingFamily A Ω) ε x =
      rotatingFamily A Ω r +
        (rotationCorrection (rotatingFamily (Ω * A - A * Ω) Ω r) v +
          (⟪v, rotatingFamily (Ω * (Ω * A - A * Ω) - (Ω * A - A * Ω) * Ω) Ω r v⟫ / 2) • rankOne ℝ v v) := by
  have hr : 0 < Real.sqrt (‖x‖ ^ 2 + ε ^ 2) := Real.sqrt_pos.mpr (by positivity)
  dsimp only [VaryingQuadratic.regularizedHessian]
  rw [deriv_rotatingFamily A Ω hr, deriv₂_rotatingFamily A Ω hr]
  ext h
  apply ext_inner_right ℝ
  intro z
  simp only [rotationCorrection, add_apply, neg_apply, sub_apply, smul_apply, one_apply_eq_self, rankOne_apply, inner_add_left, inner_add_right, inner_neg_left, inner_sub_left, real_inner_smul_left, real_inner_smul_right]
  field_simp [hr.ne']
  ring

private lemma rotatingQuadratic_eq_varyingQuadratic {Ω : H →L[ℝ] H} (hΩ : star Ω = -Ω) (A : H →L[ℝ] H) :
    rotatingQuadratic A Ω = varyingQuadratic (rotatingFamily A Ω) := by
  funext x
  dsimp [rotatingQuadratic, varyingQuadratic, rotatingFamily, operatorOrbit]
  rw [← star_exp_rotation hΩ]
  congr 1
  exact ((NormedSpace.exp (Real.log ‖x‖ • Ω)).adjoint_inner_left x (A (NormedSpace.exp (Real.log ‖x‖ • Ω) x))).symm

private lemma rotatingQuadratic_isUN_of_gap {A Ω : H →L[ℝ] H} {m ρ : ℝ}
    (hA : IsSelfAdjoint A) (hΩ : star Ω = -Ω)
    (hρ : 0 ≤ ρ) (hGap : ρ < m) (hmA : m ≤ ‖A‖)
    (hLower : ∀ h, m * ‖h‖ ≤ ‖A h‖) (hError : rotationErrorSq A Ω ≤ ρ ^ 2) :
    IsUN (CurvatureBounds.symmetric (m - ρ) (‖A‖ + ρ) (by linarith) (by linarith))
      (rotatingQuadratic A Ω) := by
  rw [rotatingQuadratic_eq_varyingQuadratic hΩ]
  apply varyingQuadratic_isUN_of_regularized_hessian_bounds (by linarith) (by linarith)
    (contDiffOn_rotatingFamily A Ω) (fun r _ => operatorOrbit_selfAdjoint hΩ hA (Real.log r))
  intro ε hε x h
  let r := Real.sqrt (‖x‖ ^ 2 + ε ^ 2)
  let v := r⁻¹ • x
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hv : ‖v‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_eq_div]
    apply (div_le_one hr).mpr
    apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    nlinarith [sq_nonneg ε]
  let F := rotatingFamily A Ω r
  let T := VaryingQuadratic.regularizedHessian (rotatingFamily A Ω) ε x
  have hRoot : Real.sqrt (rotationErrorSq A Ω) ≤ ρ := by
    exact (Real.sqrt_le_iff).mpr ⟨hρ, hError⟩
  have hPerturbation : ‖T - F‖ ≤ ρ := by
    rw [show T - F =
        rotationCorrection (rotatingFamily (Ω * A - A * Ω) Ω r) v +
          (⟪v, rotatingFamily (Ω * (Ω * A - A * Ω) - (Ω * A - A * Ω) * Ω) Ω r v⟫ / 2) • rankOne ℝ v v by
      dsimp [T, F]
      rw [rotatingFamily_regularizedHessian A Ω hε x]
      abel]
    apply le_trans (norm_rotationPerturbation_le _ _ hv)
    simpa only [rotatingFamily, norm_operatorOrbit hΩ, rotationErrorSq] using hRoot
  have hDifference : ‖(T - F) h‖ ≤ ρ * ‖h‖ :=
    ((T - F).le_opNorm h).trans (mul_le_mul_of_nonneg_right hPerturbation (norm_nonneg h))
  have hFl : m * ‖h‖ ≤ ‖F h‖ := operatorOrbit_lower_bound hΩ hLower (Real.log r) h
  have hFu : ‖F h‖ ≤ ‖A‖ * ‖h‖ := by
    simpa only [F, rotatingFamily, norm_operatorOrbit hΩ] using F.le_opNorm h
  have h₁ := norm_add_le ((T - F) h) (F h)
  have h₂ := norm_sub_le (T h) ((T - F) h)
  simp only [sub_apply, sub_add_cancel, sub_sub_cancel] at hDifference h₁ h₂
  constructor <;> nlinarith

omit [CompleteSpace H] in
private lemma inverse_norm_lower_bound {A : H →L[ℝ] H} (hInv : IsUnit A) (v : H) :
    ‖Ring.inverse A‖⁻¹ * ‖v‖ ≤ ‖A v‖ := by
  by_cases hn : ‖Ring.inverse A‖ = 0
  · simp [hn]
  have hnPos : 0 < ‖Ring.inverse A‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
  have h := (Ring.inverse A).le_opNorm (A v)
  have hCancel : (Ring.inverse A) (A v) = v := by
    have := congrArg (fun T : H →L[ℝ] H => T v) (Ring.inverse_mul_cancel A hInv)
    simpa using this
  rw [hCancel] at h
  rw [inv_mul_eq_div, div_le_iff₀ hnPos]
  simpa only [mul_comm] using h

omit [CompleteSpace H] in
private lemma inverse_norm_le_norm {A : H →L[ℝ] H} (hInv : IsUnit A) :
    ‖Ring.inverse A‖⁻¹ ≤ ‖A‖ := by
  nontriviality H
  have h := norm_mul_le (Ring.inverse A) A
  rw [Ring.inverse_mul_cancel A hInv, norm_one] at h
  have hnPos : 0 < ‖Ring.inverse A‖ := by
    have : 0 ≤ ‖A‖ := norm_nonneg A
    nlinarith [norm_nonneg (Ring.inverse A)]
  rw [inv_eq_one_div, div_le_iff₀ hnPos]
  simpa only [mul_comm] using h

omit [CompleteSpace H] in
private lemma rotation_gap_pos {A Ω : H →L[ℝ] H}
    (hSmall : rotationErrorSq A Ω < (‖Ring.inverse A‖⁻¹) ^ 2) :
    0 < ‖Ring.inverse A‖⁻¹ - Real.sqrt (rotationErrorSq A Ω) := by
  have hNonneg : 0 ≤ rotationErrorSq A Ω := by dsimp [rotationErrorSq]; positivity
  have hSq := Real.sq_sqrt hNonneg
  have hm : 0 ≤ ‖Ring.inverse A‖⁻¹ := by positivity
  nlinarith [Real.sqrt_nonneg (rotationErrorSq A Ω)]

/-- Symmetric curvature bands with inner radius `‖A⁻¹‖⁻¹ - ρ` and outer radius `‖A‖ + ρ`, where `ρ² = rotationErrorSq A Ω`. -/
def RotatingQuadratic.curvatureBounds (A Ω : H →L[ℝ] H) (hInv : IsUnit A)
    (hSmall : rotationErrorSq A Ω < (‖Ring.inverse A‖⁻¹) ^ 2) : CurvatureBounds :=
  let m := ‖Ring.inverse A‖⁻¹
  let ρ := Real.sqrt (rotationErrorSq A Ω)
  CurvatureBounds.symmetric (m - ρ) (‖A‖ + ρ) (by exact rotation_gap_pos hSmall)
    (by dsimp [m, ρ]; linarith [inverse_norm_le_norm hInv, Real.sqrt_nonneg (rotationErrorSq A Ω)])

/-- A logarithmically rotating quadratic is UN when the commutator error is smaller than the spectral gap. -/
theorem rotatingQuadratic_isUN {A Ω : H →L[ℝ] H}
    (hA : IsSelfAdjoint A) (hInv : IsUnit A) (hΩ : star Ω = -Ω)
    (hSmall : rotationErrorSq A Ω < (‖Ring.inverse A‖⁻¹) ^ 2) :
    IsUN (RotatingQuadratic.curvatureBounds A Ω hInv hSmall) (rotatingQuadratic A Ω) := by
  apply rotatingQuadratic_isUN_of_gap hA hΩ (Real.sqrt_nonneg _)
    (sub_pos.mp (rotation_gap_pos hSmall)) (inverse_norm_le_norm hInv) (inverse_norm_lower_bound hInv)
  rw [Real.sq_sqrt (show 0 ≤ rotationErrorSq A Ω by dsimp [rotationErrorSq]; positivity)]

/-- The gradient has the bi-Lipschitz constants `m - ρ` and `‖A‖ + ρ`. -/
theorem rotatingQuadratic_gradient_bounds {A Ω : H →L[ℝ] H}
    (hA : IsSelfAdjoint A) (hInv : IsUnit A) (hΩ : star Ω = -Ω)
    (hSmall : rotationErrorSq A Ω < (‖Ring.inverse A‖⁻¹) ^ 2) (x₁ x₂ : H) :
    let g := gradient (rotatingQuadratic A Ω)
    let m := ‖Ring.inverse A‖⁻¹
    let ρ := Real.sqrt (rotationErrorSq A Ω)
    (m - ρ) * ‖x₁ - x₂‖ ≤ ‖g x₁ - g x₂‖ ∧
    ‖g x₁ - g x₂‖ ≤ (‖A‖ + ρ) * ‖x₁ - x₂‖ := by
  have hUN := rotatingQuadratic_isUN hA hInv hΩ hSmall
  constructor
  · simpa [RotatingQuadratic.curvatureBounds, CurvatureBounds.muMin, CurvatureBounds.symmetric] using hUN.gradient_lower_bound x₁ x₂
  · simpa [RotatingQuadratic.curvatureBounds, CurvatureBounds.lMax, CurvatureBounds.symmetric] using hUN.gradient_upper_bound x₁ x₂

end UN.Examples
