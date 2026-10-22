module

public import UniformNondegeneracy.Core.Basic
public import UniformNondegeneracy.Analysis.StrongConvexity
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

/-!
# Strongly convex optimization with linear constraints

The Lagrangian of a smooth strongly convex energy is UN when the adjoint of the constraint operator has a positive lower norm bound. The four curvature parameters depend on the convexity and smoothness constants and the bounds on the constraint operator.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace UN.Examples

variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The Lagrangian for minimizing `f` subject to `A x = b`. -/
def lagrangian (f : H → ℝ) (A : H →L[ℝ] K) (b : K) (z : WithLp 2 (H × K)) : ℝ :=
  f z.fst + ⟪z.snd, A z.fst - b⟫

namespace Lagrangian

private lemma negative_root_magnitude {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    let m := (Real.sqrt (a ^ 2 + 4 * s ^ 2) - a) / 2
    0 < m ∧ m * (a + m) = s ^ 2 := by
  dsimp only
  have hSq := Real.sq_sqrt (show 0 ≤ a ^ 2 + 4 * s ^ 2 by positivity)
  have hSqrt := Real.sqrt_nonneg (a ^ 2 + 4 * s ^ 2)
  constructor <;> nlinarith [sq_pos_of_pos hs]

private lemma positive_root {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    let p := (Real.sqrt (a ^ 2 + 4 * s ^ 2) + a) / 2
    a ≤ p ∧ p * (p - a) = s ^ 2 := by
  dsimp only
  have h := negative_root_magnitude ha hs
  constructor <;> nlinarith [h.1, h.2]

/-- Curvature bounds for the Lagrangian of a smooth strongly convex energy with linear constraints. -/
def curvatureBounds (μ L σMin σMax : ℝ)
    (hμ : 0 < μ) (hμL : μ ≤ L) (hσ : 0 < σMin) (hσOrder : σMin ≤ σMax) :
    CurvatureBounds where
  muPlus := μ
  muMinus := (Real.sqrt (L ^ 2 + 4 * σMin ^ 2) - L) / 2
  lPlus := (Real.sqrt (L ^ 2 + 4 * σMax ^ 2) + L) / 2
  lMinus := (Real.sqrt (μ ^ 2 + 4 * σMax ^ 2) - μ) / 2
  muPlus_pos := hμ
  muMinus_pos := by exact (negative_root_magnitude (hμ.trans_le hμL) hσ).1
  muPlus_le_lPlus := by exact hμL.trans (positive_root (hμ.trans_le hμL) (hσ.trans_le hσOrder)).1
  muMinus_le_lMinus := by
    let m := (Real.sqrt (L ^ 2 + 4 * σMin ^ 2) - L) / 2
    let n := (Real.sqrt (μ ^ 2 + 4 * σMax ^ 2) - μ) / 2
    have hInner : 0 < m ∧ m * (L + m) = σMin ^ 2 := negative_root_magnitude (hμ.trans_le hμL) hσ
    have hOuter : 0 < n ∧ n * (μ + n) = σMax ^ 2 := negative_root_magnitude hμ (hσ.trans_le hσOrder)
    obtain ⟨hm, hmEq⟩ := hInner
    obtain ⟨hn, hnEq⟩ := hOuter
    change m ≤ n
    have hSq : σMin ^ 2 ≤ σMax ^ 2 := by nlinarith
    by_contra! hlt
    have hProd := mul_nonneg (sub_nonneg.mpr hμL) hm.le
    have hDiff := mul_pos (sub_pos.mpr hlt) (show 0 < m + n + μ by positivity)
    nlinarith

end Lagrangian

/-- The gradient of the Lagrangian consists of the stationarity and constraint residuals. -/
theorem hasGradientAt_lagrangian {f : H → ℝ} (A : H →L[ℝ] K) (b : K)
    {z : WithLp 2 (H × K)} {p : H} (hf : HasGradientAt f p z.fst) :
    HasGradientAt (lagrangian f A b) (WithLp.toLp 2 (p + A.adjoint z.snd, A z.fst - b)) z := by
  let fst := WithLp.fstL 2 ℝ H K
  let snd := WithLp.sndL 2 ℝ H K
  have h := (hf.hasFDerivAt.comp z fst.hasFDerivAt).add
    (snd.hasFDerivAt.inner ℝ ((A.hasFDerivAt.comp z fst.hasFDerivAt).sub_const b))
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  · rfl
  · ext v
    simp [fst, snd, InnerProductSpace.toDual_apply_apply, WithLp.prod_inner_apply,
      ContinuousLinearMap.adjoint_inner_left, inner_add_left, real_inner_comm, add_assoc]

theorem gradient_lagrangian {f : H → ℝ} (hf : Differentiable ℝ f)
    (A : H →L[ℝ] K) (b : K) (z : WithLp 2 (H × K)) :
    gradient (lagrangian f A b) z = WithLp.toLp 2 (gradient f z.fst + A.adjoint z.snd, A z.fst - b) :=
  (hasGradientAt_lagrangian A b (hf z.fst).hasGradientAt).gradient

/-- The constraint coupling contributes a bilinear term to the Bregman difference. -/
theorem bregman_lagrangian {f : H → ℝ} (hf : Differentiable ℝ f)
    (A : H →L[ℝ] K) (b : K) (z₁ z₂ : WithLp 2 (H × K)) :
    bregman (lagrangian f A b) z₁ z₂ = bregman f z₁.fst z₂.fst + ⟪z₁.snd - z₂.snd, A (z₁.fst - z₂.fst)⟫ := by
  simp [bregman, lagrangian, gradient_lagrangian hf, WithLp.prod_inner_apply,
    ContinuousLinearMap.adjoint_inner_left, inner_add_left, inner_sub_left, inner_sub_right, real_inner_comm]
  ring

omit [CompleteSpace H] in
private lemma norm_add_lower (u q w : H) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 < d)
    (hq : ‖q‖ ^ 2 ≤ c * ⟪q, u⟫) :
    d / (c + d) * ‖w‖ ^ 2 ≤ ‖q + w‖ ^ 2 + d * ⟪q, u⟫ := by
  rcases hc.eq_or_lt with hZero | hPos
  · subst c
    have hqZero : q = 0 := by
      have : ‖q‖ ^ 2 = 0 := by nlinarith
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp this)
    simp [hqZero, hd.ne']
  · have hSum : 0 < c + d := by positivity
    have hIdentity :
        c * ((c + d) * (‖q + w‖ ^ 2 + d * ⟪q, u⟫) - d * ‖w‖ ^ 2) =
          ‖(c + d) • q + c • w‖ ^ 2 + d * (c + d) * (c * ⟪q, u⟫ - ‖q‖ ^ 2) := by
      simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
        real_inner_smul_left, real_inner_smul_right]
      ring
    have hNonneg : 0 ≤ c * ((c + d) * (‖q + w‖ ^ 2 + d * ⟪q, u⟫) - d * ‖w‖ ^ 2) := by
      rw [hIdentity]
      exact add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hd.le hSum.le) (sub_nonneg.mpr hq))
    rw [div_mul_eq_mul_div, div_le_iff₀ hSum]
    apply (mul_le_mul_iff_right₀ hPos).mp
    nlinarith only [hNonneg]

private lemma quadratic_coupling_upper {L p S a b : ℝ}
    (hp : 0 < p) (hRoot : p * (p - L) = S ^ 2) :
    L / 2 * a ^ 2 + S * a * b ≤ p / 2 * (a ^ 2 + b ^ 2) := by
  have h := sq_nonneg (S * a - p * b)
  have hScaled := congrArg (fun t : ℝ => t * a ^ 2) hRoot
  apply (mul_le_mul_iff_right₀ hp).mp
  nlinarith only [h, hScaled]

private lemma quadratic_coupling_lower {μ n S a b : ℝ}
    (hn : 0 < n) (hRoot : n * (μ + n) = S ^ 2) :
    -(n / 2) * (a ^ 2 + b ^ 2) ≤ μ / 2 * a ^ 2 - S * a * b := by
  have h := sq_nonneg (S * a - n * b)
  have hScaled := congrArg (fun t : ℝ => t * a ^ 2) hRoot
  apply (mul_le_mul_iff_right₀ hn).mp
  nlinarith only [h, hScaled]

private theorem lagrangian_bregman_bounds {f : H → ℝ} {A : H →L[ℝ] K} (b : K)
    {μ L p n S : ℝ} (hp : 0 < p) (hn : 0 < n)
    (hpRoot : p * (p - L) = S ^ 2) (hnRoot : n * (μ + n) = S ^ 2)
    (hf : Differentiable ℝ f) (hBounds : HasBregmanBounds L (-μ) f) (hA : ‖A‖ ≤ S) :
    HasBregmanBounds p n (lagrangian f A b) := by
  have hCoupling (z₁ z₂ : WithLp 2 (H × K)) :
      |⟪z₁.snd - z₂.snd, A (z₁.fst - z₂.fst)⟫| ≤ S * ‖z₁.fst - z₂.fst‖ * ‖z₁.snd - z₂.snd‖ := by
    have hNorm := (A.le_opNorm (z₁.fst - z₂.fst)).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
    calc
      _ ≤ ‖z₁.snd - z₂.snd‖ * ‖A (z₁.fst - z₂.fst)‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖z₁.snd - z₂.snd‖ * (S * ‖z₁.fst - z₂.fst‖) :=
        mul_le_mul_of_nonneg_left hNorm (norm_nonneg _)
      _ = _ := by ring
  constructor
  · intro z₁ z₂
    rw [bregman_lagrangian hf, WithLp.prod_norm_sq_eq_of_L2]
    simp only [WithLp.sub_fst, WithLp.sub_snd]
    have hLower := hBounds.lower z₁.fst z₂.fst
    simp only [neg_div, neg_neg] at hLower
    have hCross := (abs_le.mp (hCoupling z₁ z₂)).1
    have hScalar := quadratic_coupling_lower (a := ‖z₁.fst - z₂.fst‖) (b := ‖z₁.snd - z₂.snd‖) hn hnRoot
    linarith
  · intro z₁ z₂
    rw [bregman_lagrangian hf, WithLp.prod_norm_sq_eq_of_L2]
    simp only [WithLp.sub_fst, WithLp.sub_snd]
    have hUpper := hBounds.upper z₁.fst z₂.fst
    have hCross := (abs_le.mp (hCoupling z₁ z₂)).2
    have hScalar := quadratic_coupling_upper (a := ‖z₁.fst - z₂.fst‖) (b := ‖z₁.snd - z₂.snd‖) hp hpRoot
    linarith

private lemma coupling_inner_secant (A : H →L[ℝ] K) {μ L m : ℝ}
    (hμ : 0 < μ) (hμL : μ ≤ L) (hm : 0 < m)
    (hLower : ∀ v, m * (L + m) * ‖v‖ ^ 2 ≤ ‖A.adjoint v‖ ^ 2)
    (u p : H) (v : K)
    (hCoco : ‖p - μ • u‖ ^ 2 ≤ (L - μ) * ⟪p - μ • u, u⟫) :
    let z := WithLp.toLp 2 (u, v)
    let g := WithLp.toLp 2 (p + A.adjoint v, A u)
    0 ≤ ⟪g + m • z, g - μ • z⟫ := by
  let q := p - μ • u
  have hLm : 0 < L + m := by linarith
  have hRatio : 0 ≤ (μ + m) / (L + m) := by positivity
  have hEstimate : m * (μ + m) * ‖v‖ ^ 2 ≤ ‖q + A.adjoint v‖ ^ 2 + (μ + m) * ⟪q, u⟫ := by
    calc
      _ = (μ + m) / (L + m) * (m * (L + m) * ‖v‖ ^ 2) := by field_simp
      _ ≤ (μ + m) / (L + m) * ‖A.adjoint v‖ ^ 2 := mul_le_mul_of_nonneg_left (hLower v) hRatio
      _ ≤ _ := by
        simpa only [show L - μ + (μ + m) = L + m by ring] using
          norm_add_lower u q (A.adjoint v) (sub_nonneg.mpr hμL) (add_pos hμ hm) hCoco
  have hIdentity :
      ⟪WithLp.toLp 2 (p + A.adjoint v, A u) + m • WithLp.toLp 2 (u, v),
        WithLp.toLp 2 (p + A.adjoint v, A u) - μ • WithLp.toLp 2 (u, v)⟫ =
      ‖A u + m • v‖ ^ 2 + ‖q + A.adjoint v‖ ^ 2 + (μ + m) * ⟪q, u⟫ - m * (μ + m) * ‖v‖ ^ 2 := by
    change ⟪p + A.adjoint v + m • u, p + A.adjoint v - μ • u⟫ + ⟪A u + m • v, A u - μ • v⟫ = _
    simp only [q, norm_add_sq_real, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    simp only [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
    ring
  dsimp only
  rw [hIdentity]
  nlinarith only [hEstimate, sq_nonneg ‖A u + m • v‖]

/-- The Lagrangian of a smooth strongly convex energy is uniformly nondegenerate under a positive lower bound on the adjoint constraint operator. -/
theorem lagrangian_isUN {f : H → ℝ} {A : H →L[ℝ] K} (b : K) {μ L σMin σMax : ℝ}
    (hμ : 0 < μ) (hμL : μ ≤ L) (hσ : 0 < σMin) (hσOrder : σMin ≤ σMax)
    (hf : Differentiable ℝ f) (hStrong : StrongConvexOn Set.univ μ f)
    (hLip : ∀ x₁ x₂, ‖gradient f x₁ - gradient f x₂‖ ≤ L * ‖x₁ - x₂‖)
    (hUpper : ‖A‖ ≤ σMax) (hLower : ∀ v, σMin * ‖v‖ ≤ ‖A.adjoint v‖) :
    IsUN (Lagrangian.curvatureBounds μ L σMin σMax hμ hμL hσ hσOrder) (lagrangian f A b) := by
  let bounds := Lagrangian.curvatureBounds μ L σMin σMax hμ hμL hσ hσOrder
  have hL : 0 < L := hμ.trans_le hμL
  have hS : 0 < σMax := hσ.trans_le hσOrder
  have hmRoot : bounds.muMinus * (L + bounds.muMinus) = σMin ^ 2 := (Lagrangian.negative_root_magnitude hL hσ).2
  have hpRoot : bounds.lPlus * (bounds.lPlus - L) = σMax ^ 2 := (Lagrangian.positive_root hL hS).2
  have hnRoot : bounds.lMinus * (μ + bounds.lMinus) = σMax ^ 2 := (Lagrangian.negative_root_magnitude hμ hS).2
  have hBounds := lagrangian_bregman_bounds b bounds.lPlus_pos bounds.lMinus_pos hpRoot hnRoot hf
    (strongConvexOn_hasBregmanBounds hf hStrong hLip) hUpper
  apply IsUN.of_hasGradient hBounds.hasGradientAt
  · intro z₁ z₂
    have hLowerSq (v : K) : bounds.muMinus * (L + bounds.muMinus) * ‖v‖ ^ 2 ≤ ‖A.adjoint v‖ ^ 2 := by
      rw [hmRoot]
      have := hLower v
      nlinarith [mul_nonneg hσ.le (norm_nonneg v)]
    have hCoco := strongConvexOn_cocoercive hμL hf hStrong hLip z₁.fst z₂.fst
    have h := coupling_inner_secant A hμ hμL bounds.muMinus_pos hLowerSq
      (z₁.fst - z₂.fst) (gradient f z₁.fst - gradient f z₂.fst) (z₁.snd - z₂.snd) hCoco
    have hDiff : gradient (lagrangian f A b) z₁ - gradient (lagrangian f A b) z₂ =
        WithLp.toLp 2 (gradient f z₁.fst - gradient f z₂.fst + A.adjoint (z₁.snd - z₂.snd), A (z₁.fst - z₂.fst)) := by
      rw [gradient_lagrangian hf, gradient_lagrangian hf]
      apply (WithLp.ofLp_injective 2)
      ext
      · simp
        module
      · simp
    rw [hDiff]
    exact h
  · exact hBounds.outer_secant (add_nonneg bounds.lPlus_pos.le bounds.lMinus_pos.le)

end UN.Examples
