module

public import UniformNondegeneracy.Analysis.GradientBounds
public import UniformNondegeneracy.Geometry.GradientInverse
public import UniformNondegeneracy.Geometry.InverseEnergy
public import UniformNondegeneracy.DAI.Normalization

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Secant bounds from balanced descent–ascent inequalities

Balanced DAI gives upper and lower secant bounds. After normalization to unit scales and a common weight, the sharp lower norm bound follows from nearly extremal secants of the inverse gradient.
-/

noncomputable section

namespace UN.HasDAI

open DAI

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-!
## Unit scales and the zero-weight case

At zero weight, the descent and ascent differences are orthogonal, so the normalized gradient preserves distances.
-/

private lemma inner_sub_add (u v : H) : ⟪u - v, u + v⟫ = ‖u‖ ^ 2 - ‖v‖ ^ 2 := by
  simp only [inner_sub_left, inner_add_right, real_inner_self_eq_norm_sq, real_inner_comm u v]
  ring

private lemma unit_dai {E : H → ℝ} {g : H → H} {r : ℝ} {hr : 0 ≤ r}
    (hDAI : HasDAI E g Scales.unit (Weights.symmetric r hr)) (x y z : H) :
    ⟪(x - y) - (g x - g y), (x - z) + (g x - g z)⟫ ≤
      r * (‖x - y‖ ^ 2 / 2 + ‖x - z‖ ^ 2 / 2 - bregman E g x y + bregman E g x z) := by
  have h := hDAI x y z
  simp only [descentStep, ascentStep, gradientStep, Scales.unit, Scales.tauPlus, Scales.tauMinus,
    Weights.symmetric, div_one, one_smul, neg_smul, sub_neg_eq_add, phiPlus, phiMinus, one_mul] at h
  convert h using 1
  · congr 1 <;> abel
  · ring

private lemma cross_inner_zero (a b : H → H)
    (ha : a 0 = 0) (hb : b 0 = 0) (hSum : ∀ x, a x + b x = (2 : ℝ) • x)
    (hCross : ∀ x y z, ⟪a x - a y, b x - b z⟫ ≤ 0) :
    ∀ x y, ⟪a x, b y⟫ = 0 := by
  have hNonpos (x y : H) : ⟪a x, b y⟫ ≤ 0 := by simpa [ha, hb] using hCross 0 x y
  have hLower (x y : H) : ⟪a x, b x⟫ ≤ ⟪a x, b y⟫ := by
    have h := hCross x 0 y
    simp only [ha, sub_zero, inner_sub_right] at h
    linarith
  intro x y
  let q := -((1 / 2 : ℝ) • a x)
  let w := b q
  have hw : w = -a x - a q := by
    have h := hSum q
    dsimp [q] at h
    norm_num [smul_smul] at h
    dsimp [w]
    apply eq_sub_iff_add_eq.mpr
    simpa [q, add_comm] using h
  have hBound (z : H) : 2 * ⟪w, z⟫ ≤ -⟪a x, b x⟫ - ⟪a q, b q⟫ := by
    have hIdentity : 2 * ⟪w, z⟫ = ⟪b q, a z⟫ - ⟪a x, b z⟫ - ⟪a q, b z⟫ := by
      calc
        _ = ⟪w, a z + b z⟫ := by rw [hSum, real_inner_smul_right]
        _ = _ := by
          rw [inner_add_right]
          conv_lhs => rhs; rw [hw]
          simp only [inner_sub_left, inner_neg_left, w]
          ring
    rw [hIdentity, real_inner_comm (a z) (b q)]
    linarith [hNonpos z q, hLower x z, hLower q z]
  have hwZero : w = 0 := by
    by_contra hwNe
    have hSq : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hwNe)
    let C := -⟪a x, b x⟫ - ⟪a q, b q⟫
    have h := hBound (((C + 1) / (2 * ‖w‖ ^ 2)) • w)
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq] at h
    have hValue : 2 * ((C + 1) / (2 * ‖w‖ ^ 2) * ‖w‖ ^ 2) = C + 1 := by field_simp
    rw [hValue] at h
    dsimp [C] at h
    linarith
  have hNeg : a q = -a x := by
    rw [hwZero] at hw
    exact (sub_eq_zero.mp hw.symm).symm
  have h := hNonpos q y
  rw [hNeg, inner_neg_left] at h
  exact le_antisymm (hNonpos x y) (by linarith)

private lemma unit_secant_zero {E : H → ℝ} {g : H → H}
    (hDAI : HasDAI E g Scales.unit (Weights.symmetric 0 le_rfl)) (x₁ x₂ : H) :
    ‖x₁ - x₂‖ ^ 2 - ‖g x₁ - g x₂‖ ^ 2 = 0 := by
  let a (x : H) := x - g x + g 0
  let b (x : H) := x + g x - g 0
  have hCross (x y z : H) : ⟪a x - a y, b x - b z⟫ ≤ 0 := by
    have h := unit_dai hDAI x y z
    rw [zero_mul] at h
    convert h using 1
    congr 1 <;> dsimp [a, b] <;> abel
  have h := cross_inner_zero a b (by simp [a]) (by simp [b]) (fun x => by dsimp [a, b]; module) hCross
  have hPair : ⟪a x₁ - a x₂, b x₁ - b x₂⟫ = 0 := by simp only [inner_sub_left, inner_sub_right, h]; ring
  have ha : a x₁ - a x₂ = (x₁ - x₂) - (g x₁ - g x₂) := by dsimp [a]; abel
  have hb : b x₁ - b x₂ = (x₁ - x₂) + (g x₁ - g x₂) := by dsimp [b]; abel
  rwa [ha, hb, inner_sub_add] at hPair

/-!
## Nearly extremal inverse secants

A nearly extremal directional secant controls the inverse gradient and its Bregman difference along the segment.
-/

private lemma near_extremal_inner (gInv : H → H) (p d : H) (K ε σ : ℝ)
    (hLip : ∀ p₁ p₂, ‖gInv p₁ - gInv p₂‖ ≤ K * ‖p₁ - p₂‖)
    (hσ : σ = 1 ∨ σ = -1)
    (hNear : (K - ε) * ‖d‖ ^ 2 ≤ σ * ⟪gInv (p + d) - gInv p, d⟫)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (K * s - ε) * ‖d‖ ^ 2 ≤ σ * ⟪gInv (p + s • d) - gInv p, d⟫ ∧
    σ * ⟪gInv (p + s • d) - gInv p, d⟫ ≤ K * s * ‖d‖ ^ 2 ∧
    |⟪gInv (p + s • d) - gInv p, d⟫ - σ * K * s * ‖d‖ ^ 2| ≤ ε * ‖d‖ ^ 2 := by
  have hσAbs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hAbs (p₁ p₂ : H) : |σ * ⟪gInv p₁ - gInv p₂, d⟫| ≤ K * ‖p₁ - p₂‖ * ‖d‖ := by
    rw [abs_mul, hσAbs, one_mul]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hLip p₁ p₂) (norm_nonneg d))
  have hUpper := (abs_le.mp (hAbs (p + s • d) p)).2
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1] at hUpper
  have hEnd := (abs_le.mp (hAbs (p + d) (p + s • d))).2
  rw [show p + d - (p + s • d) = (1 - s) • d by module] at hEnd
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.2)] at hEnd
  have hSplit : ⟪gInv (p + d) - gInv p, d⟫ =
      ⟪gInv (p + d) - gInv (p + s • d), d⟫ + ⟪gInv (p + s • d) - gInv p, d⟫ := by
    simp only [inner_sub_left]
    ring
  have hLower : (K * s - ε) * ‖d‖ ^ 2 ≤ σ * ⟪gInv (p + s • d) - gInv p, d⟫ := by
    rw [hSplit, mul_add] at hNear
    nlinarith only [hNear, hEnd]
  refine ⟨hLower, by nlinarith only [hUpper], ?_⟩
  apply abs_le.mpr
  rcases hσ with rfl | rfl <;> simp only [one_mul, neg_one_mul] at * <;> constructor <;> nlinarith only [hLower, hUpper]

private lemma segment_norm_sq_le (gInv : H → H) (p d : H) (K : ℝ)
    (hK : 0 ≤ K) (hLip : ∀ p₁ p₂, ‖gInv p₁ - gInv p₂‖ ≤ K * ‖p₁ - p₂‖) (a b : ℝ) :
    ‖gInv (p + a • d) - gInv (p + b • d)‖ ^ 2 ≤ K ^ 2 * (a - b) ^ 2 * ‖d‖ ^ 2 := by
  have h := hLip (p + a • d) (p + b • d)
  have hSq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mpr h
  rw [show p + a • d - (p + b • d) = (a - b) • d by module] at hSq
  simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_assoc] using hSq

private lemma near_extremal_norm_sq (gInv : H → H) (p d : H) (K ε σ : ℝ)
    (hK : 0 ≤ K) (hσ : σ = 1 ∨ σ = -1)
    (hLip : ∀ p₁ p₂, ‖gInv p₁ - gInv p₂‖ ≤ K * ‖p₁ - p₂‖)
    (hNear : (K - ε) * ‖d‖ ^ 2 ≤ σ * ⟪gInv (p + d) - gInv p, d⟫)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (K ^ 2 * s ^ 2 - 2 * K * s * ε) * ‖d‖ ^ 2 ≤ ‖gInv (p + s • d) - gInv p‖ ^ 2 ∧
    ‖gInv (p + s • d) - gInv p‖ ^ 2 ≤ K ^ 2 * s ^ 2 * ‖d‖ ^ 2 := by
  have hInner := (near_extremal_inner gInv p d K ε σ hLip hσ hNear hs).1
  have hSq := sq_nonneg ‖(gInv (p + s • d) - gInv p) - (σ * K * s) • d‖
  have hσSq : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  rw [norm_sub_sq_real] at hSq
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right, hσSq, one_mul] at hSq
  constructor
  · have hm := mul_le_mul_of_nonneg_left hInner (mul_nonneg hK hs.1)
    nlinarith only [hSq, hm]
  · simpa only [zero_smul, add_zero, sub_zero] using segment_norm_sq_le gInv p d K hK hLip s 0

variable [CompleteSpace H]

private lemma segment_bregman_error (EInv : H → ℝ) (gInv : H → H) (p d : H) (c ε : ℝ)
    (hGrad : ∀ p, HasGradientAt EInv (gInv p) p)
    (hInner : ∀ s ∈ Set.Icc (0 : ℝ) 1, |⟪gInv (p + s • d) - gInv p, d⟫ - c * s * ‖d‖ ^ 2| ≤ ε * ‖d‖ ^ 2)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    |bregman EInv gInv (p + s • d) p - c / 2 * s ^ 2 * ‖d‖ ^ 2| ≤ ε * s * ‖d‖ ^ 2 := by
  let f (s : ℝ) := bregman EInv gInv (p + s • d) p - c / 2 * s ^ 2 * ‖d‖ ^ 2
  let f' (s : ℝ) := ⟪gInv (p + s • d) - gInv p, d⟫ - c * s * ‖d‖ ^ 2
  have hf (s : ℝ) : HasDerivAt f (f' s) s := by
    have hg := (hGrad (p + s • d)).hasFDerivAt.comp_hasDerivAt s
      (((hasDerivAt_id s).smul_const d).const_add p)
    convert ((hg.sub_const (EInv p)).sub ((hasDerivAt_id s).mul_const ⟪gInv p, d⟫)).sub
      ((((hasDerivAt_id s).pow 2).const_mul (c / 2)).mul_const (‖d‖ ^ 2)) using 1
    · ext s
      simp [f, bregman, real_inner_smul_right]
    · simp only [f', one_smul, InnerProductSpace.toDual_apply_apply, inner_sub_left, Nat.cast_ofNat, mul_one, id_eq]
      ring
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hf s).hasDerivWithinAt) (fun s hs => by simpa only [Real.norm_eq_abs] using hInner s hs)
    (convex_Icc (0 : ℝ) 1) (by simp : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1) hs
  simpa [f, Real.norm_eq_abs, abs_of_nonneg hs.1, mul_comm, mul_left_comm, mul_assoc] using h

/-!
## The sharp inverse Lipschitz bound

Testing the normalized DAI along these segments bounds the optimal inverse Lipschitz constant `K` by $K^{2}(1-r^{2}) \le 1$, where `r` is the common DAI weight.
-/

private lemma near_extremal_dai {E : H → ℝ} {g : H → H} {r : ℝ} {hr : 0 ≤ r}
    (hDAI : HasDAI E g Scales.unit (Weights.symmetric r hr))
    (gInv : H → H) (hRightInverse : Function.RightInverse gInv g)
    (hGradInv : ∀ p, HasGradientAt (inverseEnergy E gInv) (gInv p) p)
    (K ε σ : ℝ) (hK : 0 ≤ K) (hσ : σ = 1 ∨ σ = -1)
    (hLip : ∀ p₁ p₂, ‖gInv p₁ - gInv p₂‖ ≤ K * ‖p₁ - p₂‖)
    (p d : H) (hd : d ≠ 0)
    (hNear : (K - ε) * ‖d‖ ^ 2 ≤ σ * ⟪gInv (p + d) - gInv p, d⟫)
    (a b : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    (K ^ 2 - 1) * a * b - (K + 1 + r) * (a + b) * ε ≤
      r / 2 * ((K ^ 2 - σ * K) * a ^ 2 + (K ^ 2 + σ * K) * b ^ 2) := by
  let v (s : ℝ) := gInv (p + s • d) - gInv p
  let Q := ‖d‖ ^ 2
  have hQ : 0 < Q := sq_pos_of_pos (norm_pos_iff.mpr hd)
  have hNorm (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      (K ^ 2 * s ^ 2 - 2 * K * s * ε) * Q ≤ ‖v s‖ ^ 2 ∧ ‖v s‖ ^ 2 ≤ K ^ 2 * s ^ 2 * Q :=
    near_extremal_norm_sq gInv p d K ε σ hK hσ hLip hNear hs
  have hInner (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      |⟪v s, d⟫ - σ * K * s * Q| ≤ ε * Q :=
    (near_extremal_inner gInv p d K ε σ hLip hσ hNear hs).2.2
  have hBregman (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      |bregman (inverseEnergy E gInv) gInv (p + s • d) p - σ * K / 2 * s ^ 2 * Q| ≤ ε * s * Q :=
    segment_bregman_error (inverseEnergy E gInv) gInv p d (σ * K) ε hGradInv hInner hs
  have hDiff : ‖v a - v b‖ ^ 2 ≤ K ^ 2 * (a - b) ^ 2 * Q := by
    have h := segment_norm_sq_le gInv p d K hK hLip a b
    simpa only [v, sub_sub_sub_cancel_right] using h
  have hCross : (K ^ 2 * a * b - K * (a + b) * ε) * Q ≤ ⟪v a, v b⟫ := by
    rw [norm_sub_sq_real] at hDiff
    nlinarith only [hDiff, (hNorm a ha).1, (hNorm b hb).1]
  have hMixed : -(a + b) * ε * Q ≤ b * ⟪v a, d⟫ - a * ⟪v b, d⟫ := by
    have h₁ := mul_le_mul_of_nonneg_left (abs_le.mp (hInner a ha)).1 hb.1
    have h₂ := mul_le_mul_of_nonneg_left (abs_le.mp (hInner b hb)).2 ha.1
    nlinarith only [h₁, h₂]
  have hModel :
      ‖v a‖ ^ 2 / 2 + ‖v b‖ ^ 2 / 2 - bregman (inverseEnergy E gInv) gInv (p + a • d) p + bregman (inverseEnergy E gInv) gInv (p + b • d) p ≤
      ((K ^ 2 - σ * K) * a ^ 2 + (K ^ 2 + σ * K) * b ^ 2) / 2 * Q + (a + b) * ε * Q := by
    nlinarith only [(hNorm a ha).2, (hNorm b hb).2,
      (abs_le.mp (hBregman a ha)).1, (abs_le.mp (hBregman b hb)).2]
  have hDAIInv := unit_dai hDAI (gInv p) (gInv (p + a • d)) (gInv (p + b • d))
  rw [hRightInverse p, hRightInverse (p + a • d), hRightInverse (p + b • d)] at hDAIInv
  rw [← bregman_inverseEnergy E g gInv hRightInverse (p + a • d) p,
    ← bregman_inverseEnergy E g gInv hRightInverse (p + b • d) p] at hDAIInv
  have hPrimal (s : ℝ) : gInv p - gInv (p + s • d) = -v s := by dsimp [v]; abel
  have hDual (s : ℝ) : p - (p + s • d) = -(s • d) := by abel
  rw [hPrimal a, hPrimal b, hDual a, hDual b] at hDAIInv
  rw [show -v a - -(a • d) = -(v a - a • d) by abel,
    show -v b + -(b • d) = -(v b + b • d) by abel, inner_neg_neg, norm_neg, norm_neg] at hDAIInv
  have hExpanded : ⟪v a - a • d, v b + b • d⟫ =
      ⟪v a, v b⟫ + b * ⟪v a, d⟫ - a * ⟪v b, d⟫ - a * b * Q := by
    simp only [inner_sub_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_comm (v b) d, Q]
    ring
  rw [hExpanded] at hDAIInv
  have hUpper := mul_le_mul_of_nonneg_left hModel hr
  apply (mul_le_mul_iff_right₀ hQ).mp
  nlinarith only [hDAIInv, hUpper, hCross, hMixed]

private lemma sharp_constant_of_tests (K r : ℝ) (hK : 1 < K) (hr : 0 < r)
    (hTest : ∀ ε : ℝ, 0 < ε → ε < K →
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
          (K ^ 2 - 1) * a * b - (K + 1 + r) * (a + b) * ε ≤
            r / 2 * ((K ^ 2 - σ * K) * a ^ 2 + (K ^ 2 + σ * K) * b ^ 2)) :
    K ^ 2 * (1 - r ^ 2) ≤ 1 := by
  let denom := r * K + K - 1
  let a := r * K / denom
  let b := (K - 1) / denom
  have hKPos : 0 < K := lt_trans zero_lt_one hK
  have hDenom : 0 < denom := by dsimp [denom]; nlinarith [mul_pos hr hKPos]
  have ha : a ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (mul_nonneg hr.le hKPos.le) hDenom.le, (div_le_one hDenom).mpr ?_⟩
    dsimp [denom]
    linarith
  have hb : b ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (sub_nonneg.mpr hK.le) hDenom.le, (div_le_one hDenom).mpr ?_⟩
    dsimp [denom]
    nlinarith [mul_pos hr hKPos]
  have hSum : a + b = 1 := by
    change r * K / denom + (K - 1) / denom = 1
    rw [← add_div, show r * K + (K - 1) = denom by dsimp [denom]; ring, div_self hDenom.ne']
  let testValue := r / 2 * ((K ^ 2 - K) * a ^ 2 + (K ^ 2 + K) * b ^ 2) - (K ^ 2 - 1) * a * b
  have hApprox (ε : ℝ) (hε : 0 < ε) (hεK : ε < K) : -(K + 1 + r) * ε ≤ testValue := by
    obtain ⟨σ, hσ, h⟩ := hTest ε hε hεK
    rcases hσ with rfl | rfl
    · have ht := h a b ha hb
      rw [hSum] at ht
      dsimp [testValue]
      nlinarith only [ht]
    · have ht := h b a hb ha
      rw [add_comm b a, hSum] at ht
      dsimp [testValue]
      nlinarith only [ht]
  have hTestNonneg : 0 ≤ testValue := by
    by_contra hTestNonneg
    have hTestNeg : testValue < 0 := lt_of_not_ge hTestNonneg
    have hC : 0 < 2 * (K + 1 + r) := by linarith
    let ε := min (K / 2) (-testValue / (2 * (K + 1 + r)))
    have hε : 0 < ε := lt_min (by positivity) (div_pos (neg_pos.mpr hTestNeg) hC)
    have hεK : ε < K := (min_le_left _ _).trans_lt (by linarith)
    have hεBound := (le_div_iff₀ hC).mp (min_le_right (K / 2) (-testValue / (2 * (K + 1 + r))))
    have h := hApprox ε hε hεK
    change ε * (2 * (K + 1 + r)) ≤ -testValue at hεBound
    nlinarith only [h, hεBound, hTestNeg]
  have hFactor : testValue = (r * K * (K - 1) / (2 * denom ^ 2)) * (r ^ 2 * K ^ 2 - (K ^ 2 - 1)) := by
    dsimp [testValue, a, b]
    field_simp [show r * K + K - 1 ≠ 0 from hDenom.ne']
    ring
  have hFactorPos : 0 < r * K * (K - 1) / (2 * denom ^ 2) := by positivity
  rw [hFactor] at hTestNonneg
  have h := nonneg_of_mul_nonneg_right hTestNonneg hFactorPos
  nlinarith only [h]

private lemma unit_inverse_lipschitz_bound {E : H → ℝ} {g : H → H} {r : ℝ} {hr : 0 ≤ r}
    (hDAI : HasDAI E g Scales.unit (Weights.symmetric r hr)) (hrPos : 0 < r)
    (gInv : H → H) (hRightInverse : Function.RightInverse gInv g)
    (hGradInv : ∀ p, HasGradientAt (inverseEnergy E gInv) (gInv p) p)
    (L : ℝ) (hL : 0 ≤ L) (hLip : ∀ p₁ p₂, ‖gInv p₁ - gInv p₂‖ ≤ L * ‖p₁ - p₂‖) :
    ∃ K : ℝ, 0 ≤ K ∧ (∀ p₁ p₂, ‖gInv p₁ - gInv p₂‖ ≤ K * ‖p₁ - p₂‖) ∧ K ^ 2 * (1 - r ^ 2) ≤ 1 := by
  obtain ⟨K, hK, _, hKLip, _, hNear⟩ := GradientMap.exists_optimal_lipschitz_bound hGradInv hL hLip
  refine ⟨K, hK, hKLip, ?_⟩
  by_cases hKOne : K ≤ 1
  · nlinarith [mul_nonneg (sq_nonneg K) (sq_nonneg r)]
  · apply sharp_constant_of_tests K r (lt_of_not_ge hKOne) hrPos
    intro ε hε hεK
    obtain ⟨p₁, p₂, hNe, h⟩ := hNear ε hε hεK
    have hSign : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        (K - ε) * ‖p₁ - p₂‖ ^ 2 ≤ σ * ⟪gInv p₁ - gInv p₂, p₁ - p₂⟫ := by
      by_cases hInner : 0 ≤ ⟪gInv p₁ - gInv p₂, p₁ - p₂⟫
      · exact ⟨1, Or.inl rfl, by simpa only [one_mul, abs_of_nonneg hInner] using h.le⟩
      · exact ⟨-1, Or.inr rfl, by simpa only [neg_one_mul, abs_of_neg (lt_of_not_ge hInner)] using h.le⟩
    obtain ⟨σ, hσ, hSign⟩ := hSign
    refine ⟨σ, hσ, fun a b ha hb => near_extremal_dai hDAI gInv hRightInverse hGradInv
      K ε σ hK hσ hKLip p₂ (p₁ - p₂) (sub_ne_zero.mpr hNe) ?_ a b ha hb⟩
    simpa only [show p₂ + (p₁ - p₂) = p₁ by abel] using hSign

/-!
## Recovering the secant bounds

For $0 < r < 1$, a preliminary lower norm bound makes the gradient invertible. The sharp inverse estimate then gives the lower norm bound needed for the normalized secants, which are transferred back to the original scales.
-/

private lemma unit_secant_bounds {E : H → ℝ} {g : H → H} {r : ℝ} {hr : 0 ≤ r}
    (hDAI : HasDAI E g Scales.unit (Weights.symmetric r hr)) (x₁ x₂ : H) :
    0 ≤ ‖x₁ - x₂‖ ^ 2 - ‖g x₁ - g x₂‖ ^ 2 ∧
    ‖x₁ - x₂‖ ^ 2 - ‖g x₁ - g x₂‖ ^ 2 ≤ r ^ 2 * ‖x₁ - x₂‖ ^ 2 := by
  rcases hr.eq_or_lt with hZero | hrPos
  · subst r
    rw [unit_secant_zero hDAI]
    simp
  have hBounds : HasBregmanBounds E g 1 1 := hDAI.hasBregmanBounds hrPos hrPos
  have hLip (x₁ x₂ : H) : ‖g x₁ - g x₂‖ ≤ ‖x₁ - x₂‖ := by
    simpa only [one_mul] using hBounds.norm_sub_le zero_le_one x₁ x₂
  have hOuter := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hLip x₁ x₂)
  refine ⟨by linarith, ?_⟩
  by_cases hrOne : 1 ≤ r
  · have hMul := mul_nonneg (show 0 ≤ r ^ 2 - 1 by nlinarith) (sq_nonneg ‖x₁ - x₂‖)
    nlinarith [sq_nonneg ‖g x₁ - g x₂‖]
  have hrLt : r < 1 := lt_of_not_ge hrOne
  have hμ : 0 < 1 - r := sub_pos.mpr hrLt
  have hLower (x₁ x₂ : H) : (1 - r) * ‖x₁ - x₂‖ ≤ ‖g x₁ - g x₂‖ := by
    have h := unit_dai hDAI x₁ x₂ x₂
    rw [inner_sub_add] at h
    have hSq : ((1 - r) * ‖x₁ - x₂‖) ^ 2 ≤ ‖g x₁ - g x₂‖ ^ 2 := by
      have hMargin := mul_nonneg (mul_nonneg hrPos.le hμ.le) (sq_nonneg ‖x₁ - x₂‖)
      nlinarith only [h, hMargin]
    exact (sq_le_sq₀ (mul_nonneg hμ.le (norm_nonneg _)) (norm_nonneg _)).mp hSq
  have hGrad := hBounds.hasGradientAt
  have hBijective := GradientMap.bijective_of_bounds E g (1 - r) 1 hGrad hμ (by linarith)
    hLower (fun x₁ x₂ => by simpa only [one_mul] using hLip x₁ x₂)
  let gInv := Function.invFun g
  have hRightInverse : Function.RightInverse gInv g := Function.rightInverse_invFun hBijective.2
  have hLeftInverse : Function.LeftInverse gInv g := Function.leftInverse_invFun hBijective.1
  have hInvLip := GradientMap.inverse_norm_sub_le g gInv (1 - r) hμ hLower hRightInverse
  have hInvNonneg : 0 ≤ (1 - r)⁻¹ := inv_nonneg.mpr hμ.le
  have hContinuous : Continuous gInv := by
    have hLipschitz : LipschitzWith ⟨(1 - r)⁻¹, hInvNonneg⟩ gInv := by
      apply LipschitzWith.of_dist_le_mul
      intro p₁ p₂
      simp only [dist_eq_norm]
      exact_mod_cast hInvLip p₁ p₂
    exact hLipschitz.continuous
  have hGradInv := GradientMap.hasGradientAt_inverseEnergy E g gInv (1 - r)⁻¹ hGrad hRightInverse hContinuous hInvLip
  obtain ⟨K, hK, hKLip, hSharp⟩ := unit_inverse_lipschitz_bound hDAI hrPos gInv hRightInverse hGradInv
    (1 - r)⁻¹ hInvNonneg hInvLip
  have hInv := hKLip (g x₁) (g x₂)
  rw [hLeftInverse x₁, hLeftInverse x₂] at hInv
  have hInvSq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mpr hInv
  have hGap : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hScaled := mul_le_mul_of_nonneg_left hInvSq hGap
  have hSharpScaled := mul_le_mul_of_nonneg_right hSharp (sq_nonneg ‖g x₁ - g x₂‖)
  nlinarith only [hScaled, hSharpScaled]

/-- A balanced DAI bounds the two-point product of descent and ascent differences. -/
theorem secant_bounds_of_balanced {E : H → ℝ} {g : H → H} {Λ : Scales} {ρ : Weights}
    (hDAI : HasDAI E g Λ ρ) (hBalanced : ρ.Balanced Λ) (x₁ x₂ : H) :
    0 ≤ ⟪descentStep g Λ x₁ - descentStep g Λ x₂, ascentStep g Λ x₁ - ascentStep g Λ x₂⟫ ∧
    ⟪descentStep g Λ x₁ - descentStep g Λ x₂, ascentStep g Λ x₁ - ascentStep g Λ x₂⟫ ≤ ρ.plus * ρ.minus * ‖x₁ - x₂‖ ^ 2 := by
  have h := unit_secant_bounds (hDAI.normalized hBalanced) x₁ x₂
  have hIdentity := step_inner_normalized g Λ x₁ x₂ x₂
  rw [step_inner_unit] at hIdentity
  rw [hIdentity] at h
  have hFactor : 0 < Λ.plus * Λ.minus / Λ.radius ^ 2 :=
    div_pos (mul_pos Λ.plus_pos Λ.minus_pos) (sq_pos_of_pos Λ.radius_pos)
  refine ⟨nonneg_of_mul_nonneg_right h.1 hFactor, ?_⟩
  apply (mul_le_mul_iff_right₀ hFactor).mp
  have hUpper := h.2
  rw [normalizedWeight_sq Λ ρ hBalanced] at hUpper
  nlinarith only [hUpper]

/-- The secant bounds expressed in curvature form. -/
theorem curvature_secant_bounds_of_balanced {E : H → ℝ} {g : H → H} {Λ : Scales} {ρ : Weights}
    (hDAI : HasDAI E g Λ ρ) (hBalanced : ρ.Balanced Λ) (x₁ x₂ : H) :
    -(ρ.plus * ρ.minus * (Λ.plus * Λ.minus)) * ‖x₁ - x₂‖ ^ 2 ≤ ⟪g x₁ - g x₂ + Λ.minus • (x₁ - x₂), g x₁ - g x₂ - Λ.plus • (x₁ - x₂)⟫ ∧
    ⟪g x₁ - g x₂ + Λ.minus • (x₁ - x₂), g x₁ - g x₂ - Λ.plus • (x₁ - x₂)⟫ ≤ 0 := by
  have h := hDAI.secant_bounds_of_balanced hBalanced x₁ x₂
  have hLower := mul_nonneg (mul_nonneg Λ.plus_pos.le Λ.minus_pos.le) h.1
  have hUpper := mul_le_mul_of_nonneg_left h.2 (mul_nonneg Λ.plus_pos.le Λ.minus_pos.le)
  rw [step_inner_mul_scales] at hLower hUpper
  constructor <;> nlinarith only [hLower, hUpper]

end UN.HasDAI
