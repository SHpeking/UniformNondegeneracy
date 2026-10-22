module

public import UniformNondegeneracy.Analysis.Bregman

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Equivalent global bounds for gradient maps

Symmetric quadratic Bregman bounds control the Lipschitz constant of the gradient. For a gradient field, an absolute bound on the inner-product secants gives the same constant.
-/

namespace UN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Completing the square in a two-sided secant expression. -/
theorem centered_secant_identity (u v : H) (a b : ℝ) :
    ‖u - ((a - b) / 2) • v‖ ^ 2 - ((a + b) / 2) ^ 2 * ‖v‖ ^ 2 = ⟪u + b • v, u - a • v⟫ := by
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_sub_right, inner_add_left, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm v u]
  ring

/-- An outer secant inequality bounds the norm by the larger curvature. -/
theorem norm_le_of_outer_secant (u v : H) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hSecant : ⟪u + b • v, u - a • v⟫ ≤ 0) :
    ‖u‖ ≤ max a b * ‖v‖ := by
  rw [← centered_secant_identity] at hSecant
  have hCentered : ‖u - ((a - b) / 2) • v‖ ≤ (a + b) / 2 * ‖v‖ := by
    nlinarith [norm_nonneg (u - ((a - b) / 2) • v),
      mul_nonneg (show 0 ≤ (a + b) / 2 by positivity) (norm_nonneg v)]
  have hTriangle := norm_add_le (u - ((a - b) / 2) • v) (((a - b) / 2) • v)
  rw [sub_add_cancel, norm_smul, Real.norm_eq_abs] at hTriangle
  have hMax : (a + b) / 2 + |(a - b) / 2| = max a b := by
    rcases le_total a b with hab | hba
    · rw [max_eq_right hab, abs_of_nonpos (by linarith)]
      ring
    · rw [max_eq_left hba, abs_of_nonneg (by linarith)]
      ring
  rw [← hMax]
  nlinarith

variable [CompleteSpace H]

/-- Symmetric global quadratic models imply the matching gradient norm bound. -/
theorem HasBregmanBounds.norm_sub_le {E : H → ℝ} {L : ℝ}
    (hBounds : HasBregmanBounds L L E) (hL : 0 ≤ L) (x₁ x₂ : H) :
    ‖gradient E x₁ - gradient E x₂‖ ≤ L * ‖x₁ - x₂‖ := by
  rcases hL.eq_or_lt with hZero | hPos
  · subst L
    have hB (x₁ x₂ : H) : bregman E x₁ x₂ = 0 := by
      have h₁ := hBounds.lower x₁ x₂
      have h₂ := hBounds.upper x₁ x₂
      simp only [zero_div, neg_zero, zero_mul] at h₁ h₂
      exact le_antisymm h₂ h₁
    have h := bregman_three_point E (x₁ + (gradient E x₁ - gradient E x₂)) x₁ x₂
    simp only [hB, add_sub_cancel_left, real_inner_self_eq_norm_sq] at h
    simp only [zero_mul]
    nlinarith [norm_nonneg (gradient E x₁ - gradient E x₂)]
  · have h₁ := hBounds.interpolation_upper (by linarith) x₁ x₂
    have h₂ := hBounds.interpolation_upper (by linarith) x₂ x₁
    rw [norm_sub_rev x₂ x₁, norm_sub_rev (gradient E x₂) (gradient E x₁)] at h₂
    have hi : ⟪x₂ - x₁, gradient E x₂ - gradient E x₁⟫ = ⟪x₁ - x₂, gradient E x₁ - gradient E x₂⟫ := by
      rw [← neg_sub x₁ x₂, ← neg_sub (gradient E x₁) (gradient E x₂), inner_neg_neg]
    rw [hi] at h₂
    have hDen : 0 < 2 * (L + L) := by linarith
    have hm₁ := (le_div_iff₀ hDen).mp h₁
    have hm₂ := (le_div_iff₀ hDen).mp h₂
    have hSum := bregman_add_reverse E x₁ x₂
    rw [real_inner_comm (x₁ - x₂) (gradient E x₁ - gradient E x₂)] at hSum
    have hSq : ‖gradient E x₁ - gradient E x₂‖ ^ 2 ≤ L ^ 2 * ‖x₁ - x₂‖ ^ 2 := by nlinarith
    nlinarith [norm_nonneg (gradient E x₁ - gradient E x₂), mul_nonneg hPos.le (norm_nonneg (x₁ - x₂))]

/-- Bregman bounds give the corresponding outer secant inequality. -/
theorem HasBregmanBounds.outer_secant {E : H → ℝ} {LPlus LMinus : ℝ}
    (hBounds : HasBregmanBounds LPlus LMinus E)
    (hSum : 0 ≤ LPlus + LMinus) (x₁ x₂ : H) :
    ⟪gradient E x₁ - gradient E x₂ + LMinus • (x₁ - x₂), gradient E x₁ - gradient E x₂ - LPlus • (x₁ - x₂)⟫ ≤ 0 := by
  let c := (LPlus - LMinus) / 2
  let r := (LPlus + LMinus) / 2
  let F := fun x => E x - c / 2 * ‖x‖ ^ 2
  let G := fun x => gradient E x - c • x
  have hGradientF : gradient F = G := by
    apply gradient_eq
    intro x
    rw [hasGradientAt_iff_hasFDerivAt]
    convert (hBounds.hasGradientAt x).hasFDerivAt.sub
      (hasGradientAt_quadratic c (0 : H) x).hasFDerivAt using 1
    · ext y
      simp [F]
    · simp [G, InnerProductSpace.toDual]
  have hShift (x₁ x₂ : H) :
      bregman F x₁ x₂ = bregman E x₁ x₂ - c / 2 * ‖x₁ - x₂‖ ^ 2 := by
    simp only [bregman, hGradientF, F, G, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_self_eq_norm_sq, norm_sub_sq_real]
    rw [real_inner_comm x₂ x₁]
    ring
  have hCentered : HasBregmanBounds r r F := by
    constructor
    · intro x₁ x₂
      rw [hShift]
      have := hBounds.lower x₁ x₂
      dsimp [r, c]
      linarith
    · intro x₁ x₂
      rw [hShift]
      have := hBounds.upper x₁ x₂
      dsimp [r, c]
      linarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hNorm := hCentered.norm_sub_le hr x₁ x₂
  have hG : G x₁ - G x₂ = gradient E x₁ - gradient E x₂ - c • (x₁ - x₂) := by dsimp [G]; module
  rw [hGradientF, hG] at hNorm
  rw [← centered_secant_identity]
  change ‖gradient E x₁ - gradient E x₂ - c • (x₁ - x₂)‖ ^ 2 - r ^ 2 * ‖x₁ - x₂‖ ^ 2 ≤ 0
  nlinarith [norm_nonneg (gradient E x₁ - gradient E x₂ - c • (x₁ - x₂)), mul_nonneg hr (norm_nonneg (x₁ - x₂))]

/-- Global quadratic Bregman bounds imply continuous differentiability. -/
theorem HasBregmanBounds.contDiff
    {E : H → ℝ} {LPlus LMinus : ℝ}
    (hBounds : HasBregmanBounds LPlus LMinus E) :
    ContDiff ℝ 1 E := by
  let L := max |LPlus| |LMinus|
  have hL : 0 ≤ L := (abs_nonneg LPlus).trans (le_max_left _ _)
  have hPlus : LPlus ≤ L := (le_abs_self _).trans (le_max_left _ _)
  have hMinus : LMinus ≤ L := (le_abs_self _).trans (le_max_right _ _)
  have hLip : LipschitzWith ⟨L, hL⟩ (gradient E) :=
    lipschitzWith_iff_norm_sub_le.mpr ((hBounds.mono hPlus hMinus).norm_sub_le hL)
  refine contDiff_one_iff_fderiv.mpr ⟨fun x => (hBounds.hasGradientAt x).differentiableAt, ?_⟩
  have hDeriv : fderiv ℝ E = fun x => (InnerProductSpace.toDual ℝ H) (gradient E x) :=
    funext fun x => (hBounds.hasGradientAt x).hasFDerivAt.fderiv
  rw [hDeriv]
  exact (InnerProductSpace.toDual ℝ H).continuous.comp hLip.continuous

namespace GradientMap

variable {E : H → ℝ} {g : H → H} {L : ℝ}

/-- Absolute inner-product secants give symmetric Bregman bounds. -/
theorem hasBregmanBounds_of_abs_inner_le
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (hInner : ∀ x₁ x₂, |⟪g x₁ - g x₂, x₁ - x₂⟫| ≤ L * ‖x₁ - x₂‖ ^ 2) :
    HasBregmanBounds L L E := by
  constructor
  · intro x₁ x₂
    have h := taylor_lower_bound_of_inner E g (-L) hGrad
      (fun x₁ x₂ => by have := (abs_le.mp (hInner x₁ x₂)).1; linarith) x₂ (x₁ - x₂)
    rw [show x₂ + (x₁ - x₂) = x₁ by abel] at h
    simp only [bregman, gradient_eq hGrad]
    linarith
  · intro x₁ x₂
    have h := taylor_upper_bound_of_inner E g L hGrad
      (fun x₁ x₂ => (abs_le.mp (hInner x₁ x₂)).2) x₂ (x₁ - x₂)
    simpa [bregman, gradient_eq hGrad] using h

/-- A gradient has the same constant in its norm and absolute inner-product secant bounds. -/
theorem norm_sub_le_iff_abs_inner_le (hGrad : ∀ x, HasGradientAt E (g x) x) (hL : 0 ≤ L) :
    (∀ x₁ x₂, ‖g x₁ - g x₂‖ ≤ L * ‖x₁ - x₂‖) ↔
    (∀ x₁ x₂, |⟪g x₁ - g x₂, x₁ - x₂⟫| ≤ L * ‖x₁ - x₂‖ ^ 2) := by
  constructor
  · intro hLip x₁ x₂
    calc
      _ ≤ ‖g x₁ - g x₂‖ * ‖x₁ - x₂‖ := abs_real_inner_le_norm _ _
      _ ≤ (L * ‖x₁ - x₂‖) * ‖x₁ - x₂‖ := mul_le_mul_of_nonneg_right (hLip x₁ x₂) (norm_nonneg _)
      _ = _ := by ring
  · intro hInner
    simpa only [gradient_eq hGrad] using
      (hasBregmanBounds_of_abs_inner_le hGrad hInner).norm_sub_le hL

/-- The least Lipschitz bound is approached by absolute inner-product secants. -/
theorem exists_optimal_lipschitz_bound
    (hGrad : ∀ x, HasGradientAt E (g x) x) (hL : 0 ≤ L)
    (hLip : ∀ x₁ x₂, ‖g x₁ - g x₂‖ ≤ L * ‖x₁ - x₂‖) :
    ∃ K : ℝ, 0 ≤ K ∧ K ≤ L ∧
      (∀ x₁ x₂, ‖g x₁ - g x₂‖ ≤ K * ‖x₁ - x₂‖) ∧
      (∀ C : ℝ, 0 ≤ C → (∀ x₁ x₂, ‖g x₁ - g x₂‖ ≤ C * ‖x₁ - x₂‖) → K ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → ε < K →
        ∃ x₁ x₂ : H, x₁ ≠ x₂ ∧ (K - ε) * ‖x₁ - x₂‖ ^ 2 < |⟪g x₁ - g x₂, x₁ - x₂⟫|) := by
  let ratio (x : H × H) := |⟪g x.1 - g x.2, x.1 - x.2⟫| / ‖x.1 - x.2‖ ^ 2
  let S := Set.range ratio
  have hS : S.Nonempty := ⟨ratio (0, 0), Set.mem_range_self _⟩
  have hRatio {C : ℝ} (hC : 0 ≤ C)
      (hInner : ∀ x₁ x₂, |⟪g x₁ - g x₂, x₁ - x₂⟫| ≤ C * ‖x₁ - x₂‖ ^ 2) (x : H × H) :
      ratio x ≤ C := by
    by_cases hx : x.1 = x.2
    · simpa [ratio, hx] using hC
    · exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hx)))).mpr (hInner x.1 x.2)
  have hBdd : BddAbove S := by
    refine ⟨L, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hRatio hL ((norm_sub_le_iff_abs_inner_le hGrad hL).mp hLip) x
  let K := sSup S
  have hK : 0 ≤ K := by
    have h := le_csSup hBdd (Set.mem_range_self (f := ratio) (0, 0))
    simpa [ratio] using h
  have hInner (x₁ x₂ : H) : |⟪g x₁ - g x₂, x₁ - x₂⟫| ≤ K * ‖x₁ - x₂‖ ^ 2 := by
    by_cases hx : x₁ = x₂
    · simp [hx]
    · have h := le_csSup hBdd (Set.mem_range_self (f := ratio) (x₁, x₂))
      exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hx)))).mp h
  have hKL : K ≤ L := csSup_le hS (by
    rintro _ ⟨x, rfl⟩
    exact hRatio hL ((norm_sub_le_iff_abs_inner_le hGrad hL).mp hLip) x)
  refine ⟨K, hK, hKL, (norm_sub_le_iff_abs_inner_le hGrad hK).mpr hInner, ?_, ?_⟩
  · intro C hC hBound
    apply csSup_le hS
    rintro _ ⟨x, rfl⟩
    exact hRatio hC ((norm_sub_le_iff_abs_inner_le hGrad hC).mp hBound) x
  · intro ε hε hεK
    obtain ⟨_, ⟨⟨x₁, x₂⟩, rfl⟩, h⟩ := exists_lt_of_lt_csSup hS (show K - ε < K by linarith)
    have hx : x₁ ≠ x₂ := by
      intro hx
      simp [ratio, hx] at h
      linarith
    refine ⟨x₁, x₂, hx, ?_⟩
    exact (lt_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hx)))).mp h

end GradientMap

end UN
