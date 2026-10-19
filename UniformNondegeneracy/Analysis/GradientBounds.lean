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

/-- Symmetric global quadratic models imply the matching gradient norm bound. -/
theorem HasBregmanBounds.norm_sub_le {E : H → ℝ} {g : H → H} {L : ℝ}
    (hBounds : HasBregmanBounds E g L L) (hL : 0 ≤ L) (x₁ x₂ : H) :
    ‖g x₁ - g x₂‖ ≤ L * ‖x₁ - x₂‖ := by
  rcases hL.eq_or_lt with hZero | hPos
  · subst L
    have hB (x₁ x₂ : H) : bregman E g x₁ x₂ = 0 := by
      have h₁ := hBounds.lower x₁ x₂
      have h₂ := hBounds.upper x₁ x₂
      simp only [zero_div, neg_zero, zero_mul] at h₁ h₂
      exact le_antisymm h₂ h₁
    have h := bregman_three_point E g (x₁ + (g x₁ - g x₂)) x₁ x₂
    simp only [hB, add_sub_cancel_left, real_inner_self_eq_norm_sq] at h
    simp only [zero_mul]
    nlinarith [norm_nonneg (g x₁ - g x₂)]
  · have h₁ := hBounds.interpolation_upper (by linarith) x₁ x₂
    have h₂ := hBounds.interpolation_upper (by linarith) x₂ x₁
    rw [norm_sub_rev x₂ x₁, norm_sub_rev (g x₂) (g x₁)] at h₂
    have hi : ⟪x₂ - x₁, g x₂ - g x₁⟫ = ⟪x₁ - x₂, g x₁ - g x₂⟫ := by
      rw [← neg_sub x₁ x₂, ← neg_sub (g x₁) (g x₂), inner_neg_neg]
    rw [hi] at h₂
    have hDen : 0 < 2 * (L + L) := by linarith
    have hm₁ := (le_div_iff₀ hDen).mp h₁
    have hm₂ := (le_div_iff₀ hDen).mp h₂
    have hSum := bregman_add_reverse E g x₁ x₂
    rw [real_inner_comm (x₁ - x₂) (g x₁ - g x₂)] at hSum
    have hSq : ‖g x₁ - g x₂‖ ^ 2 ≤ L ^ 2 * ‖x₁ - x₂‖ ^ 2 := by nlinarith
    nlinarith [norm_nonneg (g x₁ - g x₂), mul_nonneg hPos.le (norm_nonneg (x₁ - x₂))]

namespace GradientMap

variable [CompleteSpace H]
variable {E : H → ℝ} {g : H → H} {L : ℝ}

/-- Absolute inner-product secants give both quadratic remainder bounds. -/
theorem hasBregmanBounds_of_abs_inner_le
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (hInner : ∀ x₁ x₂, |⟪g x₁ - g x₂, x₁ - x₂⟫| ≤ L * ‖x₁ - x₂‖ ^ 2) :
    HasBregmanBounds E g L L := by
  constructor
  · intro x₁ x₂
    have h := taylor_lower_bound_of_inner E g (-L) hGrad
      (fun x₁ x₂ => by have := (abs_le.mp (hInner x₁ x₂)).1; linarith) x₂ (x₁ - x₂)
    rw [show x₂ + (x₁ - x₂) = x₁ by abel] at h
    dsimp [bregman]
    linarith
  · intro x₁ x₂
    have h := taylor_upper_bound_of_inner E g L hGrad
      (fun x₁ x₂ => (abs_le.mp (hInner x₁ x₂)).2) x₂ (x₁ - x₂)
    simpa [bregman] using h

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
    exact (hasBregmanBounds_of_abs_inner_le hGrad hInner).norm_sub_le hL

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
