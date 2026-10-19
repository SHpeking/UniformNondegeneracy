module

public import UniformNondegeneracy.Analysis.PrefixMin
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

open scoped BigOperators

/-!
# Scalar residual decay from a Lyapunov certificate

A Lyapunov decrease bound and comparison with squared residuals give exponential decay of the minimum residual.
-/

noncomputable section

namespace UN

/-- A potential comparable to squared residuals, with decrease at least the current squared residual. -/
structure HasLyapunovBounds (C : ℝ) (r P : ℕ → ℝ) : Prop where
  one_le_comparison : 1 ≤ C
  residual_nonneg : ∀ t, 0 ≤ r t
  residual_sq_le_potential : ∀ t, (r t) ^ 2 ≤ P t
  potential_le_residual_sq : ∀ t, P t ≤ C * (r t) ^ 2
  sufficient_decrease : ∀ t, (r t) ^ 2 ≤ P t - P (t + 1)

namespace HasLyapunovBounds

variable {C : ℝ} {r P : ℕ → ℝ}

theorem potential_nonneg (hLyapunov : HasLyapunovBounds C r P) (t : ℕ) :
    0 ≤ P t := by
  exact (sq_nonneg _).trans (hLyapunov.residual_sq_le_potential t)

theorem potential_antitone (hLyapunov : HasLyapunovBounds C r P) :
    Antitone P := by
  apply antitone_nat_of_succ_le
  intro t
  linarith [hLyapunov.sufficient_decrease t, sq_nonneg (r t)]

theorem tail (hLyapunov : HasLyapunovBounds C r P) (t₀ : ℕ) :
    HasLyapunovBounds C (fun t => r (t₀ + t)) (fun t => P (t₀ + t)) := by
  refine ⟨hLyapunov.one_le_comparison, ?_, ?_, ?_, ?_⟩
  · exact fun t => hLyapunov.residual_nonneg (t₀ + t)
  · exact fun t => hLyapunov.residual_sq_le_potential (t₀ + t)
  · exact fun t => hLyapunov.potential_le_residual_sq (t₀ + t)
  · exact fun t => hLyapunov.sufficient_decrease (t₀ + t)

/-- The initial decrease improves the telescoping bound from `C` to `C - 1`. -/
theorem sum_residual_sq_le (hLyapunov : HasLyapunovBounds C r P) (t₀ T : ℕ) :
    (∑ t ∈ Finset.range T, (r (t₀ + t + 1)) ^ 2) ≤ (C - 1) * (r t₀) ^ 2 := by
  have htelescope : ∀ T₁ : ℕ,
      (∑ t ∈ Finset.range T₁, (r (t₀ + t + 1)) ^ 2) ≤ P (t₀ + 1) - P (t₀ + T₁ + 1) := by
    intro T₁
    induction T₁ with
    | zero => simp
    | succ T₁ ih =>
      rw [Finset.sum_range_succ]
      have hd := hLyapunov.sufficient_decrease (t₀ + T₁ + 1)
      have he : t₀ + (T₁ + 1) + 1 = t₀ + T₁ + 1 + 1 := by omega
      rw [he]
      linarith
  have h := htelescope T
  have hp := hLyapunov.potential_nonneg (t₀ + T + 1)
  have hd := hLyapunov.sufficient_decrease t₀
  have hu := hLyapunov.potential_le_residual_sq t₀
  nlinarith

theorem exists_residual_sq_le (hLyapunov : HasLyapunovBounds C r P)
    (t₀ T : ℕ) (hT_pos : 0 < T) :
    ∃ t,
      t₀ < t ∧ t ≤ t₀ + T ∧
      (r t) ^ 2 ≤ ((C - 1) / (T : ℝ)) * (r t₀) ^ 2 := by
  have hNum : (0 : ℝ) < T := by exact_mod_cast hT_pos
  by_contra! h
  have hsum : (∑ t ∈ Finset.range T, ((C - 1) / (T : ℝ)) * (r t₀) ^ 2) <
      ∑ t ∈ Finset.range T, (r (t₀ + t + 1)) ^ 2 := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hT_pos)
    · intro t hj
      exact h (t₀ + t + 1) (by omega) (by have := Finset.mem_range.mp hj; omega)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have he : (T : ℝ) * ((C - 1) / (T : ℝ) * (r t₀) ^ 2) = (C - 1) * (r t₀) ^ 2 := by field_simp
  rw [he] at hsum
  have hs := hLyapunov.sum_residual_sq_le t₀ T
  nlinarith

/-- A sufficiently long window contains a factor-two residual reduction. -/
theorem exists_residual_le_half (hLyapunov : HasLyapunovBounds C r P)
    (W : ℕ) (hW_pos : 0 < W) (hWindow : 4 * (C - 1) ≤ (W : ℝ)) (t₀ : ℕ) :
    ∃ t, t₀ < t ∧ t ≤ t₀ + W ∧ r t ≤ r t₀ / 2 := by
  obtain ⟨t, hi, hi', hr⟩ := hLyapunov.exists_residual_sq_le t₀ W hW_pos
  refine ⟨t, hi, hi', ?_⟩
  have hwpos : (0 : ℝ) < W := by exact_mod_cast hW_pos
  have hratio : (C - 1) / (W : ℝ) ≤ 1 / 4 := by
    apply (div_le_iff₀ hwpos).mpr
    linarith
  have hsq := hr.trans (mul_le_mul_of_nonneg_right hratio (sq_nonneg (r t₀)))
  nlinarith [hLyapunov.residual_nonneg t₀, hLyapunov.residual_nonneg t]

/-- Successive windows yield geometric residual reduction. -/
theorem exists_residual_le_geometric (hLyapunov : HasLyapunovBounds C r P)
    (W : ℕ) (hW_pos : 0 < W) (hWindow : 4 * (C - 1) ≤ (W : ℝ)) (B : ℕ) :
    ∃ t ≤ B * W, r t ≤ (1 / 2 : ℝ) ^ B * r 0 := by
  induction B with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ B ih =>
    obtain ⟨t, hi, hr⟩ := ih
    obtain ⟨t₁, hn, hn', hr'⟩ := hLyapunov.exists_residual_le_half W hW_pos hWindow t
    refine ⟨t₁, ?_, ?_⟩
    · calc
        t₁ ≤ t + W := hn'
        _ ≤ B * W + W := Nat.add_le_add_right hi _
        _ = (B + 1) * W := by ring
    · rw [pow_succ]
      linarith

theorem prefixMin_le_geometric (hLyapunov : HasLyapunovBounds C r P)
    (W : ℕ) (hW_pos : 0 < W) (hWindow : 4 * (C - 1) ≤ (W : ℝ)) (T : ℕ) :
    prefixMin r T ≤ (1 / 2 : ℝ) ^ (T / W) * r 0 := by
  obtain ⟨t, hi, hr⟩ := hLyapunov.exists_residual_le_geometric W hW_pos hWindow (T / W)
  exact (prefixMin_le_at r (hi.trans (Nat.div_mul_le_self _ _))).trans hr

/-- Exponential decay with any real upper bound `R` on a valid window. The factor two accounts for rounding the number of complete windows. -/
theorem prefixMin_le_exp (hLyapunov : HasLyapunovBounds C r P)
    (W : ℕ) (hW_pos : 0 < W) (hWindow : 4 * (C - 1) ≤ (W : ℝ))
    (R : ℝ) (hWindowUpper : (W : ℝ) ≤ R) (T : ℕ) :
    prefixMin r T ≤ 2 * Real.exp (-Real.log 2 * (T : ℝ) / R) * r 0 := by
  have hR_pos : 0 < R := lt_of_lt_of_le (by exact_mod_cast hW_pos) hWindowUpper
  have hround : (T : ℝ) < (W : ℝ) * ((T / W : ℕ) + 1 : ℝ) := by
    exact_mod_cast Nat.lt_mul_div_succ T hW_pos
  have hquot : (T : ℝ) / R ≤ (T / W : ℕ) + 1 := by
    apply (div_le_iff₀ hR_pos).mpr
    have hc := mul_le_mul_of_nonneg_right hWindowUpper
      (show (0 : ℝ) ≤ (T / W : ℕ) + 1 by positivity)
    nlinarith
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hexp : (1 / 2 : ℝ) ^ (T / W) ≤ 2 * Real.exp (-Real.log 2 * (T : ℝ) / R) := by
    calc
      (1 / 2 : ℝ) ^ (T / W) = Real.exp ((T / W : ℕ) * (-Real.log 2)) := by
        rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num)]
        norm_num
      _ ≤ Real.exp (Real.log 2 + (-Real.log 2 * (T : ℝ) / R)) := by
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_left hquot hlog
        rw [← mul_div_assoc] at hm
        simp only [neg_mul, neg_div]
        nlinarith
      _ = _ := by rw [Real.exp_add, Real.exp_log (by norm_num)]
  exact (hLyapunov.prefixMin_le_geometric W hW_pos hWindow T).trans
    (mul_le_mul_of_nonneg_right hexp (hLyapunov.residual_nonneg 0))

theorem exists_residual_le_exp (hLyapunov : HasLyapunovBounds C r P)
    (W : ℕ) (hW_pos : 0 < W) (hWindow : 4 * (C - 1) ≤ (W : ℝ))
    (R : ℝ) (hWindowUpper : (W : ℝ) ≤ R) (T : ℕ) :
    ∃ t ≤ T, r t ≤ 2 * Real.exp (-Real.log 2 * (T : ℝ) / R) * r 0 := by
  obtain ⟨t, hi, he⟩ := prefixMin_attained r T
  exact ⟨t, hi, he ▸ hLyapunov.prefixMin_le_exp W hW_pos hWindow R hWindowUpper T⟩

end HasLyapunovBounds

end UN
