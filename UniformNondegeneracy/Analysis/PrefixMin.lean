module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Prefix minima of real sequences
-/

namespace UN

/-- The minimum of `r 0, …, r T`. -/
def prefixMin (r : ℕ → ℝ) : ℕ → ℝ
  | 0 => r 0
  | T + 1 => min (prefixMin r T) (r (T + 1))

@[simp] theorem prefixMin_zero (r : ℕ → ℝ) :
    prefixMin r 0 = r 0 := rfl

@[simp] theorem prefixMin_succ (r : ℕ → ℝ) (T : ℕ) :
    prefixMin r (T + 1) = min (prefixMin r T) (r (T + 1)) := rfl

theorem prefixMin_attained (r : ℕ → ℝ) (T : ℕ) :
    ∃ t ≤ T, prefixMin r T = r t := by
  induction T with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ T ih =>
    rcases ih with ⟨t, hi, he⟩
    by_cases h : prefixMin r T ≤ r (T + 1)
    · exact ⟨t, Nat.le_succ_of_le hi, by rw [prefixMin_succ, min_eq_left h, he]⟩
    · exact ⟨T + 1, le_rfl, by simp [min_eq_right (le_of_not_ge h)]⟩

theorem prefixMin_le_at (r : ℕ → ℝ) {t T : ℕ} (hIndex : t ≤ T) :
    prefixMin r T ≤ r t := by
  induction T with
  | zero => simpa using (Nat.eq_zero_of_le_zero hIndex ▸ le_refl (r 0))
  | succ T ih =>
    rcases Nat.eq_or_lt_of_le hIndex with rfl | h
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (ih (Nat.le_of_lt_succ h))

theorem le_prefixMin (r : ℕ → ℝ) (T : ℕ) {a : ℝ} (hLower : ∀ t ≤ T, a ≤ r t) :
    a ≤ prefixMin r T := by
  induction T with
  | zero => exact hLower 0 (by omega)
  | succ T ih =>
    exact le_min (ih (fun t hi => hLower t (Nat.le_succ_of_le hi))) (hLower _ le_rfl)

theorem prefixMin_nonneg (r : ℕ → ℝ) (hResidual : ∀ t, 0 ≤ r t) (T : ℕ) :
    0 ≤ prefixMin r T := by
  exact le_prefixMin r T (fun t _ => hResidual t)

theorem prefixMin_antitone (r : ℕ → ℝ) :
    Antitone (prefixMin r) := by
  apply antitone_nat_of_succ_le
  intro T
  exact min_le_left _ _

theorem prefixMin_mono_seq {r₁ r₂ : ℕ → ℝ} (hCompare : ∀ t, r₁ t ≤ r₂ t) (T : ℕ) :
    prefixMin r₁ T ≤ prefixMin r₂ T := by
  induction T with
  | zero => exact hCompare 0
  | succ T ih => exact min_le_min ih (hCompare _)

end UN
