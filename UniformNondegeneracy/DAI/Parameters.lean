module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Descent–ascent scales and weights
-/

namespace UN.DAI
noncomputable section

/-- Positive inverse step sizes: descent uses `1 / plus`, ascent uses `1 / minus`. -/
structure Scales where
  plus : ℝ
  minus : ℝ

  plus_pos : 0 < plus
  minus_pos : 0 < minus

/-- Nonnegative DAI weights. -/
structure Weights where
  plus : ℝ
  minus : ℝ

  plus_nonneg : 0 ≤ plus
  minus_nonneg : 0 ≤ minus

namespace Scales

def unit : Scales := ⟨1, 1, zero_lt_one, zero_lt_one⟩

def tauPlus (Λ : Scales) : ℝ := 1 / Λ.plus

def tauMinus (Λ : Scales) : ℝ := 1 / Λ.minus

def difference (Λ : Scales) : ℝ := Λ.plus - Λ.minus

def center (Λ : Scales) : ℝ := Λ.difference / 2

def radius (Λ : Scales) : ℝ := (Λ.plus + Λ.minus) / 2

def multiplier (Λ : Scales) (σ : ℝ) : ℝ :=
  (1 - σ / Λ.plus) * (1 + σ / Λ.minus)

def swap (Λ : Scales) : Scales where
  plus := Λ.minus
  minus := Λ.plus
  plus_pos := Λ.minus_pos
  minus_pos := Λ.plus_pos

/-- Scales after subtracting a quadratic of curvature `c`. -/
def shift (Λ : Scales) (c : ℝ) (hLower : -Λ.minus < c) (hUpper : c < Λ.plus) : Scales where
  plus := Λ.plus - c
  minus := Λ.minus + c
  plus_pos := sub_pos.mpr hUpper
  minus_pos := by linarith

/-- Scales after multiplying the energy by a positive scalar. -/
def scale (Λ : Scales) (a : ℝ) (ha : 0 < a) : Scales where
  plus := a * Λ.plus
  minus := a * Λ.minus
  plus_pos := mul_pos ha Λ.plus_pos
  minus_pos := mul_pos ha Λ.minus_pos

/-- Increase both scales equally; their difference and center remain unchanged. -/
def inflate (Λ : Scales) (ε : ℝ) (hε : 0 ≤ ε) : Scales where
  plus := Λ.plus + ε
  minus := Λ.minus + ε
  plus_pos := by linarith [Λ.plus_pos]
  minus_pos := by linarith [Λ.minus_pos]

theorem tauPlus_pos (Λ : Scales) : 0 < Λ.tauPlus := one_div_pos.mpr Λ.plus_pos

theorem tauMinus_pos (Λ : Scales) : 0 < Λ.tauMinus := one_div_pos.mpr Λ.minus_pos

theorem radius_pos (Λ : Scales) : 0 < Λ.radius := by dsimp [radius]; linarith [Λ.plus_pos, Λ.minus_pos]

theorem radius_sq_sub_center_sq (Λ : Scales) :
    Λ.radius ^ 2 - Λ.center ^ 2 = Λ.plus * Λ.minus := by unfold radius center difference; ring

@[simp] theorem swap_swap (Λ : Scales) : Λ.swap.swap = Λ := by cases Λ; rfl

@[simp] theorem shift_center (Λ : Scales) (c : ℝ) (hLower : -Λ.minus < c) (hUpper : c < Λ.plus) :
    (Λ.shift c hLower hUpper).center = Λ.center - c := by
  dsimp [center, difference, shift]
  ring

@[simp] theorem shift_radius (Λ : Scales) (c : ℝ) (hLower : -Λ.minus < c) (hUpper : c < Λ.plus) :
    (Λ.shift c hLower hUpper).radius = Λ.radius := by
  dsimp [radius, shift]
  ring

@[simp] theorem inflate_difference (Λ : Scales) (ε : ℝ) (hε : 0 ≤ ε) :
    (Λ.inflate ε hε).difference = Λ.difference := by unfold inflate difference; dsimp; ring

@[simp] theorem inflate_center (Λ : Scales) (ε : ℝ) (hε : 0 ≤ ε) :
    (Λ.inflate ε hε).center = Λ.center := by simp [center]

end Scales

namespace Weights

/-- Equal nonnegative weights. -/
def symmetric (r : ℝ) (hr : 0 ≤ r) : Weights := ⟨r, r, hr, hr⟩

/-- Weights after subtracting a quadratic of curvature `c` at scales `Λ`. -/
def quadraticShift (ρ : Weights) (Λ : Scales) (c : ℝ)
    (hLower : -Λ.minus < c) (hUpper : c < Λ.plus) : Weights where
  plus := ρ.plus * Λ.minus / (Λ.minus + c)
  minus := ρ.minus * Λ.plus / (Λ.plus - c)
  plus_nonneg := div_nonneg (mul_nonneg ρ.plus_nonneg Λ.minus_pos.le) (by linarith)
  minus_nonneg := div_nonneg (mul_nonneg ρ.minus_nonneg Λ.plus_pos.le) (sub_pos.mpr hUpper).le

/-- Balance equates the two weight-to-scale ratios. -/
def Balanced (ρ : Weights) (Λ : Scales) : Prop :=
  ρ.plus * Λ.minus = ρ.minus * Λ.plus

theorem balanced_iff_ratio (ρ : Weights) (Λ : Scales) :
    ρ.Balanced Λ ↔ ρ.plus / Λ.plus = ρ.minus / Λ.minus := by
  exact (div_eq_div_iff Λ.plus_pos.ne' Λ.minus_pos.ne').symm

theorem quadraticShift_plus_mul_minus (ρ : Weights) (Λ : Scales) (c : ℝ)
    (hLower : -Λ.minus < c) (hUpper : c < Λ.plus) :
    (ρ.quadraticShift Λ c hLower hUpper).plus * (Λ.shift c hLower hUpper).minus = ρ.plus * Λ.minus := by
  exact div_mul_cancel₀ _ (by linarith : Λ.minus + c ≠ 0)

theorem quadraticShift_minus_mul_plus (ρ : Weights) (Λ : Scales) (c : ℝ)
    (hLower : -Λ.minus < c) (hUpper : c < Λ.plus) :
    (ρ.quadraticShift Λ c hLower hUpper).minus * (Λ.shift c hLower hUpper).plus = ρ.minus * Λ.plus := by
  exact div_mul_cancel₀ _ (sub_pos.mpr hUpper).ne'

/-- Quadratic shifting preserves balance. -/
theorem balanced_quadraticShift_iff (ρ : Weights) (Λ : Scales) (c : ℝ)
    (hLower : -Λ.minus < c) (hUpper : c < Λ.plus) :
    (ρ.quadraticShift Λ c hLower hUpper).Balanced (Λ.shift c hLower hUpper) ↔ ρ.Balanced Λ := by
  unfold Balanced
  rw [quadraticShift_plus_mul_minus, quadraticShift_minus_mul_plus]

end Weights

/-- Balanced weights with common cross product `a`: `ρ₊ Λ₋ = ρ₋ Λ₊ = a`. -/
def balancedWeights (Λ : Scales) (a : ℝ) (ha : 0 ≤ a) : Weights where
  plus := a / Λ.minus
  minus := a / Λ.plus
  plus_nonneg := div_nonneg ha Λ.minus_pos.le
  minus_nonneg := div_nonneg ha Λ.plus_pos.le

theorem balancedWeights_balanced (Λ : Scales) (a : ℝ) (ha : 0 ≤ a) :
    (balancedWeights Λ a ha).Balanced Λ := by
  dsimp [Weights.Balanced, balancedWeights]
  field_simp [Λ.plus_pos.ne', Λ.minus_pos.ne']

theorem balancedWeights_product (Λ : Scales) (a : ℝ) (ha : 0 ≤ a) :
    (balancedWeights Λ a ha).plus * (balancedWeights Λ a ha).minus * (Λ.plus * Λ.minus) = a ^ 2 := by
  dsimp [balancedWeights]
  field_simp [Λ.plus_pos.ne', Λ.minus_pos.ne']

end
end UN.DAI
