module

public import Mathlib

@[expose] public section

/-!
# Descent–ascent scales and weights

Primitive scale and weight data, independent of UN curvature bounds. Admissibility and compatible weight families are developed in separate modules.
-/

namespace UN.DAI
noncomputable section

/-- Positive inverse step sizes: descent uses `1 / plus`, ascent uses `1 / minus`. -/
structure Scales where
  plus : ℝ
  minus : ℝ

  plus_pos : 0 < plus
  minus_pos : 0 < minus

/-- Nonnegative DAI coefficients. Zero coefficients are intentionally permitted. -/
structure Weights where
  plus : ℝ
  minus : ℝ

  plus_nonneg : 0 ≤ plus
  minus_nonneg : 0 ≤ minus

namespace Scales

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
@[simp] theorem inflate_difference (Λ : Scales) (ε : ℝ) (hε : 0 ≤ ε) :
    (Λ.inflate ε hε).difference = Λ.difference := by unfold inflate difference; dsimp; ring

@[simp] theorem inflate_center (Λ : Scales) (ε : ℝ) (hε : 0 ≤ ε) :
    (Λ.inflate ε hε).center = Λ.center := by simp [center]

end Scales

end
end UN.DAI
