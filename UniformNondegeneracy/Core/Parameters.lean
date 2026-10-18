module

public import Mathlib

@[expose] public section

/-!
# Curvature parameters of the UN class

Only intrinsic curvature magnitudes and their transformations belong here. Descent-ascent scales, weights, and the associated condition number are defined separately in `DAI.Parameters`. The core theory has no algorithm dependency.
-/

namespace UN
noncomputable section

/-- Four positive magnitudes defining the bands `[-L₋,-μ₋] ∪ [μ₊,L₊]`. -/
structure CurvatureBounds where
  muPlus : ℝ
  muMinus : ℝ
  lPlus : ℝ
  lMinus : ℝ

  muPlus_pos : 0 < muPlus
  muMinus_pos : 0 < muMinus

  muPlus_le_lPlus : muPlus ≤ lPlus
  muMinus_le_lMinus : muMinus ≤ lMinus

namespace CurvatureBounds

def muMin (bounds : CurvatureBounds) : ℝ := min bounds.muPlus bounds.muMinus

def lMax (bounds : CurvatureBounds) : ℝ := max bounds.lPlus bounds.lMinus

def innerCenter (bounds : CurvatureBounds) : ℝ := (bounds.muPlus - bounds.muMinus) / 2

def innerRadius (bounds : CurvatureBounds) : ℝ := (bounds.muPlus + bounds.muMinus) / 2

def outerCenter (bounds : CurvatureBounds) : ℝ := (bounds.lPlus - bounds.lMinus) / 2

def outerRadius (bounds : CurvatureBounds) : ℝ := (bounds.lPlus + bounds.lMinus) / 2

def bands (bounds : CurvatureBounds) : Set ℝ :=
  Set.Icc (-bounds.lMinus) (-bounds.muMinus) ∪ Set.Icc bounds.muPlus bounds.lPlus

/-- Exchange positive and negative curvature magnitudes, as when replacing `E` by `-E`. -/
def swap (bounds : CurvatureBounds) : CurvatureBounds where
  muPlus := bounds.muMinus
  muMinus := bounds.muPlus
  lPlus := bounds.lMinus
  lMinus := bounds.lPlus

  muPlus_pos := bounds.muMinus_pos
  muMinus_pos := bounds.muPlus_pos
  muPlus_le_lPlus := bounds.muMinus_le_lMinus
  muMinus_le_lMinus := bounds.muPlus_le_lPlus

/-- Reciprocal curvature bounds of the inverse-gradient energy. -/
def dual (bounds : CurvatureBounds) : CurvatureBounds where
  muPlus := 1 / bounds.lPlus
  muMinus := 1 / bounds.lMinus
  lPlus := 1 / bounds.muPlus
  lMinus := 1 / bounds.muMinus

  muPlus_pos := by
    exact one_div_pos.mpr (lt_of_lt_of_le bounds.muPlus_pos bounds.muPlus_le_lPlus)
  muMinus_pos := by
    exact one_div_pos.mpr (lt_of_lt_of_le bounds.muMinus_pos bounds.muMinus_le_lMinus)
  muPlus_le_lPlus := by
    exact one_div_le_one_div_of_le bounds.muPlus_pos bounds.muPlus_le_lPlus
  muMinus_le_lMinus := by
    exact one_div_le_one_div_of_le bounds.muMinus_pos bounds.muMinus_le_lMinus

/-- Bounds after subtracting `c / 2 * ‖x₁ - x₂‖²` from the energy. -/
def shift (bounds : CurvatureBounds) (c : ℝ)
    (hLower : -bounds.muMinus < c) (hUpper : c < bounds.muPlus) :
    CurvatureBounds where
  muPlus := bounds.muPlus - c
  muMinus := bounds.muMinus + c
  lPlus := bounds.lPlus - c
  lMinus := bounds.lMinus + c

  muPlus_pos := sub_pos.mpr hUpper
  muMinus_pos := by linarith
  muPlus_le_lPlus := sub_le_sub_right bounds.muPlus_le_lPlus c
  muMinus_le_lMinus := by linarith [bounds.muMinus_le_lMinus]

theorem lPlus_pos (bounds : CurvatureBounds) : 0 < bounds.lPlus := lt_of_lt_of_le bounds.muPlus_pos bounds.muPlus_le_lPlus

theorem lMinus_pos (bounds : CurvatureBounds) : 0 < bounds.lMinus := lt_of_lt_of_le bounds.muMinus_pos bounds.muMinus_le_lMinus

theorem muMin_pos (bounds : CurvatureBounds) : 0 < bounds.muMin := lt_min bounds.muPlus_pos bounds.muMinus_pos

theorem lMax_pos (bounds : CurvatureBounds) : 0 < bounds.lMax := lt_of_lt_of_le bounds.lPlus_pos (le_max_left _ _)

theorem muMin_le_lMax (bounds : CurvatureBounds) : bounds.muMin ≤ bounds.lMax :=
  (min_le_left _ _).trans (bounds.muPlus_le_lPlus.trans (le_max_left _ _))

theorem innerRadius_sub_abs_innerCenter (bounds : CurvatureBounds) :
    bounds.innerRadius - |bounds.innerCenter| = bounds.muMin := by
  unfold innerRadius innerCenter muMin
  rcases le_total bounds.muPlus bounds.muMinus with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]
    ring

theorem outerRadius_add_abs_outerCenter (bounds : CurvatureBounds) :
    bounds.outerRadius + |bounds.outerCenter| = bounds.lMax := by
  unfold outerRadius outerCenter lMax
  rcases le_total bounds.lPlus bounds.lMinus with h | h
  · rw [max_eq_right h, abs_of_nonpos (by linarith)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (by linarith)]
    ring

theorem bands_nonempty (bounds : CurvatureBounds) : bounds.bands.Nonempty :=
  ⟨bounds.muPlus, Or.inr ⟨le_rfl, bounds.muPlus_le_lPlus⟩⟩

theorem bands_isCompact (bounds : CurvatureBounds) : IsCompact bounds.bands := isCompact_Icc.union isCompact_Icc

@[simp] theorem swap_swap (bounds : CurvatureBounds) : bounds.swap.swap = bounds := by cases bounds; rfl
@[simp] theorem dual_dual (bounds : CurvatureBounds) : bounds.dual.dual = bounds := by
  cases bounds
  simp [dual]

end CurvatureBounds

end
end UN
