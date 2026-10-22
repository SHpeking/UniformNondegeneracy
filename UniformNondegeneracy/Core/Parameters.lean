module

public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Curvature bounds and their transformations
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

/-- Symmetric bands `[-L,-μ] ∪ [μ,L]`. -/
def symmetric (μ L : ℝ) (hμ : 0 < μ) (hμL : μ ≤ L) : CurvatureBounds where
  muPlus := μ
  muMinus := μ
  lPlus := L
  lMinus := L
  muPlus_pos := hμ
  muMinus_pos := hμ
  muPlus_le_lPlus := hμL
  muMinus_le_lMinus := hμL

def muMin (bounds : CurvatureBounds) : ℝ := min bounds.muPlus bounds.muMinus

def lMax (bounds : CurvatureBounds) : ℝ := max bounds.lPlus bounds.lMinus

/-- Maximum width of the two curvature bands. -/
def maxBandWidth (bounds : CurvatureBounds) : ℝ :=
  max (bounds.lPlus - bounds.muPlus) (bounds.lMinus - bounds.muMinus)

def innerCenter (bounds : CurvatureBounds) : ℝ := (bounds.muPlus - bounds.muMinus) / 2

def innerRadius (bounds : CurvatureBounds) : ℝ := (bounds.muPlus + bounds.muMinus) / 2

def outerCenter (bounds : CurvatureBounds) : ℝ := (bounds.lPlus - bounds.lMinus) / 2

def outerRadius (bounds : CurvatureBounds) : ℝ := (bounds.lPlus + bounds.lMinus) / 2

/-- Signed radius of the largest interval centered at `c` inside the inner gap. -/
def innerRadiusAt (bounds : CurvatureBounds) (c : ℝ) : ℝ :=
  min (bounds.muPlus - c) (bounds.muMinus + c)

/-- Radius of the smallest interval centered at `c` containing both curvature bands. -/
def outerRadiusAt (bounds : CurvatureBounds) (c : ℝ) : ℝ :=
  max (bounds.lPlus - c) (bounds.lMinus + c)

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

/-- Reciprocal curvature bounds for the Legendre transform. -/
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

/-- Bounds after subtracting a scalar quadratic of curvature `c`. -/
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

theorem lPlus_pos (bounds : CurvatureBounds) : 0 < bounds.lPlus :=
  lt_of_lt_of_le bounds.muPlus_pos bounds.muPlus_le_lPlus

theorem lMinus_pos (bounds : CurvatureBounds) : 0 < bounds.lMinus :=
  lt_of_lt_of_le bounds.muMinus_pos bounds.muMinus_le_lMinus

theorem muMin_pos (bounds : CurvatureBounds) : 0 < bounds.muMin :=
  lt_min bounds.muPlus_pos bounds.muMinus_pos

theorem lMax_pos (bounds : CurvatureBounds) : 0 < bounds.lMax :=
  lt_of_lt_of_le bounds.lPlus_pos (le_max_left _ _)

theorem maxBandWidth_nonneg (bounds : CurvatureBounds) : 0 ≤ bounds.maxBandWidth :=
  (sub_nonneg.mpr bounds.muPlus_le_lPlus).trans (le_max_left _ _)

theorem muMin_le_lMax (bounds : CurvatureBounds) : bounds.muMin ≤ bounds.lMax :=
  (min_le_left _ _).trans (bounds.muPlus_le_lPlus.trans (le_max_left _ _))

theorem innerRadius_pos (bounds : CurvatureBounds) : 0 < bounds.innerRadius :=
  div_pos (add_pos bounds.muPlus_pos bounds.muMinus_pos) (by norm_num)

theorem outerRadius_pos (bounds : CurvatureBounds) : 0 < bounds.outerRadius :=
  div_pos (add_pos bounds.lPlus_pos bounds.lMinus_pos) (by norm_num)

theorem innerRadiusAt_eq (bounds : CurvatureBounds) (c : ℝ) :
    bounds.innerRadiusAt c = bounds.innerRadius - |bounds.innerCenter - c| := by
  unfold innerRadiusAt innerRadius innerCenter
  rcases le_total (bounds.muPlus - c) (bounds.muMinus + c) with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

theorem outerRadiusAt_eq (bounds : CurvatureBounds) (c : ℝ) :
    bounds.outerRadiusAt c = bounds.outerRadius + |bounds.outerCenter - c| := by
  unfold outerRadiusAt outerRadius outerCenter
  rcases le_total (bounds.lPlus - c) (bounds.lMinus + c) with h | h
  · rw [max_eq_right h, abs_of_nonpos (by linarith)]; ring
  · rw [max_eq_left h, abs_of_nonneg (by linarith)]; ring

theorem innerRadiusAt_pos (bounds : CurvatureBounds) {c : ℝ}
    (hLower : -bounds.muMinus < c) (hUpper : c < bounds.muPlus) :
    0 < bounds.innerRadiusAt c :=
  lt_min (sub_pos.mpr hUpper) (by linarith)

theorem innerRadiusAt_le_outerRadiusAt (bounds : CurvatureBounds) (c : ℝ) :
    bounds.innerRadiusAt c ≤ bounds.outerRadiusAt c :=
  (min_le_left _ _).trans ((sub_le_sub_right bounds.muPlus_le_lPlus c).trans (le_max_left _ _))

/-- Symmetric curvature bounds after subtracting a quadratic of curvature `c`. -/
def centered (bounds : CurvatureBounds) (c : ℝ)
    (hLower : -bounds.muMinus < c) (hUpper : c < bounds.muPlus) : CurvatureBounds :=
  symmetric (bounds.innerRadiusAt c) (bounds.outerRadiusAt c)
    (bounds.innerRadiusAt_pos hLower hUpper) (bounds.innerRadiusAt_le_outerRadiusAt c)

/-- The bands are the intersection of an outer interval and the complement of an inner gap. -/
theorem mem_bands_iff_centered (bounds : CurvatureBounds) (σ : ℝ) :
    σ ∈ bounds.bands ↔
      |σ - bounds.outerCenter| ≤ bounds.outerRadius ∧ bounds.innerRadius ≤ |σ - bounds.innerCenter| := by
  simp only [bands, Set.mem_union, Set.mem_Icc, outerCenter, outerRadius, innerCenter, innerRadius, abs_le, le_abs]
  constructor
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact ⟨⟨by linarith, by linarith [bounds.muMinus_pos, bounds.lPlus_pos]⟩, Or.inr (by linarith)⟩
    · exact ⟨⟨by linarith [bounds.muPlus_pos, bounds.lMinus_pos], by linarith⟩, Or.inl (by linarith)⟩
  · rintro ⟨⟨h₁, h₂⟩, h₃ | h₃⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
    · exact Or.inl ⟨by linarith, by linarith⟩

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

theorem bands_isCompact (bounds : CurvatureBounds) : IsCompact bounds.bands :=
  isCompact_Icc.union isCompact_Icc

theorem innerRadiusAt_eq_infDist (bounds : CurvatureBounds) {c : ℝ}
    (hLower : -bounds.muMinus < c) (hUpper : c < bounds.muPlus) :
    bounds.innerRadiusAt c = Metric.infDist c bounds.bands := by
  apply le_antisymm
  · apply (Metric.le_infDist bounds.bands_nonempty).mpr
    intro x hx
    rw [Real.dist_eq]
    rcases hx with hx | hx
    · rw [abs_of_nonneg (by linarith [hx.2])]
      exact (min_le_right _ _).trans (by linarith [hx.2])
    · rw [abs_of_nonpos (by linarith [hx.1])]
      exact (min_le_left _ _).trans (by linarith [hx.1])
  · apply le_min
    · have h := Metric.infDist_le_dist_of_mem
        (s := bounds.bands) (x := c) (y := bounds.muPlus) (Or.inr ⟨le_rfl, bounds.muPlus_le_lPlus⟩)
      simpa [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hUpper.le)] using h
    · have h := Metric.infDist_le_dist_of_mem
        (s := bounds.bands) (x := c) (y := -bounds.muMinus) (Or.inl ⟨by linarith [bounds.muMinus_le_lMinus], le_rfl⟩)
      rw [Real.dist_eq, abs_of_nonneg (by linarith)] at h
      simpa [add_comm] using h

@[simp] theorem swap_swap (bounds : CurvatureBounds) : bounds.swap.swap = bounds := by cases bounds; rfl
@[simp] theorem dual_dual (bounds : CurvatureBounds) : bounds.dual.dual = bounds := by
  cases bounds
  simp [dual]

end CurvatureBounds

end
end UN
