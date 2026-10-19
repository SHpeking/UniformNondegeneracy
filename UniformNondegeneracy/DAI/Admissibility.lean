module

public import UniformNondegeneracy.Core.Parameters
public import UniformNondegeneracy.DAI.Parameters

@[expose] public section

/-!
# Admissible scales, multipliers, and effective curvature bounds

The maximal multiplier `q` satisfies $0 \le q < 1$ at admissible scales, giving the condition number $\kappa = \frac{1}{1-q}$. Effective curvature bounds center the inner gap at `Λ.center` and set the outer bounds to the selected scales.
-/

namespace UN.DAI
noncomputable section

/-- The selected scales dominate the outer curvature bounds. -/
structure OuterCompatible (bounds : CurvatureBounds) (Λ : Scales) : Prop where
  lPlus_le_plus : bounds.lPlus ≤ Λ.plus
  lMinus_le_minus : bounds.lMinus ≤ Λ.minus

/-- Outer-compatible scales whose difference lies in the inner gap. -/
structure Admissible (bounds : CurvatureBounds) (Λ : Scales) : Prop
    extends OuterCompatible bounds Λ where
  neg_muMinus_lt_difference : -bounds.muMinus < Λ.difference
  difference_lt_muPlus : Λ.difference < bounds.muPlus

/-- Admissible scales strictly exceeding the outer curvature bounds. -/
structure StrictAdmissible (bounds : CurvatureBounds) (Λ : Scales) : Prop
    extends Admissible bounds Λ where
  lPlus_lt_plus : bounds.lPlus < Λ.plus
  lMinus_lt_minus : bounds.lMinus < Λ.minus

/-- Supremum of the two-step multiplier over the curvature bands. -/
def q (bounds : CurvatureBounds) (Λ : Scales) : ℝ :=
  sSup (Λ.multiplier '' bounds.bands)

/-- The DAI condition number. -/
def kappa (bounds : CurvatureBounds) (Λ : Scales) : ℝ := 1 / (1 - q bounds Λ)

/-- Denominator in the explicit formula for `kappa`. -/
def kappaDenominator (bounds : CurvatureBounds) (Λ : Scales) : ℝ :=
  min (bounds.muPlus * (bounds.muPlus - Λ.difference))
    (bounds.muMinus * (bounds.muMinus + Λ.difference))

/-- Signed distance from `Λ.center` to the boundary of the inner gap. -/
def gapMargin (bounds : CurvatureBounds) (Λ : Scales) : ℝ :=
  min (bounds.muPlus - Λ.center) (bounds.muMinus + Λ.center)

def effectiveMuPlus (bounds : CurvatureBounds) (Λ : Scales) : ℝ :=
  gapMargin bounds Λ + Λ.center

def effectiveMuMinus (bounds : CurvatureBounds) (Λ : Scales) : ℝ :=
  gapMargin bounds Λ - Λ.center

/-- Symmetric outer radius after subtracting the quadratic with coefficient `Λ.center`. -/
def centeredOuterRadius (bounds : CurvatureBounds) (Λ : Scales) : ℝ :=
  max (bounds.lPlus - Λ.center) (bounds.lMinus + Λ.center)

theorem one_sub_q_eq_inv_kappa (bounds : CurvatureBounds) (Λ : Scales) :
    1 - q bounds Λ = 1 / kappa bounds Λ := by simp [kappa]

theorem gapMargin_eq_innerRadius_sub_abs (bounds : CurvatureBounds) (Λ : Scales) :
    gapMargin bounds Λ = bounds.innerRadius - |bounds.innerCenter - Λ.center| := by
  unfold gapMargin CurvatureBounds.innerRadius CurvatureBounds.innerCenter
  rcases le_total (bounds.muPlus - Λ.center) (bounds.muMinus + Λ.center) with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

theorem effectiveMuPlus_le_muPlus (bounds : CurvatureBounds) (Λ : Scales) :
    effectiveMuPlus bounds Λ ≤ bounds.muPlus := by
  dsimp [effectiveMuPlus, gapMargin]
  linarith [min_le_left (bounds.muPlus - Λ.center) (bounds.muMinus + Λ.center)]

theorem effectiveMuMinus_le_muMinus (bounds : CurvatureBounds) (Λ : Scales) :
    effectiveMuMinus bounds Λ ≤ bounds.muMinus := by
  dsimp [effectiveMuMinus, gapMargin]
  linarith [min_le_right (bounds.muPlus - Λ.center) (bounds.muMinus + Λ.center)]

theorem effective_widths_eq (bounds : CurvatureBounds) (Λ : Scales) :
    Λ.plus - effectiveMuPlus bounds Λ = Λ.minus - effectiveMuMinus bounds Λ := by
  unfold effectiveMuPlus effectiveMuMinus Scales.center Scales.difference
  ring

theorem gapMargin_inflate (bounds : CurvatureBounds) (Λ : Scales)
    (ε : ℝ) (hε : 0 ≤ ε) :
    gapMargin bounds (Λ.inflate ε hε) = gapMargin bounds Λ := by
  simp [gapMargin]

theorem gapMargin_le_centeredOuterRadius (bounds : CurvatureBounds) (Λ : Scales) :
    gapMargin bounds Λ ≤ centeredOuterRadius bounds Λ := by
  exact (min_le_left _ _).trans ((sub_le_sub_right bounds.muPlus_le_lPlus _).trans
    (le_max_left _ _))

theorem centeredOuterRadius_eq (bounds : CurvatureBounds) (Λ : Scales) :
    centeredOuterRadius bounds Λ = bounds.outerRadius + |bounds.outerCenter - Λ.center| := by
  unfold centeredOuterRadius CurvatureBounds.outerRadius CurvatureBounds.outerCenter
  rcases le_total (bounds.lPlus - Λ.center) (bounds.lMinus + Λ.center) with h | h
  · rw [max_eq_right h, abs_of_nonpos (by linarith)]; ring
  · rw [max_eq_left h, abs_of_nonneg (by linarith)]; ring

/-!
## Multiplier and condition number
-/

namespace OuterCompatible

variable {bounds : CurvatureBounds} {Λ : Scales}

/-- Outer-compatible scales make the multiplier nonnegative throughout both curvature bands. -/
theorem multiplier_nonneg (hOuter : OuterCompatible bounds Λ) {σ : ℝ} (hσ : σ ∈ bounds.bands) :
    0 ≤ Λ.multiplier σ := by
  have hLower : -Λ.minus ≤ σ := by
    rcases hσ with hσ | hσ
    · linarith [hσ.1, hOuter.lMinus_le_minus]
    · linarith [hσ.1, bounds.muPlus_pos, Λ.minus_pos]
  have hUpper : σ ≤ Λ.plus := by
    rcases hσ with hσ | hσ
    · linarith [hσ.2, bounds.muMinus_pos, Λ.plus_pos]
    · exact hσ.2.trans hOuter.lPlus_le_plus
  unfold Scales.multiplier
  apply mul_nonneg
  · exact sub_nonneg.mpr ((div_le_one Λ.plus_pos).mpr hUpper)
  · have h : (-1 : ℝ) ≤ σ / Λ.minus := (le_div_iff₀ Λ.minus_pos).mpr (by simpa using hLower)
    linarith

theorem q_nonneg (hOuter : OuterCompatible bounds Λ) : 0 ≤ q bounds Λ := by
  have hContinuous : Continuous Λ.multiplier := by unfold Scales.multiplier; fun_prop
  have hBounded := (bounds.bands_isCompact.image hContinuous).bddAbove
  have hMember : bounds.muPlus ∈ bounds.bands := Or.inr ⟨le_rfl, bounds.muPlus_le_lPlus⟩
  exact (hOuter.multiplier_nonneg hMember).trans (le_csSup hBounded ⟨_, hMember, rfl⟩)

theorem centeredOuterRadius_le_radius (hOuter : OuterCompatible bounds Λ) :
    centeredOuterRadius bounds Λ ≤ Λ.radius := by
  unfold centeredOuterRadius Scales.radius Scales.center Scales.difference
  apply max_le <;> linarith [hOuter.lPlus_le_plus, hOuter.lMinus_le_minus]

end OuterCompatible

namespace Admissible

variable {bounds : CurvatureBounds} {Λ : Scales}

theorem kappaDenominator_pos (hAdmissible : Admissible bounds Λ) :
    0 < kappaDenominator bounds Λ := by
  exact lt_min (mul_pos bounds.muPlus_pos (sub_pos.mpr hAdmissible.difference_lt_muPlus))
    (mul_pos bounds.muMinus_pos (by linarith [hAdmissible.neg_muMinus_lt_difference]))

private theorem multiplier_formula (σ : ℝ) :
    Λ.multiplier σ = 1 - σ * (σ - Λ.difference) / (Λ.plus * Λ.minus) := by
  unfold Scales.multiplier Scales.difference
  field_simp [ne_of_gt Λ.plus_pos, ne_of_gt Λ.minus_pos]; ring

private theorem multiplier_le_endpoints (hAdmissible : Admissible bounds Λ)
    {σ : ℝ} (h : σ ∈ bounds.bands) :
    Λ.multiplier σ ≤ max (Λ.multiplier (-bounds.muMinus)) (Λ.multiplier bounds.muPlus) := by
  have hp : 0 < Λ.plus * Λ.minus := mul_pos Λ.plus_pos Λ.minus_pos
  rcases h with h | h
  · apply le_trans _ (le_max_left _ _)
    rw [multiplier_formula, multiplier_formula]
    apply sub_le_sub_left
    apply (div_le_div_iff_of_pos_right hp).mpr
    have hprod := mul_nonneg (show 0 ≤ -bounds.muMinus - σ by linarith [h.2])
      (show 0 ≤ -σ + bounds.muMinus + Λ.difference by
        linarith [h.2, bounds.muMinus_pos, hAdmissible.neg_muMinus_lt_difference])
    nlinarith
  · apply le_trans _ (le_max_right _ _)
    rw [multiplier_formula, multiplier_formula]
    apply sub_le_sub_left
    apply (div_le_div_iff_of_pos_right hp).mpr
    have hprod := mul_nonneg (show 0 ≤ σ - bounds.muPlus by linarith [h.1])
      (show 0 ≤ σ + bounds.muPlus - Λ.difference by
        linarith [h.1, bounds.muPlus_pos, hAdmissible.difference_lt_muPlus])
    nlinarith

theorem q_eq_max_inner_endpoints (hAdmissible : Admissible bounds Λ) :
    q bounds Λ = max (Λ.multiplier (-bounds.muMinus)) (Λ.multiplier bounds.muPlus) := by
  have hb : BddAbove (Λ.multiplier '' bounds.bands) :=
    ⟨_, by rintro _ ⟨x, hx, rfl⟩; exact multiplier_le_endpoints hAdmissible hx⟩
  apply le_antisymm
  · exact csSup_le (bounds.bands_nonempty.image _) (by
      rintro _ ⟨x, hx, rfl⟩; exact multiplier_le_endpoints hAdmissible hx)
  · exact max_le (le_csSup hb ⟨_, Or.inl ⟨by linarith [bounds.muMinus_le_lMinus], le_rfl⟩, rfl⟩)
      (le_csSup hb ⟨_, Or.inr ⟨le_rfl, bounds.muPlus_le_lPlus⟩, rfl⟩)

theorem q_eq_one_sub_div (hAdmissible : Admissible bounds Λ) :
    q bounds Λ = 1 - kappaDenominator bounds Λ / (Λ.plus * Λ.minus) := by
  rw [hAdmissible.q_eq_max_inner_endpoints, multiplier_formula, multiplier_formula]
  have hp : 0 < Λ.plus * Λ.minus := mul_pos Λ.plus_pos Λ.minus_pos
  unfold kappaDenominator
  have hneg : -bounds.muMinus * (-bounds.muMinus - Λ.difference) =
      bounds.muMinus * (bounds.muMinus + Λ.difference) := by ring
  rw [hneg, ← min_div_div_right (le_of_lt hp)]
  simp only [min_def, max_def]
  split_ifs <;> linarith

theorem q_lt_one (hAdmissible : Admissible bounds Λ) : q bounds Λ < 1 := by
  rw [hAdmissible.q_eq_one_sub_div]
  exact sub_lt_self _ (div_pos hAdmissible.kappaDenominator_pos
    (mul_pos Λ.plus_pos Λ.minus_pos))

theorem kappa_pos (hAdmissible : Admissible bounds Λ) : 0 < kappa bounds Λ := by
  exact one_div_pos.mpr (sub_pos.mpr hAdmissible.q_lt_one)

theorem one_le_kappa (hAdmissible : Admissible bounds Λ) : 1 ≤ kappa bounds Λ := by
  exact (le_div_iff₀ (sub_pos.mpr hAdmissible.q_lt_one)).mpr (by
    simpa using sub_le_self (1 : ℝ) hAdmissible.toOuterCompatible.q_nonneg)

theorem kappa_eq_div (hAdmissible : Admissible bounds Λ) :
    kappa bounds Λ = Λ.plus * Λ.minus / kappaDenominator bounds Λ := by
  unfold kappa
  rw [hAdmissible.q_eq_one_sub_div]
  simp

theorem kappa_sub_one (hAdmissible : Admissible bounds Λ) :
    kappa bounds Λ - 1 = kappa bounds Λ * q bounds Λ := by
  unfold kappa
  field_simp [ne_of_gt (sub_pos.mpr hAdmissible.q_lt_one)]; ring

/-!
## Effective curvature bounds

The largest interval centered at `Λ.center` inside the original inner gap has radius `gapMargin` and endpoints `-effectiveMuMinus` and `effectiveMuPlus`.
-/

theorem center_mem_gap (hAdmissible : Admissible bounds Λ) :
    Λ.center ∈ Set.Ioo (-bounds.muMinus) bounds.muPlus := by
  dsimp [Scales.center]
  constructor <;> linarith [hAdmissible.neg_muMinus_lt_difference, hAdmissible.difference_lt_muPlus,
    bounds.muMinus_pos, bounds.muPlus_pos]

theorem gapMargin_pos (hAdmissible : Admissible bounds Λ) :
    0 < gapMargin bounds Λ := by
  exact lt_min (sub_pos.mpr hAdmissible.center_mem_gap.2)
    (by linarith [hAdmissible.center_mem_gap.1])

theorem abs_center_lt_gapMargin (hAdmissible : Admissible bounds Λ) :
    |Λ.center| < gapMargin bounds Λ := by
  unfold gapMargin
  apply lt_min
  · rw [abs_lt]
    dsimp [Scales.center]
    constructor <;> linarith [bounds.muPlus_pos, hAdmissible.difference_lt_muPlus]
  · rw [abs_lt]
    dsimp [Scales.center]
    constructor <;> linarith [bounds.muMinus_pos, hAdmissible.neg_muMinus_lt_difference]

theorem gapMargin_eq_infDist (hAdmissible : Admissible bounds Λ) :
    gapMargin bounds Λ = Metric.infDist Λ.center bounds.bands := by
  apply le_antisymm
  · apply (Metric.le_infDist bounds.bands_nonempty).mpr
    intro x hx
    rw [Real.dist_eq]
    rcases hx with hx | hx
    · rw [abs_of_nonneg (by linarith [hx.2, hAdmissible.center_mem_gap.1])]
      exact (min_le_right _ _).trans (by linarith [hx.2])
    · rw [abs_of_nonpos (by linarith [hx.1, hAdmissible.center_mem_gap.2])]
      exact (min_le_left _ _).trans (by linarith [hx.1])
  · apply le_min
    · have h := Metric.infDist_le_dist_of_mem
        (s := bounds.bands) (x := Λ.center)
        (y := bounds.muPlus) (Or.inr ⟨le_rfl, bounds.muPlus_le_lPlus⟩)
      simpa [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hAdmissible.center_mem_gap.2.le)] using h
    · have h := Metric.infDist_le_dist_of_mem
        (s := bounds.bands) (x := Λ.center)
        (y := -bounds.muMinus) (Or.inl ⟨by linarith [bounds.muMinus_le_lMinus], le_rfl⟩)
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hAdmissible.center_mem_gap.1])] at h
      simpa [add_comm] using h

theorem effectiveMuPlus_pos (hAdmissible : Admissible bounds Λ) :
    0 < effectiveMuPlus bounds Λ := by
  have h := (abs_lt.mp hAdmissible.abs_center_lt_gapMargin).1
  dsimp [effectiveMuPlus]; linarith

theorem effectiveMuMinus_pos (hAdmissible : Admissible bounds Λ) :
    0 < effectiveMuMinus bounds Λ := by
  exact sub_pos.mpr (abs_lt.mp hAdmissible.abs_center_lt_gapMargin).2

theorem effectiveMuPlus_mul_effectiveMuMinus (hAdmissible : Admissible bounds Λ) :
    effectiveMuPlus bounds Λ * effectiveMuMinus bounds Λ = kappaDenominator bounds Λ := by
  have hp := sub_pos.mpr hAdmissible.center_mem_gap.2
  have hm : 0 < bounds.muMinus + Λ.center := by linarith [hAdmissible.center_mem_gap.1]
  have hc : 2 * Λ.center = Λ.difference := by unfold Scales.center; ring
  unfold effectiveMuPlus effectiveMuMinus gapMargin kappaDenominator
  rcases le_total (bounds.muPlus - Λ.center) (bounds.muMinus + Λ.center) with h | h
  · rw [min_eq_left h, min_eq_left (by nlinarith)]
    rw [← hc]; ring
  · rw [min_eq_right h, min_eq_right (by nlinarith)]
    rw [← hc]; ring

theorem q_eq_radius_gapMargin (hAdmissible : Admissible bounds Λ) :
    q bounds Λ = (Λ.radius ^ 2 - gapMargin bounds Λ ^ 2) / (Λ.plus * Λ.minus) := by
  have h := hAdmissible.effectiveMuPlus_mul_effectiveMuMinus
  dsimp [effectiveMuPlus, effectiveMuMinus] at h
  rw [hAdmissible.q_eq_one_sub_div]
  field_simp [ne_of_gt Λ.plus_pos, ne_of_gt Λ.minus_pos]
  nlinarith [Λ.radius_sq_sub_center_sq]

theorem kappa_mul_steps_mul_effective_inner (hAdmissible : Admissible bounds Λ) :
    kappa bounds Λ * Λ.tauPlus * Λ.tauMinus * effectiveMuPlus bounds Λ * effectiveMuMinus bounds Λ = 1 := by
  rw [show kappa bounds Λ * Λ.tauPlus * Λ.tauMinus * effectiveMuPlus bounds Λ * effectiveMuMinus bounds Λ =
      kappa bounds Λ * Λ.tauPlus * Λ.tauMinus * (effectiveMuPlus bounds Λ * effectiveMuMinus bounds Λ) by ring,
    hAdmissible.effectiveMuPlus_mul_effectiveMuMinus, hAdmissible.kappa_eq_div]
  unfold Scales.tauPlus Scales.tauMinus
  field_simp [ne_of_gt Λ.plus_pos, ne_of_gt Λ.minus_pos, ne_of_gt hAdmissible.kappaDenominator_pos]

/-- Curvature bounds with outer magnitudes `Λ.plus`, `Λ.minus` and effective inner magnitudes. -/
def effectiveBounds (hAdmissible : Admissible bounds Λ) : CurvatureBounds where
  muPlus := effectiveMuPlus bounds Λ
  muMinus := effectiveMuMinus bounds Λ
  lPlus := Λ.plus
  lMinus := Λ.minus
  muPlus_pos := hAdmissible.effectiveMuPlus_pos
  muMinus_pos := hAdmissible.effectiveMuMinus_pos
  muPlus_le_lPlus := (effectiveMuPlus_le_muPlus bounds Λ).trans (bounds.muPlus_le_lPlus.trans hAdmissible.lPlus_le_plus)
  muMinus_le_lMinus := (effectiveMuMinus_le_muMinus bounds Λ).trans (bounds.muMinus_le_lMinus.trans hAdmissible.lMinus_le_minus)

theorem swap (hAdmissible : Admissible bounds Λ) :
    Admissible bounds.swap Λ.swap := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact hAdmissible.lMinus_le_minus
  · exact hAdmissible.lPlus_le_plus
  · dsimp [CurvatureBounds.swap, Scales.difference, Scales.swap]
    have h := hAdmissible.difference_lt_muPlus
    dsimp [Scales.difference] at h; linarith
  · dsimp [CurvatureBounds.swap, Scales.difference, Scales.swap]
    have h := hAdmissible.neg_muMinus_lt_difference
    dsimp [Scales.difference] at h; linarith

theorem q_swap (hAdmissible : Admissible bounds Λ) :
    q bounds.swap Λ.swap = q bounds Λ := by
  rw [hAdmissible.swap.q_eq_max_inner_endpoints, hAdmissible.q_eq_max_inner_endpoints]
  simp only [Scales.multiplier, Scales.swap, CurvatureBounds.swap, neg_div, sub_neg_eq_add]
  rw [max_comm]
  congr 1 <;> ring

theorem kappa_swap (hAdmissible : Admissible bounds Λ) :
    kappa bounds.swap Λ.swap = kappa bounds Λ := by
  simp only [kappa, hAdmissible.q_swap]

theorem inflate (hAdmissible : Admissible bounds Λ) (ε : ℝ) (hε : 0 ≤ ε) :
    Admissible bounds (Λ.inflate ε hε) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · dsimp [Scales.inflate]; linarith [hAdmissible.lPlus_le_plus]
  · dsimp [Scales.inflate]; linarith [hAdmissible.lMinus_le_minus]
  · simpa using hAdmissible.neg_muMinus_lt_difference
  · simpa using hAdmissible.difference_lt_muPlus

theorem strict_inflate (hAdmissible : Admissible bounds Λ) (ε : ℝ) (hε : 0 < ε) :
    StrictAdmissible bounds (Λ.inflate ε (le_of_lt hε)) := by
  refine ⟨hAdmissible.inflate ε hε.le, ?_, ?_⟩
  · dsimp [Scales.inflate]; linarith [hAdmissible.lPlus_le_plus]
  · dsimp [Scales.inflate]; linarith [hAdmissible.lMinus_le_minus]

theorem kappa_inflate (hAdmissible : Admissible bounds Λ) (ε : ℝ) (hε : 0 ≤ ε) :
    kappa bounds (Λ.inflate ε hε) = (Λ.plus + ε) * (Λ.minus + ε) / kappaDenominator bounds Λ := by
  rw [(hAdmissible.inflate ε hε).kappa_eq_div]
  simp only [kappaDenominator, Scales.inflate_difference]
  rfl

theorem centeredOuterRadius_pos (hAdmissible : Admissible bounds Λ) :
    0 < centeredOuterRadius bounds Λ := by
  apply lt_of_lt_of_le _ (le_max_left _ _)
  linarith [hAdmissible.center_mem_gap.2, bounds.muPlus_le_lPlus]

/-- Symmetric curvature bounds for the centered energy. -/
def centeredBounds (hAdmissible : Admissible bounds Λ) : CurvatureBounds where
  muPlus := gapMargin bounds Λ
  muMinus := gapMargin bounds Λ
  lPlus := centeredOuterRadius bounds Λ
  lMinus := centeredOuterRadius bounds Λ
  muPlus_pos := hAdmissible.gapMargin_pos
  muMinus_pos := hAdmissible.gapMargin_pos
  muPlus_le_lPlus := gapMargin_le_centeredOuterRadius bounds Λ
  muMinus_le_lMinus := gapMargin_le_centeredOuterRadius bounds Λ

end Admissible

namespace StrictAdmissible

variable {bounds : CurvatureBounds} {Λ : Scales}

theorem q_pos (hStrict : StrictAdmissible bounds Λ) : 0 < q bounds Λ := by
  rw [hStrict.toAdmissible.q_eq_max_inner_endpoints]
  apply lt_of_lt_of_le _ (le_max_right _ _)
  unfold Scales.multiplier
  apply mul_pos
  · exact sub_pos.mpr ((div_lt_one Λ.plus_pos).mpr
      (bounds.muPlus_le_lPlus.trans_lt hStrict.lPlus_lt_plus))
  · exact add_pos_of_pos_of_nonneg (by norm_num) (div_nonneg bounds.muPlus_pos.le Λ.minus_pos.le)

theorem centeredOuterRadius_lt_radius (hStrict : StrictAdmissible bounds Λ) :
    centeredOuterRadius bounds Λ < Λ.radius := by
  unfold centeredOuterRadius Scales.radius Scales.center Scales.difference
  apply max_lt <;> linarith [hStrict.lPlus_lt_plus, hStrict.lMinus_lt_minus]

theorem swap (hStrict : StrictAdmissible bounds Λ) :
    StrictAdmissible bounds.swap Λ.swap := by
  exact ⟨hStrict.toAdmissible.swap, hStrict.lMinus_lt_minus, hStrict.lPlus_lt_plus⟩

end StrictAdmissible

/-!
## Outer and balanced scales
-/

/-- Scales equal to the two outer curvature magnitudes. -/
def outerScales (bounds : CurvatureBounds) : Scales :=
  ⟨bounds.lPlus, bounds.lMinus, bounds.lPlus_pos, bounds.lMinus_pos⟩

/-- The smallest outer-compatible scales whose center equals the inner curvature center. -/
def balancedScales (bounds : CurvatureBounds) : Scales where
  plus := bounds.muPlus + bounds.maxBandWidth
  minus := bounds.muMinus + bounds.maxBandWidth
  plus_pos := add_pos_of_pos_of_nonneg bounds.muPlus_pos bounds.maxBandWidth_nonneg
  minus_pos := add_pos_of_pos_of_nonneg bounds.muMinus_pos bounds.maxBandWidth_nonneg

@[simp] theorem balancedScales_difference (bounds : CurvatureBounds) :
    (balancedScales bounds).difference = bounds.muPlus - bounds.muMinus := by
  unfold Scales.difference balancedScales
  dsimp
  ring

theorem balancedScales_admissible (bounds : CurvatureBounds) : Admissible bounds (balancedScales bounds) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · change bounds.lPlus ≤ bounds.muPlus + bounds.maxBandWidth
    have h := le_max_left (bounds.lPlus - bounds.muPlus) (bounds.lMinus - bounds.muMinus)
    dsimp [CurvatureBounds.maxBandWidth]
    linarith
  · change bounds.lMinus ≤ bounds.muMinus + bounds.maxBandWidth
    have h := le_max_right (bounds.lPlus - bounds.muPlus) (bounds.lMinus - bounds.muMinus)
    dsimp [CurvatureBounds.maxBandWidth]
    linarith
  · rw [balancedScales_difference]
    linarith [bounds.muPlus_pos]
  · rw [balancedScales_difference]
    linarith [bounds.muMinus_pos]


end
end UN.DAI
