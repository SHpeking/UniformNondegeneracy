module

public import UniformNondegeneracy.Core.Basic
public import UniformNondegeneracy.DAI.Secant
public import UniformNondegeneracy.DAI.Weights

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Uniform nondegeneracy from descent–ascent inequalities

Secant bounds with coefficient below one determine UN curvature bands. These bounds follow from a balanced DAI or from DAI for a C² energy. Two DAIs at the outer and balanced scales also recover prescribed curvature bands.
-/

namespace UN

open DAI

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

namespace DAI

noncomputable section

variable {E : H → ℝ}

/-- Curvature bands determined by descent–ascent secant bounds with coefficient `0 ≤ q < 1`. -/
def curvatureBounds (Λ : Scales) (q : ℝ) (hq : 0 ≤ q) (hqOne : q < 1) : CurvatureBounds := by
  let r := Real.sqrt (Λ.center ^ 2 + (1 - q) * (Λ.plus * Λ.minus))
  have hP : 0 < Λ.plus * Λ.minus := mul_pos Λ.plus_pos Λ.minus_pos
  have hGap : 0 < (1 - q) * (Λ.plus * Λ.minus) := mul_pos (sub_pos.mpr hqOne) hP
  have hRad : 0 ≤ Λ.center ^ 2 + (1 - q) * (Λ.plus * Λ.minus) := add_nonneg (sq_nonneg _) hGap.le
  have hs : r ^ 2 = Λ.center ^ 2 + (1 - q) * (Λ.plus * Λ.minus) := Real.sq_sqrt hRad
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hAbs : |Λ.center| < r := by
    simpa only [Real.sqrt_sq_eq_abs] using
      Real.sqrt_lt_sqrt (sq_nonneg Λ.center) (lt_add_of_pos_right (Λ.center ^ 2) hGap)
  have hRadius : r ≤ Λ.radius := by
    have h := Λ.radius_sq_sub_center_sq
    nlinarith [Λ.radius_pos, mul_nonneg hq hP.le]
  exact
    { muPlus := r + Λ.center
      muMinus := r - Λ.center
      lPlus := Λ.plus
      lMinus := Λ.minus
      muPlus_pos := by linarith [neg_abs_le Λ.center]
      muMinus_pos := by linarith [le_abs_self Λ.center]
      muPlus_le_lPlus := by dsimp [Scales.center, Scales.difference, Scales.radius] at *; linarith
      muMinus_le_lMinus := by dsimp [Scales.center, Scales.difference, Scales.radius] at *; linarith }

omit [CompleteSpace H] in
private theorem curvatureBounds_secant_identity (Λ : Scales) (q : ℝ) (hq : 0 ≤ q) (hqOne : q < 1) (u v : H) :
    let bounds := curvatureBounds Λ q hq hqOne
    ⟪v + bounds.muMinus • u, v - bounds.muPlus • u⟫ =
      ⟪v + Λ.minus • u, v - Λ.plus • u⟫ + q * (Λ.plus * Λ.minus) * ‖u‖ ^ 2 := by
  have hRad : 0 ≤ Λ.center ^ 2 + (1 - q) * (Λ.plus * Λ.minus) :=
    add_nonneg (sq_nonneg _) (mul_nonneg (sub_pos.mpr hqOne).le (mul_pos Λ.plus_pos Λ.minus_pos).le)
  have hSquare := congrArg (fun t : ℝ => t * ‖u‖ ^ 2) (Real.sq_sqrt hRad)
  dsimp [curvatureBounds]
  simp only [inner_add_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm u v]
  dsimp [Scales.center, Scales.difference] at hSquare ⊢
  nlinarith only [hSquare]

/-- Secant bounds with coefficient below one give uniform nondegeneracy. -/
theorem isUN_of_secant_bounds (hE : ContDiff ℝ 1 E) (Λ : Scales) (q : ℝ) (hq : 0 ≤ q) (hqOne : q < 1)
    (hSecant : ∀ x₁ x₂,
      0 ≤ ⟪descentStep (gradient E) Λ x₁ - descentStep (gradient E) Λ x₂, ascentStep (gradient E) Λ x₁ - ascentStep (gradient E) Λ x₂⟫ ∧
      ⟪descentStep (gradient E) Λ x₁ - descentStep (gradient E) Λ x₂, ascentStep (gradient E) Λ x₁ - ascentStep (gradient E) Λ x₂⟫ ≤ q * ‖x₁ - x₂‖ ^ 2) :
    IsUN (curvatureBounds Λ q hq hqOne) E := by
  refine ⟨hE, ?_, ?_⟩
  · intro x₁ x₂
    rw [curvatureBounds_secant_identity]
    have h := mul_le_mul_of_nonneg_left (hSecant x₁ x₂).2 (mul_pos Λ.plus_pos Λ.minus_pos).le
    rw [step_inner_mul_scales] at h
    linarith
  · intro x₁ x₂
    change ⟪gradient E x₁ - gradient E x₂ + Λ.minus • (x₁ - x₂), gradient E x₁ - gradient E x₂ - Λ.plus • (x₁ - x₂)⟫ ≤ 0
    have h := mul_nonneg (mul_pos Λ.plus_pos Λ.minus_pos).le (hSecant x₁ x₂).1
    rw [step_inner_mul_scales] at h
    linarith

end
end DAI

namespace HasDAI

variable {E : H → ℝ} {Λ : Scales} {ρ : Weights}

/-- A balanced DAI with weight product below one gives uniform nondegeneracy. -/
theorem isUN_of_balanced (hDAI : HasDAI Λ ρ E) (hBalanced : ρ.Balanced Λ) (hProduct : ρ.plus * ρ.minus < 1) :
    IsUN (DAI.curvatureBounds Λ (ρ.plus * ρ.minus) (mul_nonneg ρ.plus_nonneg ρ.minus_nonneg) hProduct) E :=
  DAI.isUN_of_secant_bounds hDAI.contDiff Λ (ρ.plus * ρ.minus) _ hProduct (hDAI.secant_bounds_of_balanced hBalanced)

/-- A C² energy satisfying DAI with weight product below one is uniformly nondegenerate. -/
theorem isUN_of_C2 (hDAI : HasDAI Λ ρ E) (hE : ContDiff ℝ 2 E) (hProduct : ρ.plus * ρ.minus < 1) :
    IsUN (DAI.curvatureBounds Λ (ρ.plus * ρ.minus) (mul_nonneg ρ.plus_nonneg ρ.minus_nonneg) hProduct) E :=
  DAI.isUN_of_secant_bounds hDAI.contDiff Λ (ρ.plus * ρ.minus) _ hProduct (hDAI.secant_bounds_of_C2 hE)

end HasDAI

omit [CompleteSpace H] in
private lemma balanced_secant_identity (bounds : CurvatureBounds) (u v : H) :
    ⟪v + bounds.muMinus • u, v - bounds.muPlus • u⟫ =
      ⟪v + (balancedScales bounds).minus • u, v - (balancedScales bounds).plus • u⟫ +
        bounds.maxBandWidth * (bounds.maxBandWidth + bounds.muPlus + bounds.muMinus) * ‖u‖ ^ 2 := by
  simp only [balancedScales, inner_add_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm u v]
  ring

/-- DAIs at the outer and balanced scales give uniform nondegeneracy. -/
theorem isUN_of_two_DAIs (bounds : CurvatureBounds) {E : H → ℝ}
    (hOuter : HasDAI (outerScales bounds) (outerSecantWeights bounds) E)
    (hInner : HasDAI (balancedScales bounds) (innerSecantWeights bounds) E) :
    IsUN bounds E := by
  refine ⟨hOuter.contDiff, ?_, ?_⟩
  · intro x₁ x₂
    have h := (hInner.curvature_secant_bounds_of_balanced (innerSecantWeights_balanced bounds) x₁ x₂).1
    rw [innerSecantWeights_product] at h
    rw [balanced_secant_identity]
    linarith
  · intro x₁ x₂
    exact (hOuter.curvature_secant_bounds_of_balanced (outerSecantWeights_balanced bounds) x₁ x₂).2

end UN
