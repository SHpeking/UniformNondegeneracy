module

public import Mathlib

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Quadratic differentiation and Taylor estimates
-/

namespace UN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The gradient of a translated scalar quadratic. -/
theorem hasGradientAt_quadratic (c : ℝ) (x₂ x₁ : H) :
    HasGradientAt (fun x : H => c / 2 * ‖x - x₂‖ ^ 2) (c • (x₁ - x₂)) x₁ := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := (((hasFDerivAt_id x₁).sub_const x₂).norm_sq.const_mul (c / 2))
  convert h using 1 <;> ext v <;> simp [InnerProductSpace.toDual]
  ring

omit [CompleteSpace H] in
/-- A nonnegative function with a global quadratic upper model controls the norm of its linear coefficient. -/
theorem norm_sq_le_of_nonneg_quadratic (f : H → ℝ) (x v : H) (K : ℝ)
    (hK : 0 < K) (hnonneg : ∀ ξ, 0 ≤ f ξ)
    (hupper : ∀ ξ, f ξ ≤ f x + ⟪v, ξ - x⟫ + K / 2 * ‖ξ - x‖ ^ 2) :
    ‖v‖ ^ 2 ≤ 2 * K * f x := by
  have h := (hnonneg (x - K⁻¹ • v)).trans (hupper (x - K⁻¹ • v))
  rw [show x - K⁻¹ • v - x = -K⁻¹ • v by module] at h
  simp only [real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq] at h
  have hid : f x + -K⁻¹ * ‖v‖ ^ 2 + K / 2 * (K⁻¹ ^ 2 * ‖v‖ ^ 2) = f x - ‖v‖ ^ 2 / (2 * K) := by
    field_simp; ring
  rw [hid] at h
  have hm := (div_le_iff₀ (by positivity : 0 < 2 * K)).mp (by linarith : ‖v‖ ^ 2 / (2 * K) ≤ f x)
  nlinarith

end UN

namespace UN.GradientMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem taylor_upper_bound_of_inner
    (E : H → ℝ) (g : H → H) (L : ℝ)
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (hUpper : ∀ x₁ x₂, ⟪g x₁ - g x₂, x₁ - x₂⟫ ≤ L * ‖x₁ - x₂‖ ^ 2)
    (x d : H) :
    E (x + d) - E x - ⟪g x, d⟫ ≤ (L / 2) * ‖d‖ ^ 2 := by
  let f : ℝ → ℝ := fun θ => E (x + θ • d) - E x - θ * ⟪g x, d⟫ - (L / 2) * θ ^ 2 * ‖d‖ ^ 2
  have hf (θ : ℝ) : HasDerivAt f (⟪g (x + θ • d) - g x, d⟫ - L * θ * ‖d‖ ^ 2) θ := by
    have hg := (hGrad (x + θ • d)).hasFDerivAt.comp_hasDerivAt θ
      (((hasDerivAt_id θ).smul_const d).const_add x)
    convert ((hg.sub_const (E x)).sub ((hasDerivAt_id θ).mul_const (⟪g x, d⟫))).sub
      ((((hasDerivAt_id θ).pow 2).const_mul (L / 2)).mul_const (‖d‖ ^ 2)) using 1
    · ext θ
      simp [f]
    · simp only [one_smul, InnerProductSpace.toDual_apply_apply, inner_sub_left, Nat.cast_ofNat, mul_one, id_eq]
      ring
  have hm : AntitoneOn f (Set.Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun θ _ => (hf θ).continuousAt.continuousWithinAt)
      (fun θ _ => (hf θ).differentiableAt.differentiableWithinAt)
    intro θ hθ
    rw [(hf θ).deriv]
    rw [interior_Icc] at hθ
    have h := hUpper (x + θ • d) x
    simp only [add_sub_cancel_left, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hθ.1, mul_pow] at h
    have hh : ⟪g (x + θ • d) - g x, d⟫ ≤ L * θ * ‖d‖ ^ 2 := by
      nlinarith [hθ.1]
    linarith
  have := hm (by simp) (by simp) zero_le_one
  simpa [f] using this

theorem taylor_lower_bound_of_inner
    (E : H → ℝ) (g : H → H) (ℓ : ℝ)
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (hLower : ∀ x₁ x₂, ℓ * ‖x₁ - x₂‖ ^ 2 ≤ ⟪g x₁ - g x₂, x₁ - x₂⟫)
    (x d : H) :
    (ℓ / 2) * ‖d‖ ^ 2 ≤ E (x + d) - E x - ⟪g x, d⟫ := by
  have hneg : ∀ x₁, HasGradientAt (fun x₂ => -E x₂) (-g x₁) x₁ := by
    intro x₁
    rw [hasGradientAt_iff_hasFDerivAt, map_neg]
    exact (hGrad x₁).hasFDerivAt.neg
  have hh : ∀ x₁ x₂, ⟪-g x₁ - -g x₂, x₁ - x₂⟫ ≤ -ℓ * ‖x₁ - x₂‖ ^ 2 := by
    intro x₁ x₂
    have := hLower x₁ x₂
    simp only [inner_sub_left, inner_neg_left] at *
    linarith
  have := taylor_upper_bound_of_inner (fun x₂ => -E x₂) (fun x₂ => -g x₂)
    (-ℓ) hneg hh x d
  simp only [inner_neg_left] at this
  linarith

/-- Quadratic Taylor remainder bound for an energy with a Lipschitz gradient. -/
theorem abs_taylor_remainder_le
    (E : H → ℝ) (g : H → H) (L : ℝ)
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (hUpper : ∀ x₁ x₂, ‖g x₁ - g x₂‖ ≤ L * ‖x₁ - x₂‖)
    (x d : H) :
    |E (x + d) - E x - ⟪g x, d⟫| ≤ (L / 2) * ‖d‖ ^ 2 := by
  have hinner (x₁ x₂ : H) : |⟪g x₁ - g x₂, x₁ - x₂⟫| ≤ L * ‖x₁ - x₂‖ ^ 2 := by
    calc
      _ ≤ ‖g x₁ - g x₂‖ * ‖x₁ - x₂‖ := abs_real_inner_le_norm _ _
      _ ≤ (L * ‖x₁ - x₂‖) * ‖x₁ - x₂‖ := mul_le_mul_of_nonneg_right (hUpper x₁ x₂) (norm_nonneg _)
      _ = _ := by ring
  apply abs_le.mpr
  constructor
  · have := taylor_lower_bound_of_inner E g (-L) hGrad
      (fun x₁ x₂ => by have := (abs_le.mp (hinner x₁ x₂)).1; linarith) x d
    linarith
  · exact taylor_upper_bound_of_inner E g L hGrad
      (fun x₁ x₂ => (abs_le.mp (hinner x₁ x₂)).2) x d

/-- One-sided form of `abs_taylor_remainder_le`. -/
theorem lower_taylor_bound
    (E : H → ℝ) (g : H → H) (L : ℝ)
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (hUpper : ∀ x₁ x₂, ‖g x₁ - g x₂‖ ≤ L * ‖x₁ - x₂‖)
    (x d : H) :
    E x + ⟪g x, d⟫ - (L / 2) * ‖d‖ ^ 2 ≤ E (x + d) := by
  have h := (abs_le.mp (abs_taylor_remainder_le E g L hGrad hUpper x d)).1
  linarith

end UN.GradientMap
