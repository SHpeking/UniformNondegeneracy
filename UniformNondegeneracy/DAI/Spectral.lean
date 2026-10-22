module

public import UniformNondegeneracy.DAI.Basic
public import UniformNondegeneracy.Geometry.Spectral

@[expose] public section

/-!
# Hessian spectral bounds from descent–ascent inequalities

For C² energies, DAI gives Hessian spectral bounds. These spectral bounds are equivalent to the global two-point secant bounds at the same scales.
-/

noncomputable section
open Filter Topology
open scoped RealInnerProductSpace

namespace UN
open DAI
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {E : H → ℝ} {Λ : Scales} {ρ : Weights}

omit [CompleteSpace H] in
private theorem directional_slope {F : H → H} {A : H →L[ℝ] H} {x : H}
    (hF : HasFDerivAt F A x) (v : H) :
    Tendsto (fun ε : ℝ => ε⁻¹ • (F (x + ε • v) - F x)) (𝓝[≠] 0) (𝓝 (A v)) := by
  have hLine : HasDerivAt (fun ε : ℝ => x + ε • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hF' : HasFDerivAt F A (x + (0 : ℝ) • v) := by simpa using hF
  have h := (hF'.comp_hasDerivAt 0 hLine).tendsto_slope
  change Tendsto (fun ε : ℝ => (ε - 0)⁻¹ • (F (x + ε • v) - F (x + (0 : ℝ) • v))) _ _ at h
  simpa only [sub_zero, zero_smul, add_zero] using h

private theorem phiPlus_second_order (hE : ContDiff ℝ 2 E) (Λ : Scales) (x v : H) :
    Tendsto (fun ε : ℝ => phiPlus E Λ x (x + ε • v) / ε ^ 2)
      (𝓝[≠] 0) (𝓝 (‖v‖ ^ 2 / 2 - Λ.tauPlus * (⟪(fderiv ℝ (gradient E) x) v, v⟫ / 2))) := by
  have h := (tendsto_const_nhds (x := ‖v‖ ^ 2 / 2)).sub ((bregman_second_order_reverse hE x v).const_mul Λ.tauPlus)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := hε
  simp only [phiPlus, show x - (x + ε • v) = -(ε • v) by module, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp

private theorem phiMinus_second_order (hE : ContDiff ℝ 2 E) (Λ : Scales) (x v : H) :
    Tendsto (fun ε : ℝ => phiMinus E Λ x (x + ε • v) / ε ^ 2)
      (𝓝[≠] 0) (𝓝 (‖v‖ ^ 2 / 2 + Λ.tauMinus * (⟪(fderiv ℝ (gradient E) x) v, v⟫ / 2))) := by
  have h := (tendsto_const_nhds (x := ‖v‖ ^ 2 / 2)).add ((bregman_second_order_reverse hE x v).const_mul Λ.tauMinus)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := hε
  simp only [phiMinus, show x - (x + ε • v) = -(ε • v) by module, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp

private theorem hessian_inequality (hDAI : HasDAI Λ ρ E) (hE : ContDiff ℝ 2 E) (x u v : H) :
    let A := fderiv ℝ (gradient E) x
    2 * ⟪u - Λ.tauPlus • A u, v + Λ.tauMinus • A v⟫ ≤
      ρ.plus * ⟪u - Λ.tauPlus • A u, u⟫ + ρ.minus * ⟪v + Λ.tauMinus • A v, v⟫ := by
  let A := fderiv ℝ (gradient E) x
  have hg := ((contDiff_gradient hE).differentiable one_ne_zero x).hasFDerivAt
  have hD : HasFDerivAt (descentStep (gradient E) Λ) (ContinuousLinearMap.id ℝ H - Λ.tauPlus • A) x :=
    (hasFDerivAt_id x).sub (hg.const_smul Λ.tauPlus)
  have hA : HasFDerivAt (ascentStep (gradient E) Λ) (ContinuousLinearMap.id ℝ H + Λ.tauMinus • A) x := by
    convert (hasFDerivAt_id x).add (hg.const_smul Λ.tauMinus) using 1
    ext y
    simp [ascentStep, gradientStep]
  have hLeft := (directional_slope hD u).inner (𝕜 := ℝ) (directional_slope hA v)
  have hRight := ((phiPlus_second_order hE Λ x u).const_mul ρ.plus).add
    ((phiMinus_second_order hE Λ x v).const_mul ρ.minus)
  have h := le_of_tendsto_of_tendsto hLeft hRight (by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : ε ≠ 0 := hε
    have hh := div_le_div_of_nonneg_right (hDAI.apply x (x + ε • u) (x + ε • v)) (sq_nonneg ε)
    convert hh using 1
    · simp only [real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right]
      field_simp
      ring
    · ring)
  simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.id_apply] at h
  dsimp only
  dsimp [A] at h
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at h ⊢
  linarith

/-- DAI bounds the two-step multiplier on the Hessian spectrum. -/
theorem HasDAI.spectral_bounds (hDAI : HasDAI Λ ρ E) (hE : ContDiff ℝ 2 E) (x : H) :
    ∀ σ ∈ spectrum ℝ (fderiv ℝ (gradient E) x),
      0 ≤ Λ.multiplier σ ∧ Λ.multiplier σ ≤ ρ.plus * ρ.minus := by
  have hA := GradientMap.hessian_selfAdjoint hDAI.hasGradientAt ((contDiff_gradient hE).differentiable one_ne_zero x)
  intro σ hσ
  let a := 1 - Λ.tauPlus * σ
  let b := 1 + Λ.tauMinus * σ
  have hScalar (α : ℝ) : 0 ≤ (ρ.plus * a) * (α * α) + (-2 * a * b) * α + ρ.minus * b := by
    have h := SelfAdjointOperator.quadratic_nonneg_on_spectrum hA hσ
      (a := 2 * α * Λ.tauPlus * Λ.tauMinus)
      (b := -ρ.plus * α ^ 2 * Λ.tauPlus + ρ.minus * Λ.tauMinus - 2 * α * (Λ.tauMinus - Λ.tauPlus))
      (c := ρ.plus * α ^ 2 + ρ.minus - 2 * α) (by
        intro v
        have h := hessian_inequality hDAI hE x (α • v) v
        dsimp only at h
        simp only [map_smul, inner_sub_left, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
        rw [real_inner_comm v ((fderiv ℝ (gradient E) x) v)] at h ⊢
        nlinarith only [h])
    dsimp [a, b]
    nlinarith only [h]
  have hDiscriminant := discrim_le_zero hScalar
  dsimp only [discrim] at hDiscriminant
  have hProduct : (a * b) ^ 2 ≤ (ρ.plus * ρ.minus) * (a * b) := by nlinarith only [hDiscriminant]
  have hNonneg : 0 ≤ ρ.plus * ρ.minus := mul_nonneg ρ.plus_nonneg ρ.minus_nonneg
  have hMultiplier : Λ.multiplier σ = a * b := by dsimp [Scales.multiplier, Scales.tauPlus, Scales.tauMinus, a, b]; ring
  rw [hMultiplier]
  constructor
  · by_contra! hneg
    have h := mul_nonpos_of_nonneg_of_nonpos hNonneg hneg.le
    nlinarith [sq_pos_of_neg hneg]
  · by_contra! hlt
    have hpos : 0 < a * b := hNonneg.trans_lt hlt
    have h := mul_pos hpos (sub_pos.mpr hlt)
    nlinarith only [hProduct, h]

namespace DAI

private theorem multiplier_centered (Λ : Scales) (σ : ℝ) :
    (Λ.plus * Λ.minus) * Λ.multiplier σ = Λ.radius ^ 2 - (σ - Λ.center) ^ 2 := by
  dsimp [Scales.multiplier, Scales.radius, Scales.center, Scales.difference]
  field_simp [Λ.plus_pos.ne', Λ.minus_pos.ne']
  ring

omit [CompleteSpace H] in
private theorem step_inner_centered (Λ : Scales) (u v : H) :
    (Λ.plus * Λ.minus) * ⟪u - Λ.tauPlus • v, u + Λ.tauMinus • v⟫ =
      Λ.radius ^ 2 * ‖u‖ ^ 2 - ‖v - Λ.center • u‖ ^ 2 := by
  simp only [inner_sub_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, sq_abs, mul_pow, real_inner_comm v u]
  dsimp [Scales.tauPlus, Scales.tauMinus, Scales.radius, Scales.center, Scales.difference]
  field_simp [Λ.plus_pos.ne', Λ.minus_pos.ne']
  ring

/-- For C² energies, the multiplier bounds on the Hessian spectrum are equivalent to the two-point secant bounds. -/
theorem spectral_iff_secant (hE : ContDiff ℝ 2 E) (Λ : Scales) (q : ℝ) :
    (∀ x σ, σ ∈ spectrum ℝ (fderiv ℝ (gradient E) x) → 0 ≤ Λ.multiplier σ ∧ Λ.multiplier σ ≤ q) ↔
    (∀ x₁ x₂,
      0 ≤ ⟪descentStep (gradient E) Λ x₁ - descentStep (gradient E) Λ x₂, ascentStep (gradient E) Λ x₁ - ascentStep (gradient E) Λ x₂⟫ ∧
      ⟪descentStep (gradient E) Λ x₁ - descentStep (gradient E) Λ x₂, ascentStep (gradient E) Λ x₁ - ascentStep (gradient E) Λ x₂⟫ ≤ q * ‖x₁ - x₂‖ ^ 2) := by
  have hP : 0 < Λ.plus * Λ.minus := mul_pos Λ.plus_pos Λ.minus_pos
  have hGeometry := centered_secant_iff_spectral_bounds hE Λ.center (Λ.radius ^ 2 - q * (Λ.plus * Λ.minus)) Λ.radius_pos.le
  have hSpectral :
      (∀ x σ, σ ∈ spectrum ℝ (fderiv ℝ (gradient E) x) → 0 ≤ Λ.multiplier σ ∧ Λ.multiplier σ ≤ q) ↔
      (∀ x σ, σ ∈ spectrum ℝ (fderiv ℝ (gradient E) x) →
        Λ.radius ^ 2 - q * (Λ.plus * Λ.minus) ≤ (σ - Λ.center) ^ 2 ∧ (σ - Λ.center) ^ 2 ≤ Λ.radius ^ 2) := by
    apply forall_congr'; intro x
    apply forall_congr'; intro σ
    apply imp_congr_right; intro _
    have hIdentity := multiplier_centered Λ σ
    constructor
    · rintro ⟨hLower, hUpper⟩
      constructor <;> nlinarith [mul_nonneg hP.le hLower, mul_le_mul_of_nonneg_left hUpper hP.le]
    · rintro ⟨hLower, hUpper⟩
      constructor <;> nlinarith
  rw [hSpectral, ← hGeometry]
  apply forall_congr'; intro x₁
  apply forall_congr'; intro x₂
  have hD : descentStep (gradient E) Λ x₁ - descentStep (gradient E) Λ x₂ =
      (x₁ - x₂) - Λ.tauPlus • (gradient E x₁ - gradient E x₂) := by dsimp [descentStep, gradientStep]; module
  have hA : ascentStep (gradient E) Λ x₁ - ascentStep (gradient E) Λ x₂ =
      (x₁ - x₂) + Λ.tauMinus • (gradient E x₁ - gradient E x₂) := by dsimp [ascentStep, gradientStep]; module
  rw [hD, hA]
  have hIdentity := step_inner_centered Λ (x₁ - x₂) (gradient E x₁ - gradient E x₂)
  constructor
  · rintro ⟨hLower, hUpper⟩
    constructor <;> nlinarith
  · rintro ⟨hLower, hUpper⟩
    constructor <;> nlinarith [mul_nonneg hP.le hLower, mul_le_mul_of_nonneg_left hUpper hP.le]

end DAI

end UN
