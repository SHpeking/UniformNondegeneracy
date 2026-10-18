module

public import UniformNondegeneracy.Analysis.Taylor

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Global inversion for a gradient with two-sided Lipschitz bounds

This module is independent of UN curvature bounds. It proves global surjectivity of a bi-Lipschitz gradient on a real Hilbert space using finite directional improvement and closedness of the gradient range.

The only differential hypothesis is `HasGradientAt E (g x) x`. Continuity of the gradient is supplied by its upper Lipschitz bound. Neither finite dimensionality, differentiability of `g`, nor surjectivity is assumed.

The proof uses finite normalized ascent to obtain directional improvement, then geometric residual decay. The lower Lipschitz bound and completeness make the gradient range closed, so the improving residuals establish surjectivity.

Proof order:
1. Quadratic Taylor estimates imported from `Analysis.Taylor`.
2. The gradient and estimates for a directional finite difference.
3. Finite normalized ascent and directional improvement.
4. Residual contraction and a geometrically improving sequence.
5. Completeness, surjectivity, and inverse estimates.
-/

noncomputable section

namespace UN.GradientMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-!
## Actual constructions
-/

/-- The directional finite difference of the energy with scalar increment `h` and direction `v`. Its analytic estimates require `0 < h`; the expression itself is a total real-valued function. -/
def directionalDifference (E : H → ℝ) (v : H) (h : ℝ) (x : H) : ℝ :=
  (E (x + h • v) - E x) / h

/-- The gradient of `directionalDifference` when `g` is the gradient of `E` and the finite-difference increment is nonzero. -/
def differenceGradient (g : H → H) (v : H) (h : ℝ) (x : H) : H :=
  h⁻¹ • (g (x + h • v) - g x)

/-- One ascent update in the normalized vector-field direction. The definition is total, including at zeros of the field; its ascent estimates assume that the field is bounded away from zero. -/
private def normalizedAscentStep (V : H → H) (τ : ℝ) (x : H) : H :=
  x + (τ / ‖V x‖) • V x

/-- A finite recursive trajectory of normalized ascent updates. -/
private def finiteAscent (V : H → H) (τ : ℝ) (x₀ : H) : ℕ → H
  | 0 => x₀
  | N + 1 => normalizedAscentStep V τ (finiteAscent V τ x₀ N)

/-- The contraction factor for the *squared residual* in the inversion proof. This is unrelated to the ADA multiplier `UN.q`. -/
private def residualFactor (μ L : ℝ) : ℝ :=
  1 - μ ^ 2 / (2 * L ^ 2)

/-!
## Directional finite differences
-/

/-- Differentiate the finite difference using translation, subtraction, and scalar multiplication. No derivative of `g` is required. -/
theorem hasGradientAt_directionalDifference
    (E : H → ℝ) (g : H → H)
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (v : H) (h : ℝ)
    (x : H) :
    HasGradientAt (directionalDifference E v h) (differenceGradient g v h x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have ht := (hGrad (x + h • v)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const (h • v))
  have hAux := (ht.sub (hGrad x).hasFDerivAt).const_mul h⁻¹
  convert hAux using 1
  · ext x'
    simp [directionalDifference, Function.comp_def, div_eq_mul_inv, mul_comm]
  · simp [differenceGradient, map_smul, map_sub]

omit [CompleteSpace H] in
/-- Two-sided bounds on the finite-difference gradient in a unit direction. -/
theorem differenceGradient_norm_bounds
    (g : H → H) (μ L : ℝ)
    (hLower : ∀ x₁ x₂, μ * ‖x₁ - x₂‖ ≤ ‖g x₁ - g x₂‖)
    (hUpper : ∀ x₁ x₂, ‖g x₁ - g x₂‖ ≤ L * ‖x₁ - x₂‖)
    (v : H) (hv_unit : ‖v‖ = 1)
    (h : ℝ) (hIncrement : 0 < h)
    (x : H) :
    μ ≤ ‖differenceGradient g v h x‖ ∧
    ‖differenceGradient g v h x‖ ≤ L := by
  have hl := hLower (x + h • v) x
  have hu := hUpper (x + h • v) x
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hIncrement, hv_unit, mul_one] at hl hu
  rw [differenceGradient, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hIncrement)]
  rw [inv_mul_eq_div]
  exact ⟨(le_div_iff₀ hIncrement).mpr hl, (div_le_iff₀ hIncrement).mpr hu⟩

omit [CompleteSpace H] in
/-- The difference gradient is globally Lipschitz with bound `2L / h`. -/
theorem differenceGradient_norm_sub_le
    (g : H → H) (L : ℝ)
    (hUpper : ∀ x₁ x₂, ‖g x₁ - g x₂‖ ≤ L * ‖x₁ - x₂‖)
    (v : H) (h : ℝ) (hIncrement : 0 < h)
    (x₁ x₂ : H) :
    ‖differenceGradient g v h x₁ - differenceGradient g v h x₂‖ ≤ (2 * L / h) * ‖x₁ - x₂‖ := by
  have heq : (g (x₁ + h • v) - g x₁) - (g (x₂ + h • v) - g x₂) =
      (g (x₁ + h • v) - g (x₂ + h • v)) - (g x₁ - g x₂) := by abel
  have hAux := norm_sub_le (g (x₁ + h • v) - g (x₂ + h • v)) (g x₁ - g x₂)
  have hu := hUpper (x₁ + h • v) (x₂ + h • v)
  simp only [add_sub_add_right_eq_sub] at hu
  simp only [differenceGradient, ← smul_sub, heq,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hIncrement)]
  calc
    _ ≤ h⁻¹ * (2 * L * ‖x₁ - x₂‖) :=
      mul_le_mul_of_nonneg_left (by linarith [hUpper x₁ x₂]) (inv_nonneg.mpr hIncrement.le)
    _ = _ := by ring

/-- The finite difference approximates the directional gradient component. This follows from `abs_taylor_remainder_le` with displacement `h • v`. -/
theorem abs_directionalDifference_sub_inner_le
    (E : H → ℝ) (g : H → H) (L : ℝ)
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (hUpper : ∀ x₁ x₂, ‖g x₁ - g x₂‖ ≤ L * ‖x₁ - x₂‖)
    (v : H) (hv_unit : ‖v‖ = 1)
    (h : ℝ) (hIncrement : 0 < h)
    (x : H) :
    |directionalDifference E v h x - ⟪g x, v⟫| ≤ L * h / 2 := by
  have hAux := abs_taylor_remainder_le E g L hGrad hUpper x (h • v)
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hIncrement, hv_unit, mul_one] at hAux
  have heq : directionalDifference E v h x - ⟪g x, v⟫ =
      (E (x + h • v) - E x - h * ⟪g x, v⟫) / h := by
    dsimp [directionalDifference]
    field_simp
  rw [heq, abs_div, abs_of_pos hIncrement, div_le_iff₀ hIncrement]
  nlinarith

/-!
## Finite normalized ascent
-/

/-- The finite construction underlying directional improvement. Its endpoint lies within `R` of the start, and the two explicit error terms can be made arbitrarily small by choosing the increment first and the number of steps next.

Use lower Taylor bounds at every finite ascent step and induct on the step count. Then transfer the energy difference to the directional gradient component using `abs_directionalDifference_sub_inner_le` at both endpoints. -/
private theorem finiteAscent_directional_estimates
    (E : H → ℝ) (g : H → H) (μ L : ℝ)
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (hμ_pos : 0 < μ) (hμ_le_L : μ ≤ L)
    (hLower : ∀ x₁ x₂, μ * ‖x₁ - x₂‖ ≤ ‖g x₁ - g x₂‖)
    (hUpper : ∀ x₁ x₂, ‖g x₁ - g x₂‖ ≤ L * ‖x₁ - x₂‖)
    (x₀ v : H) (hv_unit : ‖v‖ = 1)
    (h R : ℝ) (hIncrement : 0 < h) (hR_pos : 0 < R)
    (N : ℕ) (hN_pos : 0 < N) :
    let endpoint := finiteAscent (differenceGradient g v h) (R / (N : ℝ)) x₀ N
    ‖endpoint - x₀‖ ≤ R ∧
    μ * R - L * h - L * R ^ 2 / (h * (N : ℝ)) ≤ ⟪g endpoint - g x₀, v⟫ := by
  let E_h := directionalDifference E v h
  let g_h := differenceGradient g v h
  let δ := R / (N : ℝ)
  have hN : 0 < (N : ℝ) := by exact_mod_cast hN_pos
  have hδ : 0 < δ := div_pos hR_pos hN
  have hL : 0 < L := lt_of_lt_of_le hμ_pos hμ_le_L
  have hG (x₁ : H) : μ ≤ ‖g_h x₁‖ :=
    (differenceGradient_norm_bounds g μ L hLower hUpper
      v hv_unit h hIncrement x₁).1
  have hGpos (x₁ : H) : 0 < ‖g_h x₁‖ := lt_of_lt_of_le hμ_pos (hG x₁)
  have hstepnorm (x₁ : H) : ‖normalizedAscentStep g_h δ x₁ - x₁‖ = δ := by
    simp [normalizedAscentStep, norm_smul, div_mul_cancel₀ _ (hGpos x₁).ne']
    exact hδ.le
  have hstep (x₁ : H) : E_h x₁ + (μ * δ - L / h * δ ^ 2) ≤ E_h (normalizedAscentStep g_h δ x₁) := by
    have ht := lower_taylor_bound E_h g_h (2 * L / h)
      (hasGradientAt_directionalDifference E g hGrad v h)
      (differenceGradient_norm_sub_le g L hUpper v h hIncrement)
      x₁ ((δ / ‖g_h x₁‖) • g_h x₁)
    have hn : ‖(δ / ‖g_h x₁‖) • g_h x₁‖ = δ := by
      simpa [normalizedAscentStep] using hstepnorm x₁
    have hi : ⟪g_h x₁, (δ / ‖g_h x₁‖) • g_h x₁⟫ = δ * ‖g_h x₁‖ := by
      rw [inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    rw [hn, hi] at ht
    change E_h x₁ + δ * ‖g_h x₁‖ - (2 * L / h / 2) * δ ^ 2 ≤ E_h (normalizedAscentStep g_h δ x₁) at ht
    have hc : 2 * L / h / 2 = L / h := by ring
    rw [hc] at ht
    nlinarith [mul_le_mul_of_nonneg_left (hG x₁) hδ.le]
  have hiter (n : ℕ) :
      ‖finiteAscent g_h δ x₀ n - x₀‖ ≤ (n : ℝ) * δ ∧
      E_h x₀ + (n : ℝ) * (μ * δ - L / h * δ ^ 2) ≤ E_h (finiteAscent g_h δ x₀ n) := by
    induction n with
    | zero => simp [finiteAscent]
    | succ n ih =>
      constructor
      · have ht := norm_sub_le_norm_sub_add_norm_sub (finiteAscent g_h δ x₀ (n + 1))
          (finiteAscent g_h δ x₀ n) x₀
        rw [finiteAscent, hstepnorm] at ht
        simp only [finiteAscent, Nat.cast_add, Nat.cast_one]
        linarith [ih.1]
      · have ht := hstep (finiteAscent g_h δ x₀ n)
        simp only [finiteAscent, Nat.cast_add, Nat.cast_one]
        nlinarith [ih.2]
  dsimp only
  have hNδ : (N : ℝ) * δ = R := by dsimp [δ]; field_simp
  have htotal : (N : ℝ) * (μ * δ - L / h * δ ^ 2) = μ * R - L * R ^ 2 / (h * (N : ℝ)) := by
    dsimp [δ]
    field_simp
  have hi := hiter N
  rw [hNδ] at hi
  refine ⟨hi.1, ?_⟩
  have ha := abs_directionalDifference_sub_inner_le E g L hGrad hUpper
    v hv_unit h hIncrement (finiteAscent g_h δ x₀ N)
  have hb := abs_directionalDifference_sub_inner_le E g L hGrad hUpper
    v hv_unit h hIncrement x₀
  rw [htotal] at hi
  rw [inner_sub_left]
  have ha' := (abs_le.mp ha).2
  have hb' := (abs_le.mp hb).1
  dsimp only [E_h] at hi
  linarith [hi.2]

/-- Arbitrarily accurate directional improvement within a prescribed radius. This is an existential finite construction, with no maximizer or compactness assumption. Apply `finiteAscent_directional_estimates` after making its two error terms sum to less than `ε`. -/
theorem exists_directional_improvement
    (E : H → ℝ) (g : H → H) (μ L : ℝ)
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (hμ_pos : 0 < μ) (hμ_le_L : μ ≤ L)
    (hLower : ∀ x₁ x₂, μ * ‖x₁ - x₂‖ ≤ ‖g x₁ - g x₂‖)
    (hUpper : ∀ x₁ x₂, ‖g x₁ - g x₂‖ ≤ L * ‖x₁ - x₂‖)
    (x₀ v : H) (hv_unit : ‖v‖ = 1)
    (R ε : ℝ) (hR_pos : 0 < R) (hε_pos : 0 < ε) :
    ∃ x,
      ‖x - x₀‖ ≤ R ∧
      μ * R - ε ≤ ⟪g x - g x₀, v⟫ := by
  have hL : 0 < L := lt_of_lt_of_le hμ_pos hμ_le_L
  let h := ε / (2 * L)
  have hh : 0 < h := by dsimp [h]; positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (max (0 : ℝ) (2 * L * R ^ 2 / (h * ε)))
  have hn0 : 0 < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hn' : 0 < n := by exact_mod_cast hn0
  have hnlarge : 2 * L * R ^ 2 / (h * ε) < (n : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hn
  have herror : L * R ^ 2 / (h * (n : ℝ)) ≤ ε / 2 := by
    apply (div_le_iff₀ (mul_pos hh hn0)).mpr
    have hh' := (div_lt_iff₀ (mul_pos hh hε_pos)).mp hnlarge
    nlinarith
  have hinc : L * h = ε / 2 := by dsimp [h]; field_simp
  obtain ⟨hdist, hdir⟩ := finiteAscent_directional_estimates E g μ L hGrad hμ_pos
    hμ_le_L hLower hUpper x₀ v hv_unit h R hh hR_pos n hn'
  refine ⟨finiteAscent (differenceGradient g v h) (R / (n : ℝ)) x₀ n,
    hdist, ?_⟩
  rw [hinc] at hdir
  linarith

/-!
## Residual contraction and surjectivity
-/

/-- The inversion residual factor lies in `[0, 1)`. -/
private theorem residualFactor_nonneg_lt_one
    (μ L : ℝ)
    (hμ_pos : 0 < μ) (hμ_le_L : μ ≤ L) :
    0 ≤ residualFactor μ L ∧
    residualFactor μ L < 1 := by
  have hL_pos : 0 < L := lt_of_lt_of_le hμ_pos hμ_le_L
  have hr₀_pos : μ ^ 2 ≤ L ^ 2 := sq_le_sq₀ hμ_pos.le hL_pos.le |>.mpr hμ_le_L
  have hden : 0 < 2 * L ^ 2 := by positivity
  dsimp [residualFactor]
  constructor
  · have : μ ^ 2 / (2 * L ^ 2) ≤ 1 := (div_le_one hden).mpr (by nlinarith)
    linarith
  · have : 0 < μ ^ 2 / (2 * L ^ 2) := by positivity
    linarith

/-- One strict improvement in squared residual for an arbitrary target. For nonzero residual `r₀`, apply directional improvement with radius `μ * r₀ / L^2` and error `μ^2 * r₀ / (4 * L^2)`. For zero residual keep the point. The split also handles the zero-dimensional Hilbert space without a unit-vector existence assumption. -/
private theorem exists_residual_sq_le
    (E : H → ℝ) (g : H → H) (μ L : ℝ)
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (hμ_pos : 0 < μ) (hμ_le_L : μ ≤ L)
    (hLower : ∀ x₁ x₂, μ * ‖x₁ - x₂‖ ≤ ‖g x₁ - g x₂‖)
    (hUpper : ∀ x₁ x₂, ‖g x₁ - g x₂‖ ≤ L * ‖x₁ - x₂‖)
    (x₀ p : H) :
    ∃ x, ‖p - g x‖ ^ 2 ≤ residualFactor μ L * ‖p - g x₀‖ ^ 2 := by
  by_cases hz : p - g x₀ = 0
  · exact ⟨x₀, by simp [hz]⟩
  have hr₀_pos : 0 < ‖p - g x₀‖ := norm_pos_iff.mpr hz
  have hL : 0 < L := lt_of_lt_of_le hμ_pos hμ_le_L
  let r₀ := ‖p - g x₀‖
  let v := r₀⁻¹ • (p - g x₀)
  have hv : ‖v‖ = 1 := by simp [v, r₀, norm_smul, hr₀_pos.ne']
  let R := μ * r₀ / L ^ 2
  let ε := μ ^ 2 * r₀ / (4 * L ^ 2)
  have hR_pos : 0 < R := by dsimp [R, r₀]; positivity
  have hε_pos : 0 < ε := by dsimp [ε, r₀]; positivity
  obtain ⟨x₁, hxr, hxi⟩ := exists_directional_improvement E g μ L
    hGrad hμ_pos hμ_le_L hLower hUpper x₀ v hv R ε hR_pos hε_pos
  have hb : ‖g x₁ - g x₀‖ ≤ L * R :=
    (hUpper x₁ x₀).trans (mul_le_mul_of_nonneg_left hxr hL.le)
  have hb2 : ‖g x₁ - g x₀‖ ^ 2 ≤ (L * R) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb
  have hi : r₀ * (μ * R - ε) ≤ ⟪p - g x₀, g x₁ - g x₀⟫ := by
    dsimp [v] at hxi
    rw [inner_smul_right, real_inner_comm, inv_mul_eq_div] at hxi
    have := (le_div_iff₀ hr₀_pos).mp hxi
    nlinarith
  have hn : ‖p - g x₁‖ ^ 2 = r₀ ^ 2 + ‖g x₁ - g x₀‖ ^ 2 - 2 * ⟪p - g x₀, g x₁ - g x₀⟫ := by
    have heq : p - g x₁ = (p - g x₀) - (g x₁ - g x₀) := by abel
    rw [heq, norm_sub_sq_real]
    dsimp [r₀]
    ring
  have halg : r₀ ^ 2 + (L * R) ^ 2 - 2 * r₀ * (μ * R - ε) = residualFactor μ L * r₀ ^ 2 := by
    dsimp [R, ε, residualFactor]
    field_simp
    ring
  refine ⟨x₁, ?_⟩
  change ‖p - g x₁‖ ^ 2 ≤ residualFactor μ L * r₀ ^ 2
  rw [← halg, hn]
  nlinarith

/-- Classical choice of residual improvements followed by natural-number recursion yields a sequence with a geometric squared-residual bound. No continuity of the chosen update map is needed. -/
private theorem exists_residual_sequence
    (E : H → ℝ) (g : H → H) (μ L : ℝ)
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (hμ_pos : 0 < μ) (hμ_le_L : μ ≤ L)
    (hLower : ∀ x₁ x₂, μ * ‖x₁ - x₂‖ ≤ ‖g x₁ - g x₂‖)
    (hUpper : ∀ x₁ x₂, ‖g x₁ - g x₂‖ ≤ L * ‖x₁ - x₂‖)
    (x₀ p : H) :
    ∃ x : ℕ → H,
      x 0 = x₀ ∧
      ∀ k, ‖p - g (x k)‖ ^ 2 ≤ (residualFactor μ L) ^ k * ‖p - g x₀‖ ^ 2 := by
  classical
  choose next hnext using fun x₁ : H => exists_residual_sq_le E g μ L hGrad
    hμ_pos hμ_le_L hLower hUpper x₁ p
  have hq := (residualFactor_nonneg_lt_one μ L hμ_pos hμ_le_L).1
  refine ⟨fun n => next^[n] x₀, rfl, ?_⟩
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply', pow_succ]
    calc
      _ ≤ residualFactor μ L * ‖p - g (next^[n] x₀)‖ ^ 2 := hnext _
      _ ≤ residualFactor μ L * (residualFactor μ L ^ n * ‖p - g x₀‖ ^ 2) :=
        mul_le_mul_of_nonneg_left ih hq
      _ = _ := by ring

/-- Main independent inversion theorem.

Use `exists_residual_sequence` starting at zero. The squared residual tends to zero because `residualFactor` belongs to `[0, 1)`. The lower norm bound and completeness make the gradient range closed; continuity follows from the upper norm bound. Consequently the limit of the gradient images belongs to the range.

The argument names in this signature form the interface consumed by UN geometry. -/
theorem surjective_of_bounds
    (E : H → ℝ) (g : H → H) (μ L : ℝ)
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (hμ_pos : 0 < μ) (hμ_le_L : μ ≤ L)
    (hLower : ∀ x₁ x₂, μ * ‖x₁ - x₂‖ ≤ ‖g x₁ - g x₂‖)
    (hUpper : ∀ x₁ x₂, ‖g x₁ - g x₂‖ ≤ L * ‖x₁ - x₂‖) :
    Function.Surjective g := by
  have hL : 0 < L := lt_of_lt_of_le hμ_pos hμ_le_L
  have hLip : LipschitzWith ⟨L, hL.le⟩ g := lipschitzWith_iff_norm_sub_le.mpr hUpper
  have hAnti : AntilipschitzWith ⟨μ⁻¹, inv_nonneg.mpr hμ_pos.le⟩ g := by
    apply antilipschitzWith_iff_le_mul_dist.mpr
    intro x₁ x₂
    simp only [dist_eq_norm]
    change ‖x₁ - x₂‖ ≤ μ⁻¹ * ‖g x₁ - g x₂‖
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hμ_pos).mpr (by simpa [mul_comm] using hLower x₁ x₂)
  have hclosed := hAnti.isClosed_range hLip.uniformContinuous
  intro p
  obtain ⟨x, _, hseq⟩ := exists_residual_sequence E g μ L hGrad
    hμ_pos hμ_le_L hLower hUpper 0 p
  obtain ⟨hq0, hq1⟩ := residualFactor_nonneg_lt_one μ L hμ_pos hμ_le_L
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (‖p - g 0‖ ^ 2)
  simp only [zero_mul] at hpow
  have hsquare := squeeze_zero (fun n => sq_nonneg (‖p - g (x n)‖)) hseq hpow
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at hnorm
  have hlim : Filter.Tendsto (fun n => g (x n)) Filter.atTop (nhds p) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [norm_sub_rev] using hnorm
  exact hclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall (fun n => ⟨x n, rfl⟩))

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Injectivity requires only the positive lower bound. -/
theorem injective_of_lower_bound
    (g : H → H) (μ : ℝ) (hμ_pos : 0 < μ)
    (hLower : ∀ x₁ x₂, μ * ‖x₁ - x₂‖ ≤ ‖g x₁ - g x₂‖) :
    Function.Injective g := by
  intro x₁ x₂ hxy
  have hAux := hLower x₁ x₂
  rw [hxy, sub_self, norm_zero] at hAux
  have : ‖x₁ - x₂‖ = 0 := by nlinarith [norm_nonneg (x₁ - x₂)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- Combine the independent surjectivity theorem with the elementary lower-bound injectivity argument. -/
theorem bijective_of_bounds
    (E : H → ℝ) (g : H → H) (μ L : ℝ)
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (hμ_pos : 0 < μ) (hμ_le_L : μ ≤ L)
    (hLower : ∀ x₁ x₂, μ * ‖x₁ - x₂‖ ≤ ‖g x₁ - g x₂‖)
    (hUpper : ∀ x₁ x₂, ‖g x₁ - g x₂‖ ≤ L * ‖x₁ - x₂‖) :
    Function.Bijective g := by
  exact ⟨injective_of_lower_bound g μ hμ_pos hLower,
    surjective_of_bounds E g μ L hGrad
      hμ_pos hμ_le_L hLower hUpper⟩

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- A right inverse inherits the reciprocal norm bound. This formulation is independent of the particular inverse chosen by a later module. -/
theorem inverse_norm_sub_le
    (g gInv : H → H) (μ : ℝ)
    (hμ_pos : 0 < μ)
    (hLower : ∀ x₁ x₂, μ * ‖x₁ - x₂‖ ≤ ‖g x₁ - g x₂‖)
    (hRightInverse : Function.RightInverse gInv g)
    (p₁ p₂ : H) :
    ‖gInv p₁ - gInv p₂‖ ≤ μ⁻¹ * ‖p₁ - p₂‖ := by
  have hAux := hLower (gInv p₁) (gInv p₂)
  rw [hRightInverse p₁, hRightInverse p₂] at hAux
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ hμ_pos).mpr (by simpa [mul_comm] using hAux)

end UN.GradientMap
