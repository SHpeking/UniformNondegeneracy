module

public import UniformNondegeneracy.Analysis.Taylor

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Global inversion of gradient maps

Gradients with two-sided Lipschitz bounds on a real Hilbert space are bijective. The proof combines finite directional improvement, geometric decay of the inversion residual, and closedness of the gradient range.
-/

noncomputable section

namespace UN.GradientMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-!
## Finite differences and normalized ascent
-/

/-- The finite difference of `E` in direction `v` with increment `h`. -/
private def directionalDifference (E : H → ℝ) (v : H) (h : ℝ) (x : H) : ℝ :=
  (E (x + h • v) - E x) / h

/-- The finite difference of `g` in direction `v` with increment `h`. -/
private def differenceGradient (g : H → H) (v : H) (h : ℝ) (x : H) : H :=
  h⁻¹ • (g (x + h • v) - g x)

/-- A normalized ascent step for the field `V`. -/
private def normalizedAscentStep (V : H → H) (τ : ℝ) (x : H) : H :=
  x + (τ / ‖V x‖) • V x

private def finiteAscent (V : H → H) (τ : ℝ) (x₀ : H) : ℕ → H
  | 0 => x₀
  | N + 1 => normalizedAscentStep V τ (finiteAscent V τ x₀ N)

/-- Contraction factor for the squared inversion residual. -/
private def residualFactor (μ L : ℝ) : ℝ :=
  1 - μ ^ 2 / (2 * L ^ 2)

/-!
## Directional finite differences
-/

private theorem hasGradientAt_directionalDifference
    (E : H → ℝ) (g : H → H)
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (v : H) (h : ℝ) (x : H) :
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
private theorem differenceGradient_norm_bounds
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
private theorem differenceGradient_norm_sub_le
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

/-- The finite difference approximates the directional gradient component. -/
private theorem abs_directionalDifference_sub_inner_le
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

/-- Finite normalized ascent gives directional improvement within radius `R`, with errors controlled by `h` and `N`. -/
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

/-- Directional improvement of at least `μ * R - ε` within radius `R`. -/
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

private theorem residualFactor_nonneg_lt_one (μ L : ℝ) (hμ_pos : 0 < μ) (hμ_le_L : μ ≤ L) :
    0 ≤ residualFactor μ L ∧ residualFactor μ L < 1 := by
  have hL_pos : 0 < L := lt_of_lt_of_le hμ_pos hμ_le_L
  have hr₀_pos : μ ^ 2 ≤ L ^ 2 := sq_le_sq₀ hμ_pos.le hL_pos.le |>.mpr hμ_le_L
  have hden : 0 < 2 * L ^ 2 := by positivity
  dsimp [residualFactor]
  constructor
  · have : μ ^ 2 / (2 * L ^ 2) ≤ 1 := (div_le_one hden).mpr (by nlinarith)
    linarith
  · have : 0 < μ ^ 2 / (2 * L ^ 2) := by positivity
    linarith

/-- Directional improvement contracts the squared inversion residual. -/
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

/-- Repeated contraction gives a sequence whose inversion residual decays geometrically. -/
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

/-- A gradient with two-sided Lipschitz bounds is surjective. -/
theorem surjective_of_bilipschitz
    (E : H → ℝ) (g : H → H) (μ L : ℝ)
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (hμ_pos : 0 < μ)
    (hLower : ∀ x₁ x₂, μ * ‖x₁ - x₂‖ ≤ ‖g x₁ - g x₂‖)
    (hUpper : ∀ x₁ x₂, ‖g x₁ - g x₂‖ ≤ L * ‖x₁ - x₂‖) :
    Function.Surjective g := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · exact fun p => ⟨p, hH.elim _ _⟩
  let _ := hH
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  have hNorm : 0 < ‖x - 0‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hμ_le_L : μ ≤ L := (mul_le_mul_iff_left₀ hNorm).mp ((hLower x 0).trans (hUpper x 0))
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
/-- A positive lower norm bound implies injectivity. -/
theorem injective_of_lower_bound
    (g : H → H) (μ : ℝ) (hμ_pos : 0 < μ)
    (hLower : ∀ x₁ x₂, μ * ‖x₁ - x₂‖ ≤ ‖g x₁ - g x₂‖) :
    Function.Injective g := by
  intro x₁ x₂ hxy
  have hAux := hLower x₁ x₂
  rw [hxy, sub_self, norm_zero] at hAux
  have : ‖x₁ - x₂‖ = 0 := by nlinarith [norm_nonneg (x₁ - x₂)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

theorem bijective_of_bilipschitz
    (E : H → ℝ) (g : H → H) (μ L : ℝ)
    (hGrad : ∀ x, HasGradientAt E (g x) x)
    (hμ_pos : 0 < μ)
    (hLower : ∀ x₁ x₂, μ * ‖x₁ - x₂‖ ≤ ‖g x₁ - g x₂‖)
    (hUpper : ∀ x₁ x₂, ‖g x₁ - g x₂‖ ≤ L * ‖x₁ - x₂‖) :
    Function.Bijective g := by
  exact ⟨injective_of_lower_bound g μ hμ_pos hLower,
    surjective_of_bilipschitz E g μ L hGrad hμ_pos hLower hUpper⟩

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- A right inverse inherits the reciprocal norm bound. -/
theorem inverse_norm_sub_le
    (g gInv : H → H) (μ : ℝ) (hμ_pos : 0 < μ)
    (hLower : ∀ x₁ x₂, μ * ‖x₁ - x₂‖ ≤ ‖g x₁ - g x₂‖)
    (hRightInverse : Function.RightInverse gInv g)
    (p₁ p₂ : H) :
    ‖gInv p₁ - gInv p₂‖ ≤ μ⁻¹ * ‖p₁ - p₂‖ := by
  have hAux := hLower (gInv p₁) (gInv p₂)
  rw [hRightInverse p₁, hRightInverse p₂] at hAux
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ hμ_pos).mpr (by simpa [mul_comm] using hAux)

end UN.GradientMap
