module

public import UniformNondegeneracy.Algorithms.ADA.Certificate
public import UniformNondegeneracy.Analysis.ResidualDecay

@[expose] public section

/-!
# The final ADA complexity theorem

The main theorems quantify over every admissible asymmetric scale pair and either initial phase.  Horizons count individual gradient updates.

Proof route:
1. Apply the scalar residual theorem to the canonical Lyapunov certificate.
2. Convert canonical cycle indices to even indices of the full trajectory.
3. Use sign reversal and scale exchange when ascent is the larger step.
4. If the first step is the smaller step, discard it and bound its residual by twice the initial residual using gradient Lipschitz continuity.

Boundary scales and `q = 0` are already handled by the UN-to-DAI interface. There is no perturbation or limiting argument for trajectories in this file.
-/

noncomputable section

namespace UN

open DAI
namespace ADA

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {bounds : CurvatureBounds} {E : H → ℝ} {g : H → H} {Λ : Scales}

/-- Canonical cycle estimate when descent is the larger step.

Apply `hasLyapunovBounds_of_isUN`, then `HasLyapunovBounds.prefixMin_le_exp`.  No independent convergence proof belongs here. -/
theorem canonical_cycle_prefixMin_le_exp
    (hUN : IsUN bounds E g) (hAdmissible : Admissible bounds Λ)
    (hOrder : Λ.tauMinus ≤ Λ.tauPlus)
    (x₀ : H) (T : ℕ) :
    prefixMin (fun t => ‖g (cycleStart g Λ x₀ t)‖) T ≤ 2 * Real.exp (-Real.log 2 * (T : ℝ) / (17 * kappa bounds Λ)) * ‖g x₀‖ := by
  let κ := kappa bounds Λ
  let W := Nat.ceil (16 * κ)
  have hκ : 1 ≤ κ := hAdmissible.one_le_kappa
  have hW_pos : 0 < W := Nat.ceil_pos.mpr (by linarith)
  have hW_lower : 16 * κ ≤ (W : ℝ) := Nat.le_ceil _
  have hWindow : 4 * ((3 * κ + 2) - 1) ≤ (W : ℝ) := by linarith
  have hWindowUpper : (W : ℝ) ≤ 17 * κ := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 16 * κ by linarith)
    dsimp [W]
    linarith
  simpa only [cycleStart_zero] using
    (hasLyapunovBounds_of_isUN hUN hAdmissible hOrder x₀).prefixMin_le_exp
      W hW_pos hWindow (17 * κ) hWindowUpper T

/-- Universal multiplicative constant in the individual-update estimate. -/
def ratePrefactor : ℝ := 8

/-- Universal exponential-rate constant in the individual-update estimate. -/
def rateConstant : ℝ := Real.log 2 / 34

theorem ratePrefactor_pos : 0 < ratePrefactor := by
  norm_num [ratePrefactor]

theorem rateConstant_pos : 0 < rateConstant := by
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

/-- Rounding two updates to a cycle costs at most one factor of two. -/
private theorem cycle_exponential_le_update_exponential {κ : ℝ} (hk : 1 ≤ κ)
    (N T : ℕ) (hc : N ≤ 2 * T + 2) :
    2 * Real.exp (-Real.log 2 * (T : ℝ) / (17 * κ)) ≤ 4 * Real.exp (-rateConstant * (N : ℝ) / κ) := by
  have hkpos : 0 < κ := by linarith
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hcount : (N : ℝ) ≤ 2 * (T : ℝ) + 2 := by exact_mod_cast hc
  have harg : -Real.log 2 * (T : ℝ) / (17 * κ) ≤ Real.log 2 + (-rateConstant * (N : ℝ) / κ) := by
    unfold rateConstant
    apply (mul_le_mul_iff_of_pos_right (show 0 < 34 * κ by positivity)).mp
    field_simp
    nlinarith [mul_nonneg hlog (show 0 ≤ 34 * κ + 2 * (T : ℝ) - (N : ℝ) by linarith)]
  have he := Real.exp_le_exp.mpr harg
  rw [Real.exp_add, Real.exp_log (by norm_num)] at he
  linarith

/-- The smaller initial ascent step increases the gradient norm by at most two. -/
private theorem norm_gradient_ascent_le_two
    (hUN : IsUN bounds E g) (hAdmissible : Admissible bounds Λ)
    (hOrder : Λ.tauMinus ≤ Λ.tauPlus) (x : H) :
    ‖g (ascentStep g Λ x)‖ ≤ 2 * ‖g x‖ := by
  have hs : Λ.plus ≤ Λ.minus :=
    (one_div_le_one_div Λ.minus_pos Λ.plus_pos).mp hOrder
  have hmax : bounds.lMax ≤ Λ.minus :=
    max_le (hAdmissible.lPlus_le_plus.trans hs) hAdmissible.lMinus_le_minus
  have ht : bounds.lMax * Λ.tauMinus ≤ 1 := by
    change bounds.lMax * (1 / Λ.minus) ≤ 1
    rw [mul_one_div]
    exact (div_le_one Λ.minus_pos).mpr hmax
  calc
    _ ≤ ‖g (ascentStep g Λ x) - g x‖ + ‖g x‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ bounds.lMax * ‖ascentStep g Λ x - x‖ + ‖g x‖ :=
      add_le_add (hUN.norm_sub_le_upper _ _) le_rfl
    _ = (bounds.lMax * Λ.tauMinus + 1) * ‖g x‖ := by
      simp [ascentStep, gradientStep, norm_smul, Real.norm_eq_abs, abs_of_pos Λ.tauMinus_pos]
      ring
    _ ≤ 2 * ‖g x‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

private theorem bestResidual_le_exp_of_order
    (hUN : IsUN bounds E g) (hAdmissible : Admissible bounds Λ)
    (hOrder : Λ.tauMinus ≤ Λ.tauPlus)
    (firstPhase : Phase) (x₀ : H) (N : ℕ) :
    bestResidual g Λ firstPhase x₀ N ≤ ratePrefactor * Real.exp (-rateConstant * (N : ℝ) / kappa bounds Λ) * ‖g x₀‖ := by
  by_cases hz : N = 0
  · subst N
    simp only [bestResidual_zero, Nat.cast_zero, mul_zero, zero_div, Real.exp_zero, mul_one]
    unfold ratePrefactor
    nlinarith [norm_nonneg (g x₀)]
  have hseed : ∃ k₀ ≤ 1,
      k₀ ≤ N ∧ phaseAt firstPhase k₀ = .descent ∧
      ‖g (trajectory g Λ firstPhase x₀ k₀)‖ ≤ 2 * ‖g x₀‖ := by
    cases firstPhase with
    | descent =>
      refine ⟨0, by omega, by omega, by rfl, ?_⟩
      simp only [trajectory_zero]
      nlinarith [norm_nonneg (g x₀)]
    | ascent =>
      refine ⟨1, le_rfl, by omega, by rfl, ?_⟩
      exact norm_gradient_ascent_le_two hUN hAdmissible hOrder x₀
  obtain ⟨k₀, hs, hsh, hphase, hres⟩ := hseed
  let xStart := trajectory g Λ firstPhase x₀ k₀
  let T := (N - k₀) / 2
  obtain ⟨t, hi, heq⟩ := prefixMin_attained
    (fun t₁ => ‖g (cycleStart g Λ xStart t₁)‖) T
  have hbound := canonical_cycle_prefixMin_le_exp hUN hAdmissible hOrder xStart T
  rw [heq] at hbound
  have hindex : k₀ + 2 * t ≤ N := by
    have hm := Nat.mul_div_le (N - k₀) 2
    dsimp [T] at hi
    omega
  have hcount : N ≤ 2 * T + 2 := by
    dsimp [T]
    omega
  have htrajectory : cycleStart g Λ xStart t = trajectory g Λ firstPhase x₀ (k₀ + 2 * t) := by
    rw [← trajectory_descent_even]
    have ht := trajectory_tail g Λ firstPhase x₀ k₀ (2 * t)
    rw [hphase] at ht
    exact ht
  have hbest : bestResidual g Λ firstPhase x₀ N ≤ ‖g (cycleStart g Λ xStart t)‖ := by
    rw [htrajectory]
    exact prefixMin_le_at _ hindex
  have hexp := cycle_exponential_le_update_exponential hAdmissible.one_le_kappa N T hcount
  calc
    _ ≤ ‖g (cycleStart g Λ xStart t)‖ := hbest
    _ ≤ 2 * Real.exp (-Real.log 2 * (T : ℝ) / (17 * kappa bounds Λ)) * ‖g xStart‖ := hbound
    _ ≤ (4 * Real.exp (-rateConstant * (N : ℝ) / kappa bounds Λ)) * (2 * ‖g x₀‖) :=
      mul_le_mul hexp hres (norm_nonneg _) (by positivity)
    _ = _ := by unfold ratePrefactor; ring

/-- Best-iterate complexity for every admissible asymmetric scale pair, every initial point, and either initial phase.

The constants are fixed numerical definitions, independent of the Hilbert space, all curvature parameters, the energy, the initial point, and the horizon. The result includes stationary initial points and horizon zero. -/
theorem bestResidual_le_exp
    (hUN : IsUN bounds E g) (hAdmissible : Admissible bounds Λ)
    (firstPhase : Phase) (x₀ : H) (N : ℕ) :
    bestResidual g Λ firstPhase x₀ N ≤ ratePrefactor * Real.exp (-rateConstant * (N : ℝ) / kappa bounds Λ) * ‖g x₀‖ := by
  by_cases hOrder : Λ.tauMinus ≤ Λ.tauPlus
  · exact bestResidual_le_exp_of_order hUN hAdmissible hOrder firstPhase x₀ N
  · have hs : Λ.swap.tauMinus ≤ Λ.swap.tauPlus := le_of_not_ge hOrder
    have h := bestResidual_le_exp_of_order hUN.neg hAdmissible.swap hs firstPhase.flip x₀ N
    simpa only [bestResidual_neg_swap, hAdmissible.kappa_swap, norm_neg] using h

/-- An iterate attaining the claimed residual accuracy exists by the given horizon.  This is the main theorem without a minimum or a division by the initial residual. -/
theorem exists_residual_le_exp
    (hUN : IsUN bounds E g) (hAdmissible : Admissible bounds Λ)
    (firstPhase : Phase) (x₀ : H) (N : ℕ) :
    ∃ k ≤ N, ‖g (trajectory g Λ firstPhase x₀ k)‖ ≤ ratePrefactor * Real.exp (-rateConstant * (N : ℝ) / kappa bounds Λ) * ‖g x₀‖ := by
  obtain ⟨k, hi, he⟩ := bestResidual_attained g Λ firstPhase x₀ N
  exact ⟨k, hi, he ▸ bestResidual_le_exp hUN hAdmissible firstPhase x₀ N⟩

/-- Normalized best-iterate complexity for a nonzero initial gradient.  Positivity makes division by the initial residual legitimate. -/
theorem bestResidual_div_le_exp
    (hUN : IsUN bounds E g) (hAdmissible : Admissible bounds Λ)
    (firstPhase : Phase) (x₀ : H) (N : ℕ)
    (hInitial : 0 < ‖g x₀‖) :
    bestResidual g Λ firstPhase x₀ N / ‖g x₀‖ ≤ ratePrefactor * Real.exp (-rateConstant * (N : ℝ) / kappa bounds Λ) := by
  exact (div_le_iff₀ hInitial).mpr
    (bestResidual_le_exp hUN hAdmissible firstPhase x₀ N)

end ADA
end UN
