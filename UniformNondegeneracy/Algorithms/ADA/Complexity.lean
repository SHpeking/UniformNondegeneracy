module

public import UniformNondegeneracy.Algorithms.ADA.FromUN
public import UniformNondegeneracy.Analysis.ResidualDecay
public import UniformNondegeneracy.Algorithms.ADA.ConditionNumber
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

/-!
# ADA complexity bounds

Exponential bounds for the best residual, every gradient residual, and the distance to the stationary point, for admissible scales and either initial phase. Balanced scales minimize the condition number in the rate.
-/

noncomputable section

namespace UN

open DAI
namespace ADA

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {bounds : CurvatureBounds} {E : H → ℝ} {Λ : Scales}

local notation "g" => gradient E

/-- Exponential residual bound over cycles when the descent step is at least as large as the ascent step. -/
private theorem cycle_residual_decay
    (hUN : IsUN bounds E) (hAdmissible : Admissible bounds Λ)
    (hOrder : Λ.tauMinus ≤ Λ.tauPlus)
    (x₀ : H) (T : ℕ) :
    prefixMin (fun t => ‖g (cycleStart g Λ x₀ t)‖) T ≤
      2 * Real.exp (-Real.log 2 * (T : ℝ) / (17 * kappa bounds Λ)) * ‖g x₀‖ := by
  let κ := kappa bounds Λ
  let W := Nat.ceil (16 * κ)
  have hκ : 1 ≤ κ := one_le_kappa hAdmissible
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

/-- Prefactor in the residual bound. -/
def ratePrefactor : ℝ := 8

/-- Exponential rate constant in the residual bound. -/
def rateConstant : ℝ := Real.log 2 / 34

theorem ratePrefactor_pos : 0 < ratePrefactor := by
  norm_num [ratePrefactor]

theorem rateConstant_pos : 0 < rateConstant := by
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

/-- Rounding two updates to a cycle costs at most one factor of two. -/
private theorem cycle_exponential_le_update_exponential {κ : ℝ} (hk : 1 ≤ κ)
    (T T₁ : ℕ) (hc : T ≤ 2 * T₁ + 2) :
    2 * Real.exp (-Real.log 2 * (T₁ : ℝ) / (17 * κ)) ≤ 4 * Real.exp (-rateConstant * (T : ℝ) / κ) := by
  have hkpos : 0 < κ := by linarith
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hcount : (T : ℝ) ≤ 2 * (T₁ : ℝ) + 2 := by exact_mod_cast hc
  have harg : -Real.log 2 * (T₁ : ℝ) / (17 * κ) ≤ Real.log 2 + (-rateConstant * (T : ℝ) / κ) := by
    unfold rateConstant
    apply (mul_le_mul_iff_of_pos_right (show 0 < 34 * κ by positivity)).mp
    field_simp
    nlinarith [mul_nonneg hlog (show 0 ≤ 34 * κ + 2 * (T₁ : ℝ) - (T : ℝ) by linarith)]
  have he := Real.exp_le_exp.mpr harg
  rw [Real.exp_add, Real.exp_log (by norm_num)] at he
  linarith

/-- The smaller initial ascent step increases the gradient norm by at most a factor of two. -/
private theorem norm_gradient_ascent_le_two
    (hUN : IsUN bounds E) (hAdmissible : Admissible bounds Λ)
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
      add_le_add (hUN.gradient_upper_bound _ _) le_rfl
    _ = (bounds.lMax * Λ.tauMinus + 1) * ‖g x‖ := by
      simp [ascentStep, gradientStep, norm_smul, Real.norm_eq_abs, abs_of_pos Λ.tauMinus_pos]
      ring
    _ ≤ 2 * ‖g x‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

private theorem bestResidual_exponential_decay_of_order
    (hUN : IsUN bounds E) (hAdmissible : Admissible bounds Λ)
    (hOrder : Λ.tauMinus ≤ Λ.tauPlus)
    (firstPhase : Phase) (x₀ : H) (T : ℕ) :
    bestResidual g Λ firstPhase x₀ T ≤
      ratePrefactor * Real.exp (-rateConstant * (T : ℝ) / kappa bounds Λ) * ‖g x₀‖ := by
  by_cases hz : T = 0
  · subst T
    simp only [bestResidual_zero, Nat.cast_zero, mul_zero, zero_div, Real.exp_zero, mul_one]
    unfold ratePrefactor
    nlinarith [norm_nonneg (g x₀)]
  have hseed : ∃ t₀ ≤ 1,
      t₀ ≤ T ∧ phaseAt firstPhase t₀ = .descent ∧
      ‖g (trajectory g Λ firstPhase x₀ t₀)‖ ≤ 2 * ‖g x₀‖ := by
    cases firstPhase with
    | descent =>
      refine ⟨0, by omega, by omega, by rfl, ?_⟩
      simp only [trajectory_zero]
      nlinarith [norm_nonneg (g x₀)]
    | ascent =>
      refine ⟨1, le_rfl, by omega, by rfl, ?_⟩
      exact norm_gradient_ascent_le_two hUN hAdmissible hOrder x₀
  obtain ⟨t₀, hs, hsh, hphase, hres⟩ := hseed
  let xStart := trajectory g Λ firstPhase x₀ t₀
  let T₁ := (T - t₀) / 2
  obtain ⟨t, hi, heq⟩ := prefixMin_attained
    (fun t₁ => ‖g (cycleStart g Λ xStart t₁)‖) T₁
  have hbound := cycle_residual_decay hUN hAdmissible hOrder xStart T₁
  rw [heq] at hbound
  have hindex : t₀ + 2 * t ≤ T := by
    have hm := Nat.mul_div_le (T - t₀) 2
    dsimp [T₁] at hi
    omega
  have hcount : T ≤ 2 * T₁ + 2 := by
    dsimp [T₁]
    omega
  have htrajectory : cycleStart g Λ xStart t = trajectory g Λ firstPhase x₀ (t₀ + 2 * t) := by
    rw [← trajectory_descent_even]
    have ht := trajectory_tail g Λ firstPhase x₀ t₀ (2 * t)
    rw [hphase] at ht
    exact ht
  have hbest : bestResidual g Λ firstPhase x₀ T ≤ ‖g (cycleStart g Λ xStart t)‖ := by
    rw [htrajectory]
    exact prefixMin_le_at _ hindex
  have hexp := cycle_exponential_le_update_exponential (one_le_kappa hAdmissible) T T₁ hcount
  calc
    _ ≤ ‖g (cycleStart g Λ xStart t)‖ := hbest
    _ ≤ 2 * Real.exp (-Real.log 2 * (T₁ : ℝ) / (17 * kappa bounds Λ)) * ‖g xStart‖ := hbound
    _ ≤ (4 * Real.exp (-rateConstant * (T : ℝ) / kappa bounds Λ)) * (2 * ‖g x₀‖) :=
      mul_le_mul hexp hres (norm_nonneg _) (by positivity)
    _ = _ := by unfold ratePrefactor; ring

/-- Exponential decay of the best gradient residual over `T` updates. -/
theorem bestResidual_exponential_decay
    (hUN : IsUN bounds E) (hAdmissible : Admissible bounds Λ)
    (firstPhase : Phase) (x₀ : H) (T : ℕ) :
    bestResidual g Λ firstPhase x₀ T ≤
      ratePrefactor * Real.exp (-rateConstant * (T : ℝ) / kappa bounds Λ) * ‖g x₀‖ := by
  by_cases hOrder : Λ.tauMinus ≤ Λ.tauPlus
  · exact bestResidual_exponential_decay_of_order hUN hAdmissible hOrder firstPhase x₀ T
  · have hs : Λ.swap.tauMinus ≤ Λ.swap.tauPlus := le_of_not_ge hOrder
    have h := bestResidual_exponential_decay_of_order hUN.neg hAdmissible.swap hs firstPhase.flip x₀ T
    simpa only [gradient_neg hUN.differentiable, bestResidual_neg_swap, kappa_swap hAdmissible, norm_neg] using h

/-- An iterate with the residual bound occurs by update `T`. -/
theorem exists_residual_exponential_bound
    (hUN : IsUN bounds E) (hAdmissible : Admissible bounds Λ)
    (firstPhase : Phase) (x₀ : H) (T : ℕ) :
    ∃ t ≤ T, ‖g (trajectory g Λ firstPhase x₀ t)‖ ≤
      ratePrefactor * Real.exp (-rateConstant * (T : ℝ) / kappa bounds Λ) * ‖g x₀‖ := by
  obtain ⟨t, hi, he⟩ := bestResidual_attained g Λ firstPhase x₀ T
  exact ⟨t, hi, he ▸ bestResidual_exponential_decay hUN hAdmissible firstPhase x₀ T⟩

/-- Relative residual bound for a nonstationary initial point. -/
theorem bestResidual_relative_decay
    (hUN : IsUN bounds E) (hAdmissible : Admissible bounds Λ)
    (firstPhase : Phase) (x₀ : H) (T : ℕ) (hInitial : 0 < ‖g x₀‖) :
    bestResidual g Λ firstPhase x₀ T / ‖g x₀‖ ≤
      ratePrefactor * Real.exp (-rateConstant * (T : ℝ) / kappa bounds Λ) := by
  exact (div_le_iff₀ hInitial).mpr
    (bestResidual_exponential_decay hUN hAdmissible firstPhase x₀ T)

/-- Best-iterate complexity at the scales minimizing the ADA condition number. -/
theorem bestResidual_exponential_decay_balancedScales
    (hUN : IsUN bounds E) (firstPhase : Phase) (x₀ : H) (T : ℕ) :
    bestResidual g (balancedScales bounds) firstPhase x₀ T ≤
      ratePrefactor * Real.exp (-rateConstant * (T : ℝ) / ((1 + bounds.maxBandWidth / bounds.muPlus) * (1 + bounds.maxBandWidth / bounds.muMinus))) * ‖g x₀‖ := by
  simpa only [kappa_balancedScales] using
    bestResidual_exponential_decay hUN (balancedScales_admissible bounds) firstPhase x₀ T

/-- An iterate attains the balanced-scale residual bound by the given update horizon. -/
theorem exists_residual_exponential_bound_balancedScales
    (hUN : IsUN bounds E) (firstPhase : Phase) (x₀ : H) (T : ℕ) :
    ∃ t ≤ T, ‖g (trajectory g (balancedScales bounds) firstPhase x₀ t)‖ ≤
      ratePrefactor * Real.exp (-rateConstant * (T : ℝ) / ((1 + bounds.maxBandWidth / bounds.muPlus) * (1 + bounds.maxBandWidth / bounds.muMinus))) * ‖g x₀‖ := by
  simpa only [kappa_balancedScales] using
    exists_residual_exponential_bound hUN (balancedScales_admissible bounds) firstPhase x₀ T

/-!
## Convergence of the trajectory
-/

/-- Prefactor in the gradient residual bound along the full trajectory. -/
def trajectoryPrefactor (bounds : CurvatureBounds) (Λ : Scales) : ℝ :=
  2 * ratePrefactor * (1 + bounds.lMax * max Λ.tauPlus Λ.tauMinus) * Real.sqrt (3 * kappa bounds Λ + 2)

private theorem trajectory_residual_bound_of_order
    (hUN : IsUN bounds E) (hAdmissible : Admissible bounds Λ)
    (hOrder : Λ.tauMinus ≤ Λ.tauPlus)
    (firstPhase : Phase) (x₀ : H) (t : ℕ) :
    ‖g (trajectory g Λ firstPhase x₀ t)‖ ≤
      2 * (1 + bounds.lMax * max Λ.tauPlus Λ.tauMinus) * Real.sqrt (3 * kappa bounds Λ + 2) * ‖g x₀‖ := by
  let A := 1 + bounds.lMax * max Λ.tauPlus Λ.tauMinus
  let C := 3 * kappa bounds Λ + 2
  have hA : 1 ≤ A := by
    have hm : 0 ≤ max Λ.tauPlus Λ.tauMinus := Λ.tauPlus_pos.le.trans (le_max_left _ _)
    dsimp [A]
    linarith [mul_nonneg bounds.lMax_pos.le hm]
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hRoot : 1 ≤ Real.sqrt C := by
    have hC : 1 ≤ C := by dsimp [C]; linarith [one_le_kappa hAdmissible]
    simpa using Real.sqrt_le_sqrt hC
  have hDescent (x : H) (t : ℕ) :
      ‖g (trajectory g Λ .descent x t)‖ ≤ A * Real.sqrt C * ‖g x‖ := by
    have hCycle (t : ℕ) : ‖g (cycleStart g Λ x t)‖ ≤ Real.sqrt C * ‖g x‖ := by
      simpa only [cycleStart_zero] using
        (hasLyapunovBounds_of_isUN hUN hAdmissible hOrder x).residual_le_of_le (Nat.zero_le t)
    by_cases he : t % 2 = 0
    · rw [show t = 2 * (t / 2) by omega, trajectory_descent_even]
      calc
        _ ≤ Real.sqrt C * ‖g x‖ := hCycle _
        _ ≤ A * Real.sqrt C * ‖g x‖ := by
          have h := mul_le_mul_of_nonneg_right hA (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg (g x)))
          simpa only [one_mul, mul_assoc] using h
    · rw [show t = 2 * (t / 2) + 1 by omega, trajectory_descent_odd]
      have hStep := gradientStep_residual_bound hUN.gradient_lipschitz Λ.tauPlus (cycleStart g Λ x (t / 2))
      have hCoeff : 1 + |Λ.tauPlus| * bounds.lMax ≤ A := by
        rw [abs_of_pos Λ.tauPlus_pos]
        dsimp [A]
        nlinarith [mul_le_mul_of_nonneg_left (le_max_left Λ.tauPlus Λ.tauMinus) bounds.lMax_pos.le]
      calc
        _ ≤ (1 + |Λ.tauPlus| * bounds.lMax) * ‖g (cycleStart g Λ x (t / 2))‖ := hStep
        _ ≤ A * ‖g (cycleStart g Λ x (t / 2))‖ := mul_le_mul_of_nonneg_right hCoeff (norm_nonneg _)
        _ ≤ A * (Real.sqrt C * ‖g x‖) := mul_le_mul_of_nonneg_left (hCycle _) hA0
        _ = _ := by ring
  change ‖g (trajectory g Λ firstPhase x₀ t)‖ ≤ 2 * A * Real.sqrt C * ‖g x₀‖
  cases firstPhase with
  | descent =>
    have h := hDescent x₀ t
    have hn : 0 ≤ A * Real.sqrt C * ‖g x₀‖ := by positivity
    nlinarith only [h, hn]
  | ascent =>
    cases t with
    | zero =>
      rw [trajectory_zero]
      have hFactor : 1 ≤ 2 * A * Real.sqrt C := by
        have h := mul_le_mul hA hRoot (by norm_num : (0 : ℝ) ≤ 1) hA0
        nlinarith only [h]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hFactor (norm_nonneg (g x₀))
    | succ t =>
      have hTail : trajectory g Λ .ascent x₀ (t + 1) = trajectory g Λ .descent (ascentStep g Λ x₀) t := by
        simpa [phaseAt, Phase.flip, step, Nat.add_comm] using (trajectory_tail g Λ .ascent x₀ 1 t).symm
      rw [hTail]
      calc
        _ ≤ A * Real.sqrt C * ‖g (ascentStep g Λ x₀)‖ := hDescent _ _
        _ ≤ A * Real.sqrt C * (2 * ‖g x₀‖) :=
          mul_le_mul_of_nonneg_left (norm_gradient_ascent_le_two hUN hAdmissible hOrder x₀)
            (mul_nonneg hA0 (Real.sqrt_nonneg C))
        _ = _ := by ring

private theorem trajectory_residual_bound
    (hUN : IsUN bounds E) (hAdmissible : Admissible bounds Λ)
    (firstPhase : Phase) (x₀ : H) (t : ℕ) :
    ‖g (trajectory g Λ firstPhase x₀ t)‖ ≤
      2 * (1 + bounds.lMax * max Λ.tauPlus Λ.tauMinus) * Real.sqrt (3 * kappa bounds Λ + 2) * ‖g x₀‖ := by
  by_cases hOrder : Λ.tauMinus ≤ Λ.tauPlus
  · exact trajectory_residual_bound_of_order hUN hAdmissible hOrder firstPhase x₀ t
  · have hs : Λ.swap.tauMinus ≤ Λ.swap.tauPlus := le_of_not_ge hOrder
    have h := trajectory_residual_bound_of_order hUN.neg hAdmissible.swap hs firstPhase.flip x₀ t
    simp only [gradient_neg hUN.differentiable, trajectory_neg_swap, kappa_swap hAdmissible, norm_neg] at h
    simpa only [CurvatureBounds.lMax, CurvatureBounds.swap, Scales.swap, Scales.tauPlus, Scales.tauMinus, max_comm] using h

/-- Every gradient residual decays exponentially along the trajectory. -/
theorem residual_exponential_decay
    (hUN : IsUN bounds E) (hAdmissible : Admissible bounds Λ)
    (firstPhase : Phase) (x₀ : H) (t : ℕ) :
    ‖g (trajectory g Λ firstPhase x₀ t)‖ ≤
      trajectoryPrefactor bounds Λ * Real.exp (-rateConstant * (t : ℝ) / kappa bounds Λ) * ‖g x₀‖ := by
  obtain ⟨t₀, ht, hBest⟩ := bestResidual_attained g Λ firstPhase x₀ t
  have hTail := trajectory_residual_bound hUN hAdmissible (phaseAt firstPhase t₀)
    (trajectory g Λ firstPhase x₀ t₀) (t - t₀)
  rw [trajectory_tail, Nat.add_sub_of_le ht, ← hBest] at hTail
  let B := 2 * (1 + bounds.lMax * max Λ.tauPlus Λ.tauMinus) * Real.sqrt (3 * kappa bounds Λ + 2)
  have hB : 0 ≤ B := by
    have hm : 0 ≤ max Λ.tauPlus Λ.tauMinus := Λ.tauPlus_pos.le.trans (le_max_left _ _)
    have hL : 0 ≤ bounds.lMax := bounds.lMax_pos.le
    dsimp [B]
    positivity
  calc
    _ ≤ B * bestResidual g Λ firstPhase x₀ t := hTail
    _ ≤ B * (ratePrefactor * Real.exp (-rateConstant * (t : ℝ) / kappa bounds Λ) * ‖g x₀‖) :=
      mul_le_mul_of_nonneg_left (bestResidual_exponential_decay hUN hAdmissible firstPhase x₀ t) hB
    _ = _ := by dsimp [B, trajectoryPrefactor]; ring

/-- The distance to the stationary point decays exponentially along the trajectory. -/
theorem trajectory_exponential_decay
    (hUN : IsUN bounds E) (hAdmissible : Admissible bounds Λ)
    (firstPhase : Phase) (x₀ : H) (t : ℕ) :
    ‖trajectory g Λ firstPhase x₀ t - stationaryPoint E‖ ≤
      trajectoryPrefactor bounds Λ / bounds.muMin * Real.exp (-rateConstant * (t : ℝ) / kappa bounds Λ) * ‖g x₀‖ := by
  have hDist : ‖trajectory g Λ firstPhase x₀ t - stationaryPoint E‖ ≤ bounds.muMin⁻¹ * ‖g (trajectory g Λ firstPhase x₀ t)‖ := by
    simpa only [hUN.inverseGradient_gradient, sub_zero, stationaryPoint] using
      hUN.inverseGradient_bound (g (trajectory g Λ firstPhase x₀ t)) 0
  calc
    _ ≤ bounds.muMin⁻¹ * ‖g (trajectory g Λ firstPhase x₀ t)‖ := hDist
    _ ≤ bounds.muMin⁻¹ * (trajectoryPrefactor bounds Λ * Real.exp (-rateConstant * (t : ℝ) / kappa bounds Λ) * ‖g x₀‖) :=
      mul_le_mul_of_nonneg_left (residual_exponential_decay hUN hAdmissible firstPhase x₀ t)
        (inv_nonneg.mpr bounds.muMin_pos.le)
    _ = _ := by ring

/-- ADA converges to the unique stationary point from every initial point and either phase. -/
theorem trajectory_tendsto_stationaryPoint
    (hUN : IsUN bounds E) (hAdmissible : Admissible bounds Λ)
    (firstPhase : Phase) (x₀ : H) :
    Filter.Tendsto (trajectory g Λ firstPhase x₀) Filter.atTop (nhds (stationaryPoint E)) := by
  have hExp : Filter.Tendsto (fun t : ℕ => Real.exp (-rateConstant * (t : ℝ) / kappa bounds Λ)) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp
      (Filter.Tendsto.atBot_div_const (kappa_pos hAdmissible)
        (Filter.Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr rateConstant_pos) tendsto_natCast_atTop_atTop))
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun t => by simpa only [dist_eq_norm] using trajectory_exponential_decay hUN hAdmissible firstPhase x₀ t)
  simpa only [mul_zero, zero_mul] using
    (hExp.const_mul (trajectoryPrefactor bounds Λ / bounds.muMin)).mul_const ‖g x₀‖

end ADA
end UN
