module

public import UniformNondegeneracy.DAI.Basic
public import UniformNondegeneracy.DAI.Weights
public import UniformNondegeneracy.Algorithms.ADA.Iteration
public import UniformNondegeneracy.Analysis.ResidualDecay

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Corrected energy and Lyapunov bounds

The normalized corrected energy is comparable to the squared gradient norm and decreases by at least the current squared gradient norm over each descent–ascent cycle. These estimates follow from Bregman, signed PL, and DAI bounds when the descent step is at least as large as the ascent step.
-/

noncomputable section

namespace UN.ADA

open DAI

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Bregman and DAI bounds, together with signed PL bounds relative to `Eref`. -/
structure LyapunovInputs (bounds : CurvatureBounds) (E : H → ℝ) (g : H → H)
    (Λ : Scales) (hAdmissible : Admissible bounds Λ)
    (Eref : ℝ) : Prop where
  bregman_bounds : HasBregmanBounds E g Λ.plus Λ.minus
  signed_pl_lower : ∀ x, -(‖g x‖ ^ 2 / (2 * effectiveMuMinus bounds Λ)) ≤ E x - Eref
  signed_pl_upper : ∀ x, E x - Eref ≤ ‖g x‖ ^ 2 / (2 * effectiveMuPlus bounds Λ)
  dai : HasDAI E g Λ hAdmissible.canonicalWeights

/-- The corrected energy $W(y)$ combines the energy gap, descent Bregman difference, and squared ascent displacement. -/
def correctedEnergy (E : H → ℝ) (g : H → H) (Λ : Scales)
    (κ Eref : ℝ) (y : H) : ℝ :=
  let z := descentStep g Λ y
  let yNext := ascentStep g Λ z
  Λ.tauPlus * (E y - Eref) +
    (Λ.tauMinus / Λ.tauPlus) * (κ - 1) * phiPlus E g Λ z y +
    ‖yNext - z‖ ^ 2 / 2

/-- The normalized potential $P(y) = 2W(y)/\tau_{+}^{2}$. -/
def normalizedEnergy (E : H → ℝ) (g : H → H) (Λ : Scales)
    (κ Eref : ℝ) (y : H) : ℝ :=
  2 * correctedEnergy E g Λ κ Eref y / Λ.tauPlus ^ 2

/-!
## Scalar comparison estimates
-/

section ScalarEstimates

variable (τPlus τMinus κ μEffPlus μEffMinus : ℝ)

local notation "τ₊" => τPlus
local notation "τ₋" => τMinus
local notation "μEff₊" => μEffPlus
local notation "μEff₋" => μEffMinus

/-- Scalar lower bound for the corrected energy. `e_y`, `e_z` are energy gaps, `G_y`, `G_z` are squared gradient norms, and `Φ` is the descent Bregman difference. -/
private theorem lower_scalar_bound (e_y e_z G_y G_z Φ : ℝ)
    (hτPlus_pos : 0 < τ₊) (hτMinus_pos : 0 < τ₋)
    (hμEffMinus_pos : 0 < μEff₋)
    (hκ_ge_one : 1 ≤ κ) (hκ_identity : κ * τ₊ * τ₋ * μEff₊ * μEff₋ = 1)
    (hτ_relation : τ₋ - τ₊ = τ₊ * τ₋ * (μEff₊ - μEff₋))
    (hGz_nonneg : 0 ≤ G_z)
    (hEnergy : τ₊ * e_y = τ₊ * e_z + Φ + τ₊ ^ 2 * G_y / 2)
    (hPL : -G_z / (2 * μEff₋) ≤ e_z)
    (hf : τ₊ ^ 2 * G_z ≤ 2 * (1 + τ₊ / τ₋) * Φ) :
    τ₊ ^ 2 * G_y ≤ 2 * (τ₊ * e_y + (τ₋ / τ₊) * (κ - 1) * Φ + τ₋ ^ 2 * G_z / 2) := by
  have hab : 0 < τ₊ + τ₋ := add_pos hτPlus_pos hτMinus_pos
  have hA : 0 ≤ 1 + τ₋ / τ₊ * (κ - 1) := by positivity
  have hFl : τ₊ ^ 2 * τ₋ / (2 * (τ₊ + τ₋)) * G_z ≤ Φ := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < 2 * (τ₊ + τ₋) by positivity)).mpr
    have hfb := mul_le_mul_of_nonneg_left hf hτMinus_pos.le
    field_simp at hfb ⊢
    nlinarith [hfb]
  have hc : -τ₊ / μEff₋ + (1 + τ₋ / τ₊ * (κ - 1)) * τ₊ ^ 2 * τ₋ / (τ₊ + τ₋) + τ₋ ^ 2 =
      τ₋ ^ 2 * (τ₋ + τ₊ * κ * (1 - τ₊ * μEff₊) ^ 2) / (τ₊ + τ₋) := by
    field_simp
    linear_combination τ₊ * hτ_relation - (τ₊ ^ 2 * τ₋ * μEff₊ - 2 * τ₊ * τ₋) * hκ_identity
  have hc0 : 0 ≤ -τ₊ / μEff₋ + (1 + τ₋ / τ₊ * (κ - 1)) * τ₊ ^ 2 * τ₋ / (τ₊ + τ₋) + τ₋ ^ 2 := by
    rw [hc]; positivity
  have hFa := mul_le_mul_of_nonneg_left hFl hA
  have hpla := mul_le_mul_of_nonneg_left hPL hτPlus_pos.le
  have hHc := mul_nonneg hc0 hGz_nonneg
  simp only [div_eq_mul_inv, mul_inv_rev] at hFa hpla hHc ⊢
  nlinarith only [hEnergy, hFa, hpla, hHc]

/-- Scalar upper bound when the descent step is at least as large as the ascent step. -/
private theorem upper_scalar_bound (e_y G_y G_z Φ : ℝ)
    (hτPlus_pos : 0 < τ₊) (hτMinus_pos : 0 < τ₋)
    (hμEffPlus_pos : 0 < μEff₊)
    (hκ_ge_one : 1 ≤ κ) (hκ_identity : κ * τ₊ * τ₋ * μEff₊ * μEff₋ = 1)
    (hbn : τ₋ * μEff₋ ≤ 1) (hba : τ₋ ≤ τ₊)
    (hGy_nonneg : 0 ≤ G_y)
    (hPL : e_y ≤ G_y / (2 * μEff₊))
    (hFu : 2 * τ₋ * Φ ≤ (τ₊ + τ₋) * τ₊ ^ 2 * G_y)
    (hFl : τ₊ ^ 2 * τ₋ * G_z ≤ 2 * (τ₊ + τ₋) * Φ) :
    2 * (τ₊ * e_y + (τ₋ / τ₊) * (κ - 1) * Φ + τ₋ ^ 2 * G_z / 2) ≤ (3 * κ + 2) * τ₊ ^ 2 * G_y := by
  have hab : 0 < τ₊ + τ₋ := add_pos hτPlus_pos hτMinus_pos
  have hk0 : 0 ≤ κ := by linarith
  have hkm : 1 ≤ κ * τ₊ * μEff₊ := by
    have h := mul_le_mul_of_nonneg_left hbn (show 0 ≤ κ * τ₊ * μEff₊ by positivity)
    nlinarith only [h, hκ_identity]
  have ht : τ₊ / μEff₊ ≤ κ * τ₊ ^ 2 := by
    apply (div_le_iff₀ hμEffPlus_pos).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hkm hτPlus_pos.le]
  have henergy : 2 * τ₊ * e_y ≤ κ * τ₊ ^ 2 * G_y := by
    have h1 := mul_le_mul_of_nonneg_left hPL (show 0 ≤ 2 * τ₊ by positivity)
    have h2 := mul_le_mul_of_nonneg_right ht hGy_nonneg
    simp only [div_eq_mul_inv, mul_inv_rev] at h1 h2
    nlinarith only [h1, h2]
  have hnorm : τ₋ ^ 2 * G_z ≤ (τ₊ + τ₋) ^ 2 * G_y := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hτPlus_pos)).mp
    have h1 := mul_le_mul_of_nonneg_left hFu hab.le
    have h2 := mul_le_mul_of_nonneg_left hFl hτMinus_pos.le
    nlinarith only [h1, h2]
  have hnorm2 : τ₋ ^ 2 * G_z ≤ 4 * τ₊ ^ 2 * G_y := by
    have h1 : (τ₊ + τ₋) ^ 2 ≤ 4 * τ₊ ^ 2 := by nlinarith [sq_nonneg (τ₊ - τ₋)]
    exact hnorm.trans (by nlinarith [mul_le_mul_of_nonneg_right h1 hGy_nonneg])
  have hphi : 2 * (τ₋ / τ₊) * (κ - 1) * Φ ≤ 2 * (κ - 1) * τ₊ ^ 2 * G_y := by
    have h1 := mul_le_mul_of_nonneg_left hFu (show 0 ≤ (κ - 1) / τ₊ by positivity)
    have h2 := mul_nonneg (sub_nonneg.mpr hba) (show 0 ≤ (κ - 1) * τ₊ ^ 2 * G_y by positivity)
    field_simp at h1
    apply (mul_le_mul_iff_left₀ hτPlus_pos).mp
    have hid : (2 * (τ₋ / τ₊) * (κ - 1) * Φ) * τ₊ = 2 * τ₋ * (κ - 1) * Φ := by field_simp
    rw [hid]
    nlinarith only [h1, h2]
  nlinarith only [henergy, hnorm2, hphi]

end ScalarEstimates

namespace LyapunovInputs

variable {bounds : CurvatureBounds} {E : H → ℝ} {g : H → H} {Λ : Scales}
variable {hAdmissible : Admissible bounds Λ} {Eref : ℝ}

local notation "Λ₊" => Λ.plus
local notation "Λ₋" => Λ.minus
local notation "τ₊" => Λ.tauPlus
local notation "τ₋" => Λ.tauMinus
local notation "μEff₊" => effectiveMuPlus bounds Λ
local notation "μEff₋" => effectiveMuMinus bounds Λ
local notation "κ" => kappa bounds Λ
local notation "Φ₊" => phiPlus E g Λ
local notation "Φ₋" => phiMinus E g Λ
local notation "P" => normalizedEnergy E g Λ κ Eref

/-!
## Comparison with the squared gradient norm
-/

private theorem phi_descent_gradient (hInputs : LyapunovInputs bounds E g Λ hAdmissible Eref)
    (x : H) :
    τ₊ ^ 2 * ‖g (descentStep g Λ x)‖ ^ 2 ≤ 2 * (1 + τ₊ / τ₋) * Φ₊ (descentStep g Λ x) x := by
  have hp := Λ.plus_pos
  have hm := Λ.minus_pos
  have h := hInputs.bregman_bounds.descentStep_norm_sq_le (descentStep g Λ x) x
  have hid : descentStep g Λ (descentStep g Λ x) - descentStep g Λ x = -τ₊ • g (descentStep g Λ x) := by
    unfold descentStep gradientStep
    module
  rw [hid] at h
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq] at h
  convert h using 1
  dsimp [Scales.tauPlus, Scales.tauMinus]
  field_simp

private theorem corrected_energy_identity (x : H) :
    τ₊ * (E x - Eref) =
      τ₊ * (E (descentStep g Λ x) - Eref) + Φ₊ (descentStep g Λ x) x + τ₊ ^ 2 * ‖g x‖ ^ 2 / 2 := by
  have hv : descentStep g Λ x - x = -τ₊ • g x := by
    unfold descentStep gradientStep
    module
  unfold phiPlus bregman
  rw [hv]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

/-- The squared gradient norm is a lower bound for the normalized corrected energy. -/
theorem residual_sq_le_normalizedEnergy
    (hInputs : LyapunovInputs bounds E g Λ hAdmissible Eref) (x : H) :
    ‖g x‖ ^ 2 ≤ P x := by
  have ha := Λ.tauPlus_pos
  have hb := Λ.tauMinus_pos
  have hm := hAdmissible.effectiveMuPlus_pos
  have hn := hAdmissible.effectiveMuMinus_pos
  have hp := Λ.plus_pos
  have hmn := Λ.minus_pos
  have hw : τ₋ - τ₊ = τ₊ * τ₋ * (μEff₊ - μEff₋) := by
    have h := effective_widths_eq bounds Λ
    dsimp [Scales.tauPlus, Scales.tauMinus]
    field_simp
    linarith
  have h := lower_scalar_bound τ₊ τ₋ κ μEff₊ μEff₋
    (E x - Eref) (E (descentStep g Λ x) - Eref)
    (‖g x‖ ^ 2) (‖g (descentStep g Λ x)‖ ^ 2)
    (Φ₊ (descentStep g Λ x) x)
    ha hb hn hAdmissible.one_le_kappa hAdmissible.kappa_mul_steps_mul_effective_inner hw
    (sq_nonneg _) (corrected_energy_identity x)
    (by simpa only [neg_div] using hInputs.signed_pl_lower (descentStep g Λ x))
    (hInputs.phi_descent_gradient x)
  dsimp only [normalizedEnergy, correctedEnergy]
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  have hv : ascentStep g Λ (descentStep g Λ x) - descentStep g Λ x = τ₋ • g (descentStep g Λ x) := by
    unfold ascentStep gradientStep
    module
  rw [hv]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  nlinarith only [h]

/-- The normalized corrected energy is at most `3 * κ + 2` times the squared gradient norm. -/
theorem normalizedEnergy_le_residual_sq
    (hInputs : LyapunovInputs bounds E g Λ hAdmissible Eref)
    (hOrder : τ₋ ≤ τ₊) (x : H) :
    P x ≤ (3 * κ + 2) * ‖g x‖ ^ 2 := by
  have ha := Λ.tauPlus_pos
  have hb := Λ.tauMinus_pos
  have hm := hAdmissible.effectiveMuPlus_pos
  have hn := hAdmissible.effectiveMuMinus_pos
  have hp := Λ.plus_pos
  have hmn := Λ.minus_pos
  have hbn : τ₋ * μEff₋ ≤ 1 := by
    dsimp [Scales.tauMinus]
    rw [one_div_mul_eq_div]
    exact (div_le_one hmn).mpr hAdmissible.effectiveBounds.muMinus_le_lMinus
  have hFu : 2 * τ₋ * Φ₊ (descentStep g Λ x) x ≤ (τ₊ + τ₋) * τ₊ ^ 2 * ‖g x‖ ^ 2 := by
    have h := hInputs.bregman_bounds.lower (descentStep g Λ x) x
    have hv : descentStep g Λ x - x = -τ₊ • g x := by
      unfold descentStep gradientStep
      module
    unfold phiPlus
    rw [hv] at h ⊢
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq] at h ⊢
    have h1 := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * τ₊ * τ₋ by positivity)
    have hid : τ₋ * Λ₋ = 1 := by dsimp [Scales.tauMinus]; field_simp
    have heq : 2 * τ₊ * τ₋ * (-(Λ₋ / 2) * (τ₊ ^ 2 * ‖g x‖ ^ 2)) = -(τ₊ ^ 3 * ‖g x‖ ^ 2) := by
      calc
        _ = -(τ₊ ^ 3 * ‖g x‖ ^ 2) * (τ₋ * Λ₋) := by ring
        _ = _ := by rw [hid]; ring
    rw [heq] at h1
    nlinarith only [h1]
  have hFl : τ₊ ^ 2 * τ₋ * ‖g (descentStep g Λ x)‖ ^ 2 ≤ 2 * (τ₊ + τ₋) * Φ₊ (descentStep g Λ x) x := by
    have h := mul_le_mul_of_nonneg_left (hInputs.phi_descent_gradient x) hb.le
    field_simp at h
    nlinarith only [h]
  have h := upper_scalar_bound τ₊ τ₋ κ μEff₊ μEff₋
    (E x - Eref) (‖g x‖ ^ 2) (‖g (descentStep g Λ x)‖ ^ 2)
    (Φ₊ (descentStep g Λ x) x)
    ha hb hm hAdmissible.one_le_kappa hAdmissible.kappa_mul_steps_mul_effective_inner hbn hOrder
    (sq_nonneg _) (hInputs.signed_pl_upper x) hFu hFl
  dsimp only [normalizedEnergy, correctedEnergy]
  apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
  have hv : ascentStep g Λ (descentStep g Λ x) - descentStep g Λ x = τ₋ • g (descentStep g Λ x) := by
    unfold ascentStep gradientStep
    module
  rw [hv]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  nlinarith only [h]

/-!
## Decrease over a descent–ascent cycle
-/

private theorem decrease_phiPlus_symm (x₁ x₂ : H) :
    Φ₊ x₁ x₂ + Φ₊ x₂ x₁ = ⟪descentStep g Λ x₁ - descentStep g Λ x₂, x₁ - x₂⟫ := by
  unfold phiPlus bregman descentStep gradientStep
  simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm x₂ x₁]
  ring

private theorem decrease_phiMinus_symm (x₁ x₂ : H) :
    Φ₋ x₁ x₂ + Φ₋ x₂ x₁ = ⟪ascentStep g Λ x₁ - ascentStep g Λ x₂, x₁ - x₂⟫ := by
  unfold phiMinus bregman ascentStep gradientStep
  simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm x₂ x₁]
  ring

/-- One descent–ascent cycle decreases the normalized corrected energy by at least the starting squared gradient norm. -/
theorem normalizedEnergy_decrease
    (hInputs : LyapunovInputs bounds E g Λ hAdmissible Eref)
    (hOrder : τ₋ ≤ τ₊) (y : H) :
    ‖g y‖ ^ 2 ≤ P y - P (descentAscentCycle g Λ y) := by
  let τPlus := τ₊
  let τMinus := τ₋
  have hτPlus_pos : 0 < τPlus := Λ.tauPlus_pos
  have hτMinus_pos : 0 < τMinus := Λ.tauMinus_pos
  have hab : τMinus ≤ τPlus := hOrder
  let z := descentStep g Λ y
  let yNext := ascentStep g Λ z
  let zNext := descentStep g Λ yNext
  let yNextNext := ascentStep g Λ zNext
  have hD (x : H) : descentStep g Λ x - x = -(τPlus / τMinus) • (ascentStep g Λ x - x) := by
    simp only [descentStep, ascentStep, gradientStep, sub_sub_cancel_left,
      neg_smul, neg_neg, smul_smul, neg_mul]
    change -(τPlus • g x) = -((τPlus / τMinus * τMinus) • g x)
    rw [div_mul_cancel₀ _ hτMinus_pos.ne']
  have hA (x : H) : ascentStep g Λ x - x = -(τMinus / τPlus) • (descentStep g Λ x - x) := by
    simp only [descentStep, ascentStep, gradientStep, sub_sub_cancel_left,
      neg_smul, neg_neg, smul_neg, smul_smul, neg_mul]
    change τMinus • g x = (τMinus / τPlus * τPlus) • g x
    rw [div_mul_cancel₀ _ hτPlus_pos.ne']
  have hmul : τPlus / τMinus * (τMinus / τPlus) = 1 := by field_simp
  have hd1 : descentStep g Λ z - descentStep g Λ y = -(τPlus / τMinus) • (yNext - z) := hD z
  have ha1 : ascentStep g Λ z - ascentStep g Λ yNext = -(τMinus / τPlus) • (yNext - zNext) := by
    change yNext - ascentStep g Λ yNext = _
    have hx := hA yNext
    change ascentStep g Λ yNext - yNext = -(τMinus / τPlus) • (zNext - yNext) at hx
    rw [show yNext - ascentStep g Λ yNext = -(ascentStep g Λ yNext - yNext) by module, hx]
    module
  have hd2 : descentStep g Λ yNext - descentStep g Λ zNext = (τPlus / τMinus) • (yNextNext - zNext) := by
    change zNext - descentStep g Λ zNext = _
    rw [show zNext - descentStep g Λ zNext = -(descentStep g Λ zNext - zNext) by module, hD zNext]
    module
  have ha2 : ascentStep g Λ yNext - ascentStep g Λ z = (τMinus / τPlus) • (yNext - zNext) := by
    change ascentStep g Λ yNext - yNext = _
    rw [hA yNext]
    change -(τMinus / τPlus) • (zNext - yNext) = _
    module
  have hDAI₁ := hInputs.dai z y yNext
  have hDAI₂ := hInputs.dai yNext zNext z
  rw [hd1, ha1] at hDAI₁
  rw [hd2, ha2] at hDAI₂
  simp only [real_inner_smul_left, real_inner_smul_right, neg_mul, mul_neg, neg_neg] at hDAI₁ hDAI₂
  rw [← mul_assoc, mul_comm (τMinus / τPlus) (τPlus / τMinus), hmul, one_mul, real_inner_comm] at hDAI₁
  rw [← mul_assoc, mul_comm (τMinus / τPlus) (τPlus / τMinus), hmul, one_mul, real_inner_comm] at hDAI₂
  change ⟪yNext - zNext, yNext - z⟫ ≤
    q bounds Λ * τMinus / τPlus * Φ₊ z y + (τPlus / τMinus) * Φ₋ z yNext at hDAI₁
  change ⟪yNext - zNext, yNextNext - zNext⟫ ≤
    q bounds Λ * τMinus / τPlus * Φ₊ yNext zNext + (τPlus / τMinus) * Φ₋ yNext z at hDAI₂
  have hM : (τPlus / τMinus) * (Φ₋ z yNext + Φ₋ yNext z) = ⟪yNext - zNext, yNext - z⟫ := by
    rw [decrease_phiMinus_symm, ha1]
    simp only [real_inner_smul_left]
    rw [show z - yNext = -(yNext - z) by module, inner_neg_right]
    calc
      _ = (τPlus / τMinus * (τMinus / τPlus)) * ⟪yNext - zNext, yNext - z⟫ := by ring
      _ = _ := by rw [hmul, one_mul]
  have hP : (τMinus / τPlus) * (Φ₊ zNext yNext + Φ₊ yNext zNext) = ⟪yNext - zNext, yNextNext - zNext⟫ := by
    rw [decrease_phiPlus_symm]
    rw [show descentStep g Λ zNext - descentStep g Λ yNext =
      -(descentStep g Λ yNext - descentStep g Λ zNext) by module, hd2]
    simp only [inner_neg_left, real_inner_smul_left]
    rw [show zNext - yNext = -(yNext - zNext) by module, inner_neg_right, real_inner_comm]
    calc
      _ = (τPlus / τMinus * (τMinus / τPlus)) * ⟪yNext - zNext, yNextNext - zNext⟫ := by ring
      _ = _ := by rw [hmul, one_mul]
  have hsum : ⟪yNext - zNext, yNextNext - zNext⟫ ≤
      q bounds Λ * (τMinus / τPlus) * (Φ₊ z y + Φ₊ yNext zNext) := by
    rw [mul_add] at hM
    rw [mul_div_assoc] at hDAI₁ hDAI₂
    nlinarith only [hDAI₁, hDAI₂, hM]
  have hK := hAdmissible.kappa_pos
  have hKq : κ * q bounds Λ = κ - 1 := by
    have hq : 1 - q bounds Λ ≠ 0 := by linarith [hAdmissible.q_lt_one]
    unfold kappa
    field_simp [hq]; ring
  have hscaled := mul_le_mul_of_nonneg_left hsum hK.le
  have hcoeff : κ * (q bounds Λ * (τMinus / τPlus) * (Φ₊ z y + Φ₊ yNext zNext)) =
      (κ - 1) * (τMinus / τPlus) * (Φ₊ z y + Φ₊ yNext zNext) := by
    calc
      _ = (κ * q bounds Λ) * (τMinus / τPlus) * (Φ₊ z y + Φ₊ yNext zNext) := by ring
      _ = _ := by rw [hKq]
  rw [hcoeff] at hscaled
  have hphi : ⟪yNext - zNext, yNextNext - zNext⟫ ≤
      (κ - 1) * (τMinus / τPlus) * (Φ₊ z y - Φ₊ zNext yNext) := by
    nlinarith only [hscaled, congrArg (fun r : ℝ => (κ - 1) * r) hP]
  have hratio : Λ₋ / Λ₊ = τPlus / τMinus := by
    dsimp [τPlus, τMinus, Scales.tauPlus, Scales.tauMinus]
    field_simp
  have hn1 := hInputs.bregman_bounds.descentStep_norm_sq_le yNext zNext
  have hn2 := hInputs.bregman_bounds.descentStep_norm_sq_le zNext yNext
  rw [hd2, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hratio] at hn1
  rw [norm_sub_rev, hd2, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hratio] at hn2
  have hn : 2 * (τPlus / τMinus) ^ 2 * ‖yNextNext - zNext‖ ^ 2 ≤
      2 * (1 + τPlus / τMinus) * (Φ₊ zNext yNext + Φ₊ yNext zNext) := by
    nlinarith only [hn1, hn2]
  have hnscaled := mul_le_mul_of_nonneg_left hn (sq_nonneg (τMinus / τPlus))
  have hleft : (τMinus / τPlus) ^ 2 * (2 * (τPlus / τMinus) ^ 2 * ‖yNextNext - zNext‖ ^ 2) =
      2 * ‖yNextNext - zNext‖ ^ 2 := by
    field_simp
  have hright : (τMinus / τPlus) ^ 2 * (2 * (1 + τPlus / τMinus) * (Φ₊ zNext yNext + Φ₊ yNext zNext)) =
      2 * (1 + τMinus / τPlus) * ⟪yNext - zNext, yNextNext - zNext⟫ := by
    rw [← hP]
    field_simp; ring
  rw [hleft, hright] at hnscaled
  have hnonneg : 0 ≤ ⟪yNext - zNext, yNextNext - zNext⟫ := by
    rw [← hP]
    exact mul_nonneg (div_nonneg hτMinus_pos.le hτPlus_pos.le)
      (add_nonneg (hInputs.bregman_bounds.phiPlus_nonneg zNext yNext)
        (hInputs.bregman_bounds.phiPlus_nonneg yNext zNext))
  have ht : τMinus / τPlus ≤ 1 := (div_le_one hτPlus_pos).mpr hab
  have hhalf : ‖yNextNext - zNext‖ ^ 2 / 2 ≤ ⟪yNext - zNext, yNextNext - zNext⟫ := by
    nlinarith only [hnscaled, mul_nonneg (show 0 ≤ 1 - τMinus / τPlus by linarith) hnonneg]
  have hupper := mul_le_mul_of_nonneg_left (hInputs.bregman_bounds.upper yNext y) hτPlus_pos.le
  have hconst : τPlus * (Λ₊ / 2 * ‖yNext - y‖ ^ 2) = ‖yNext - y‖ ^ 2 / 2 := by
    dsimp [τPlus, Scales.tauPlus]
    field_simp [Λ.plus_pos.ne']
  rw [hconst] at hupper
  unfold bregman at hupper
  have hnorm : ‖yNext - z‖ ^ 2 = ‖yNext - y‖ ^ 2 + 2 * τPlus * ⟪g y, yNext - y⟫ + τPlus ^ 2 * ‖g y‖ ^ 2 := by
    rw [show yNext - z = (yNext - y) + τPlus • g y by dsimp [z, descentStep, gradientStep, τPlus]; module]
    rw [norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right]
    rw [real_inner_comm (g y) (yNext - y)]
    ring
  have henergy : τPlus * (E yNext - E y) ≤ (‖yNext - z‖ ^ 2 - τPlus ^ 2 * ‖g y‖ ^ 2) / 2 := by
    nlinarith only [hupper, hnorm]
  change ‖g y‖ ^ 2 ≤
    2 * (τPlus * (E y - Eref) + (τMinus / τPlus) * (κ - 1) * Φ₊ z y + ‖yNext - z‖ ^ 2 / 2) / τPlus ^ 2 -
    2 * (τPlus * (E yNext - Eref) + (τMinus / τPlus) * (κ - 1) * Φ₊ zNext yNext + ‖yNextNext - zNext‖ ^ 2 / 2) / τPlus ^ 2
  rw [← sub_div]
  apply (le_div_iff₀ (sq_pos_of_pos hτPlus_pos)).mpr
  nlinarith only [hphi, hhalf, henergy]

/-- The normalized corrected energy satisfies the Lyapunov bounds along ADA cycles. -/
theorem hasLyapunovBounds
    (hInputs : LyapunovInputs bounds E g Λ hAdmissible Eref)
    (hOrder : τ₋ ≤ τ₊) (x₀ : H) :
    HasLyapunovBounds (3 * κ + 2)
      (fun t => ‖g (cycleStart g Λ x₀ t)‖)
      (fun t => P (cycleStart g Λ x₀ t)) := by
  refine
    { one_le_comparison := by linarith [hAdmissible.one_le_kappa]
      residual_nonneg := fun t => norm_nonneg _
      residual_sq_le_potential := ?_
      potential_le_residual_sq := ?_
      sufficient_decrease := ?_ }
  · intro t
    exact hInputs.residual_sq_le_normalizedEnergy _
  · intro t
    exact hInputs.normalizedEnergy_le_residual_sq hOrder _
  · intro t
    simpa only [cycleStart] using
      hInputs.normalizedEnergy_decrease hOrder (cycleStart g Λ x₀ t)

end LyapunovInputs
end UN.ADA
