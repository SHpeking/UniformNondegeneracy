module

public import UniformNondegeneracy.Analysis.Taylor
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Signed gradient steps

Positive `τ` means descent; negative `τ` means ascent.
-/

noncomputable section
namespace UN
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def gradientStep (g : H → H) (τ : ℝ) (x : H) : H :=
  x - τ • g x

/-- Potential whose gradient is the signed gradient step. -/
def gradientStepPotential (E : H → ℝ) (s : ℝ) : H → ℝ :=
  fun x => (1 / 2 : ℝ) * ‖x‖ ^ 2 - s * E x

/-- A Lipschitz bound on `g` controls its norm after a signed gradient step. -/
theorem gradientStep_residual_bound {g : H → H} {L : NNReal}
    (hLip : LipschitzWith L g) (τ : ℝ) (x : H) :
    ‖g (gradientStep g τ x)‖ ≤ (1 + |τ| * (L : ℝ)) * ‖g x‖ := by
  calc
    _ ≤ ‖g (gradientStep g τ x) - g x‖ + ‖g x‖ := norm_le_norm_sub_add _ _
    _ ≤ (L : ℝ) * ‖gradientStep g τ x - x‖ + ‖g x‖ :=
      add_le_add (hLip.norm_sub_le _ _) le_rfl
    _ = _ := by simp [gradientStep, norm_smul, Real.norm_eq_abs]; ring

variable [CompleteSpace H]

theorem hasGradientAt_gradientStepPotential {E : H → ℝ} {x : H} (hE : DifferentiableAt ℝ E x) (s : ℝ) :
    HasGradientAt (gradientStepPotential E s) (x - s • gradient E x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  unfold gradientStepPotential
  convert! ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (1 / 2 : ℝ)).sub
    (hE.hasGradientAt.hasFDerivAt.const_mul s) using 1
  ext v
  simp [InnerProductSpace.toDual_apply_apply]

end UN
