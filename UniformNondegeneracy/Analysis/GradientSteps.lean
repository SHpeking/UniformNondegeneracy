module

public import Mathlib

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

/-- A Lipschitz bound on `g` controls its norm after a signed gradient step. -/
theorem norm_gradient_step_le {g : H → H} {L : NNReal}
    (hLip : LipschitzWith L g)
    (τ : ℝ) (x : H) :
    ‖g (gradientStep g τ x)‖ ≤ (1 + |τ| * (L : ℝ)) * ‖g x‖ := by
  calc
    _ ≤ ‖g (gradientStep g τ x) - g x‖ + ‖g x‖ := norm_le_norm_sub_add _ _
    _ ≤ (L : ℝ) * ‖gradientStep g τ x - x‖ + ‖g x‖ :=
      add_le_add (hLip.norm_sub_le _ _) le_rfl
    _ = _ := by simp [gradientStep, norm_smul, Real.norm_eq_abs]; ring

end UN
