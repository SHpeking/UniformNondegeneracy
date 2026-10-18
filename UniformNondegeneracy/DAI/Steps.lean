module

public import UniformNondegeneracy.DAI.Parameters
public import UniformNondegeneracy.Analysis.GradientSteps

@[expose] public section

/-!
# Descent and ascent maps at the selected DAI scales
-/

noncomputable section
namespace UN.DAI
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Descent with step size `1 / Λ.plus`. -/
def descentStep (g : H → H) (Λ : Scales) (x : H) : H :=
  gradientStep g Λ.tauPlus x

/-- Ascent with step size `1 / Λ.minus`. -/
def ascentStep (g : H → H) (Λ : Scales) (x : H) : H :=
  gradientStep g (-Λ.tauMinus) x

end UN.DAI
