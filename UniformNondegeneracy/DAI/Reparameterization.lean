module

public import UniformNondegeneracy.DAI.Admissibility
public import UniformNondegeneracy.Geometry.Reparameterization

@[expose] public section

/-!
# Curvature bounds at descent–ascent scales

Specializations of curvature reparameterization to admissible DAI scales.
-/

noncomputable section

namespace UN.IsUN

open DAI

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {bounds : CurvatureBounds} {E : H → ℝ} {Λ : Scales}

/-- Admissible scales give effective inner bounds and the selected outer bounds. -/
theorem effectiveBounds (hUN : IsUN bounds E) (hAdmissible : Admissible bounds Λ) :
    IsUN hAdmissible.effectiveBounds E :=
  hUN.mono (effectiveMuPlus_le_muPlus bounds Λ) (effectiveMuMinus_le_muMinus bounds Λ)
    hAdmissible.lPlus_le_plus hAdmissible.lMinus_le_minus

/-- Centering at the DAI scale center gives symmetric curvature bounds. -/
theorem centered_at_scales (hUN : IsUN bounds E) (hAdmissible : Admissible bounds Λ) :
    IsUN hAdmissible.centeredBounds (UN.quadraticShift E Λ.center (stationaryPoint E)) :=
  hUN.centered Λ.center hAdmissible.center_mem_gap.1 hAdmissible.center_mem_gap.2 (stationaryPoint E)

end UN.IsUN
