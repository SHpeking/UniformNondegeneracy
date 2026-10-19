module

public import UniformNondegeneracy.Algorithms.ADA.Lyapunov
public import UniformNondegeneracy.DAI.FromUN

@[expose] public section

/-!
# Lyapunov bounds from UN
-/

noncomputable section

namespace UN.ADA

open DAI

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {bounds : CurvatureBounds} {E : H → ℝ} {g : H → H} {Λ : Scales}

/-- UN supplies the Bregman, signed PL, and DAI bounds for the corrected energy. -/
theorem lyapunovInputs_of_isUN (hUN : IsUN bounds E g)
    (hAdmissible : Admissible bounds Λ) :
    LyapunovInputs bounds E g Λ hAdmissible (stationaryValue E g) := by
  refine
    { bregman_bounds := hUN.hasBregmanBounds.mono hAdmissible.lPlus_le_plus hAdmissible.lMinus_le_minus
      signed_pl_lower := ?_
      signed_pl_upper := ?_
      dai := hUN.hasDAI_canonicalWeights hAdmissible }
  · intro x
    exact ((hUN.effectiveBounds hAdmissible).signedPL x).1
  · intro x
    exact ((hUN.effectiveBounds hAdmissible).signedPL x).2

/-- Lyapunov bounds for descent–ascent cycles under UN. -/
theorem hasLyapunovBounds_of_isUN (hUN : IsUN bounds E g)
    (hAdmissible : Admissible bounds Λ)
    (hOrder : Λ.tauMinus ≤ Λ.tauPlus) (x₀ : H) :
    HasLyapunovBounds (3 * kappa bounds Λ + 2)
      (fun t => ‖g (cycleStart g Λ x₀ t)‖)
      (fun t => normalizedEnergy E g Λ (kappa bounds Λ) (stationaryValue E g) (cycleStart g Λ x₀ t)) := by
  exact (lyapunovInputs_of_isUN hUN hAdmissible).hasLyapunovBounds hOrder x₀

end UN.ADA
