module

public import UniformNondegeneracy.Algorithms.ADA.Lyapunov
public import UniformNondegeneracy.DAI.FromUN

@[expose] public section

/-!
# Bridge from UN geometry to the algebraic ADA certificate
-/

noncomputable section

namespace UN.ADA

open DAI

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {bounds : CurvatureBounds} {E : H → ℝ} {g : H → H} {Λ : Scales}

/-- Use effective UN bounds for signed PL, original outer bounds for Bregman control, and the canonical-weight DAI theorem. -/
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

/-- Public bridge, independent of the choice of first phase of the full run. The order restriction belongs only to this canonical-cycle analysis. -/
theorem hasLyapunovBounds_of_isUN (hUN : IsUN bounds E g)
    (hAdmissible : Admissible bounds Λ)
    (hOrder : Λ.tauMinus ≤ Λ.tauPlus) (x₀ : H) :
    HasLyapunovBounds (3 * kappa bounds Λ + 2)
      (fun index => ‖g (cycleStart g Λ x₀ index)‖)
      (fun index => normalizedEnergy E g Λ (kappa bounds Λ) (stationaryValue E g) (cycleStart g Λ x₀ index)) := by
  exact (lyapunovInputs_of_isUN hUN hAdmissible).hasLyapunovBounds hOrder x₀

end UN.ADA
