module

public import UniformNondegeneracy.Geometry.Basic

@[expose] public section

/-!
# Limits of uniformly nondegenerate energies

Pointwise convergence of energies and gradients preserves common UN bounds.
-/

open Filter Topology
open scoped RealInnerProductSpace

namespace UN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {ι : Type*} {l : Filter ι} [l.NeBot]
variable {bounds : CurvatureBounds} {Eᵢ : ι → H → ℝ} {E : H → ℝ} {g : H → H}

/-- Common UN bounds identify a pointwise limit of gradients as the gradient of the limiting energy. -/
theorem hasGradientAt_of_pointwise_limit
    (hUN : ∀ᶠ i in l, IsUN bounds (Eᵢ i))
    (hE : ∀ x, Tendsto (fun i => Eᵢ i x) l (𝓝 (E x)))
    (hg : ∀ x, Tendsto (fun i => gradient (Eᵢ i) x) l (𝓝 (g x))) :
    ∀ x, HasGradientAt E (g x) x := by
  intro x
  have hRemainder (y : H) :
      Tendsto (fun i => bregman (Eᵢ i) y x) l (𝓝 (E y - E x - ⟪g x, y - x⟫)) :=
    ((hE y).sub (hE x)).sub ((hg x).inner tendsto_const_nhds)
  apply hasGradientAt_of_quadratic_bounds
  · intro y
    exact ge_of_tendsto (hRemainder y) (hUN.mono fun i hi => hi.bregman_lower y x)
  · intro y
    exact le_of_tendsto (hRemainder y) (hUN.mono fun i hi => hi.bregman_upper y x)

/-- Pointwise limits of energies and gradients preserve common UN bounds. -/
theorem isUN_of_pointwise_limit
    (hUN : ∀ᶠ i in l, IsUN bounds (Eᵢ i))
    (hE : ∀ x, Tendsto (fun i => Eᵢ i x) l (𝓝 (E x)))
    (hg : ∀ x, Tendsto (fun i => gradient (Eᵢ i) x) l (𝓝 (g x))) :
    IsUN bounds E := by
  apply IsUN.of_hasGradient (hasGradientAt_of_pointwise_limit hUN hE hg)
  · intro x₁ x₂
    have hΔ := (hg x₁).sub (hg x₂)
    exact ge_of_tendsto ((hΔ.add tendsto_const_nhds).inner (hΔ.sub tendsto_const_nhds))
      (hUN.mono fun i hi => hi.inner_secant x₁ x₂)
  · intro x₁ x₂
    have hΔ := (hg x₁).sub (hg x₂)
    exact le_of_tendsto ((hΔ.add tendsto_const_nhds).inner (hΔ.sub tendsto_const_nhds))
      (hUN.mono fun i hi => hi.outer_secant x₁ x₂)

end UN
