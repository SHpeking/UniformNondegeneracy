module

public import UniformNondegeneracy.Core.Parameters
public import UniformNondegeneracy.Core.Basic
public import UniformNondegeneracy.Analysis.Taylor
public import UniformNondegeneracy.Analysis.Bregman
public import UniformNondegeneracy.Analysis.PrefixMin
public import UniformNondegeneracy.Analysis.ResidualDecay
public import UniformNondegeneracy.Analysis.GradientSteps
public import UniformNondegeneracy.Geometry.GradientInverse
public import UniformNondegeneracy.Geometry.Basic
public import UniformNondegeneracy.Geometry.Transforms
public import UniformNondegeneracy.Geometry.Duality
public import UniformNondegeneracy.Envelopes.Basic
public import UniformNondegeneracy.Envelopes.Comparison
public import UniformNondegeneracy.DAI.Parameters
public import UniformNondegeneracy.DAI.Admissibility
public import UniformNondegeneracy.DAI.Weights
public import UniformNondegeneracy.DAI.Steps
public import UniformNondegeneracy.DAI.Reparameterization
public import UniformNondegeneracy.DAI.Basic
public import UniformNondegeneracy.DAI.EnvelopeComparison
public import UniformNondegeneracy.DAI.FromUN

@[expose] public section

/-!
# Uniform nondegeneracy: shared mathematical theory

This entry point intentionally imports no algorithm application. New results about UN geometry or its structural inequalities belong to the relevant theory modules. Applications have their own entry points under `Algorithms`.

Throughout the project, `H` is the real Hilbert space, `E : H → ℝ` is the energy, and `g : H → H` is its gradient. Generic two-point statements use `x₁ x₂`; the second argument of `bregman E g x₁ x₂` is the expansion point. Dual points use `p`, `p₁`, `p₂`. DAI uses `x y z`, with `y` the descent anchor and `z` the ascent anchor.

Envelope parameters use `s`, `s₁`, `s₂`, and trial points use `ξ`. Local notation `D`, `J`, and `M` abbreviates the Bregman difference, resolvent, and interior envelope for the fixed energy and gradient. `xStar` and `EStar` denote the stationary point and value; `Esharp` denotes the dual energy. Shifted functions use `Eshift`, `gshift`, and scalar energy gaps use `ΔE`.

The original asymmetric bounds are $\mu_+,\mu_-,L_+,L_-$. `Λ : DAI.Scales` contains the inverse step sizes, with $\tau_+=1/\Lambda_+$ and $\tau_-=1/\Lambda_-$. `ρ : DAI.Weights` contains the DAI weights. Effective inner bounds use `μEffPlus`, `μEffMinus` (or local notation `μEff₊`, `μEff₋`) to distinguish them from the original bounds. Generic gradient norm bounds use `μ`, `L`; the scalar curvature argument of a multiplier uses `σ`.

In ADA, `t`, `T` count cycles and `k`, `N` count individual updates. For a descent-first trajectory, $y_t=x_{2t}$ and $z_t=x_{2t+1}$. The scalar decay argument uses `r t` for residual norms and `P t` for the normalized potential. `Eref` is the reference energy in the algebraic Lyapunov interface; the UN certificate supplies the stationary value.
-/
