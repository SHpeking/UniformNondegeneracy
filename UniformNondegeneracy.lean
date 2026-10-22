module

public import UniformNondegeneracy.Core.Parameters
public import UniformNondegeneracy.Core.Basic
public import UniformNondegeneracy.Analysis.Taylor
public import UniformNondegeneracy.Analysis.Bregman
public import UniformNondegeneracy.Analysis.EnergyTransforms
public import UniformNondegeneracy.Analysis.GradientBounds
public import UniformNondegeneracy.Analysis.StrongConvexity
public import UniformNondegeneracy.Analysis.PrefixMin
public import UniformNondegeneracy.Analysis.ResidualDecay
public import UniformNondegeneracy.Analysis.GradientSteps
public import UniformNondegeneracy.Analysis.GlobalInverse
public import UniformNondegeneracy.Analysis.SelfAdjointSpectrum
public import UniformNondegeneracy.Geometry.GradientInverse
public import UniformNondegeneracy.Geometry.InverseEnergy
public import UniformNondegeneracy.Geometry.Basic
public import UniformNondegeneracy.Geometry.Limits
public import UniformNondegeneracy.Geometry.Spectral
public import UniformNondegeneracy.Geometry.Transforms
public import UniformNondegeneracy.Geometry.Reparameterization
public import UniformNondegeneracy.Geometry.Duality
public import UniformNondegeneracy.Envelopes.Basic
public import UniformNondegeneracy.Envelopes.Comparison
public import UniformNondegeneracy.DAI.Parameters
public import UniformNondegeneracy.DAI.Admissibility
public import UniformNondegeneracy.DAI.Weights
public import UniformNondegeneracy.DAI.Steps
public import UniformNondegeneracy.DAI.Reparameterization
public import UniformNondegeneracy.DAI.Basic
public import UniformNondegeneracy.DAI.Transforms
public import UniformNondegeneracy.DAI.Normalization
public import UniformNondegeneracy.DAI.Spectral
public import UniformNondegeneracy.DAI.Secant
public import UniformNondegeneracy.DAI.EnvelopeComparison
public import UniformNondegeneracy.DAI.FromUN
public import UniformNondegeneracy.DAI.ToUN

@[expose] public section

/-!
# Uniform nondegeneracy

Structural theory on real Hilbert spaces: spectral characterization, gradient inversion, duality, envelopes, and descent–ascent inequalities.

`E` denotes the energy and `g` its gradient. Local notation `D`, `J`, and `M` denotes the Bregman difference, resolvent, and envelope. `xStar` and `EStar` denote the stationary point and value, and `Esharp` denotes the Legendre transform.
-/
