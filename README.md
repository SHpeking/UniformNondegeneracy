# UniformNondegeneracy

A Lean library for uniform nondegeneracy (UN) on real Hilbert spaces, including applications to first-order optimization. Its purpose is to develop the structural theory of UN and support further characterizations, examples, analytic constructions, and algorithms.

## Mathematical foundation

Let $H$ be a real Hilbert space and $E:H\to\mathbb R$ a continuously differentiable energy with gradient $g=\nabla E$. A curvature certificate consists of positive magnitudes $\mu_+,\mu_-,L_+,L_-$ with $\mu_+\le L_+$ and $\mu_-\le L_-$. For every $x_1,x_2\in H$, write $\Delta x=x_1-x_2$ and $\Delta g=g(x_1)-g(x_2)$. The predicate `UN.IsUN bounds E g` asserts the gradient identity and the two secant inequalities:

$$
\langle\Delta g+L_-\Delta x,\Delta g-L_+\Delta x\rangle\le0\le\langle\Delta g+\mu_-\Delta x,\Delta g-\mu_+\Delta x\rangle
$$

The certificate bounds two curvature bands; it does not require that both curvature signs occur. Positive definite, negative definite, and indefinite examples are included. Surjectivity, the inverse gradient, and existence and uniqueness of a stationary point are proved consequences.

## Project structure and current results

| Area | Responsibility |
| --- | --- |
| [Core](UniformNondegeneracy/Core) | Curvature bounds and the definition of UN |
| [Analysis](UniformNondegeneracy/Analysis) | General Taylor and Bregman estimates, gradient-step bounds, and residual decay |
| [Geometry](UniformNondegeneracy/Geometry) | Global gradient inversion, unique stationary points, transformations, duality, signed PL bounds, and refined secant inequalities |
| [Envelopes](UniformNondegeneracy/Envelopes) | Interior resolvents and envelopes, their derivatives, and comparison inequalities |
| [DAI](UniformNondegeneracy/DAI) | Descent–ascent inequalities and their derivation from UN |
| [Algorithms/ADA](UniformNondegeneracy/Algorithms/ADA) | ADA iterations and explicit complexity bounds for the best-iterate gradient residual |
| [Examples](UniformNondegeneracy/Examples) | Positive definite, negative definite, and indefinite quadratic energies |

`Core` and `Geometry` establish the foundations. `Envelopes` and `DAI` develop further mathematical structure, while `Algorithms` use the shared theory. General analytic tools are collected in `Analysis`.

## Building and imports

Lean and mathlib are pinned to `v4.35.0`. With the toolchain and dependencies installed, run:

```sh
lake build
```

Import the shared mathematical theory with:

```lean
import UniformNondegeneracy
```

Use `import UniformNondegeneracy.Algorithms.ADA` for ADA, or `import UniformNondegeneracy.All` for the entire library, including examples. Individual modules can also be imported directly.

All current theorems are proved without `sorry`, `admit`, or project-specific axioms.

## References

- [First-Order Optimization under Uniform Nondegeneracy: Geometry, Computation, and Information](https://arxiv.org/abs/2609.06946)
- [Descent–Ascent Structure of Uniform Nondegeneracy](https://arxiv.org/abs/2610.06115)
