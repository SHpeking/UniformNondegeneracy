# UniformNondegeneracy

A Lean library for the structural theory of uniform nondegeneracy (UN) on real Hilbert spaces and its applications to first-order optimization.

Uniform nondegeneracy provides a unifying framework for studying the geometry of energies and their optimization dynamics, revealing common structures across convex and nonconvex settings.

## Uniform nondegeneracy

Let $\mathcal{H}$ be a real Hilbert space with inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$, and let $E\in C^1(\mathcal{H};\mathbb{R})$ have gradient $g=\nabla E:\mathcal{H}\to\mathcal{H}$.

**Definition.** $E$ is [uniformly nondegenerate (UN)](UniformNondegeneracy/Core/Basic.lean) with curvature bound $\mathcal{S}=[-L_-,-\mu_-]\cup[\mu_+,L_+]$, where $L_-\ge\mu_->0$ and $L_+\ge\mu_+>0$, if, for every $x_1,x_2\in\mathcal{H}$, the differences $\Delta x=x_1-x_2$ and $\Delta g=g(x_1)-g(x_2)$ satisfy

$$
\langle\Delta g+L_-\Delta x,\Delta g-L_+\Delta x\rangle\le0\le\langle\Delta g+\mu_-\Delta x,\Delta g-\mu_+\Delta x\rangle.
$$

In particular, for $E\in C^2(\mathcal{H};\mathbb{R})$, this is equivalent to $\mathrm{spec}(\nabla^2 E(x))\subseteq\mathcal{S}$ for every $x\in\mathcal{H}$.

## Structural theory

Uniform nondegeneracy gives rise to a rich geometric structure, extending classical ideas from convex analysis and revealing new relations for nonconvex energies.

### Gradient geometry

For a UN energy $E$, the gradient $g$ is a **[global bi-Lipschitz homeomorphism](UniformNondegeneracy/Geometry/Basic.lean)**, giving a unique stationary point $x^\star=g^{-1}(0)$.

Writing $[c]_\pm=\max\lbrace\pm c,0\rbrace$ for $c\in\mathbb{R}$, the classical Polyak–Łojasiewicz (PL) inequality is generalized as

$$
\frac{1}{2}\|g(x)\|^2\ge\mu_+[E(x)-E(x^\star)]_++\mu_-[E(x)-E(x^\star)]_-,\quad\forall x\in\mathcal{H}.
$$

### Duality

The **[Legendre transform](UniformNondegeneracy/Geometry/Duality.lean)**

$$
E^\sharp(p)=\langle p,g^{-1}(p)\rangle-E(g^{-1}(p)),\quad p\in\mathcal{H},
$$

is UN with reciprocal curvature bound $\mathcal{S}^\sharp=[-\mu_-^{-1},-L_-^{-1}]\cup[L_+^{-1},\mu_+^{-1}]$, and satisfies

$$
\nabla E^\sharp=(\nabla E)^{-1},\quad E^{\sharp\sharp}=E.
$$

For a differentiable energy $f:\mathcal{H}\to\mathbb{R}$, denote its Bregman difference by $D_f(x_1,x_2)=f(x_1)-f(x_2)-\langle\nabla f(x_2),x_1-x_2\rangle$. Duality gives **Bregman reciprocity**:

$$
D_E(x_1,x_2)=D_{E^\sharp}(g(x_2),g(x_1)),\quad \forall x_1,x_2\in\mathcal{H}.
$$

### Two-sided envelopes

For $s\in(-L_-^{-1},L_+^{-1})$, we consider the **[two-sided envelope](UniformNondegeneracy/Envelopes/Basic.lean)** defined by

$$
M_s(x)=\sup_{\xi\in\mathcal{H}}\left\lbrace s\bigl(E(\xi)-E(x^\star)\bigr)-\frac{1}{2}\|\xi-x\|^2\right\rbrace,\quad x\in\mathcal{H}.
$$

The unique maximizer is $J_s(x)=(I-sg)^{-1}(x)$, and the derivatives recover the energy and gradient at this point:

$$
\partial_s M_s(x)=E(J_s(x))-E(x^\star),\quad\nabla_x M_s(x)=J_s(x)-x=s g(J_s(x)).
$$

Its proximal operator is given by $\mathrm{prox}_{M_s}=J_s^{-1}=I-sg$.

### Descent–ascent structure

For scales $\Lambda_\pm>0$, define the descent and ascent Bregman differences

$$
\Phi_\pm(x_1,x_2)=\frac{1}{2}\|x_1-x_2\|^2\mp\frac{1}{\Lambda_\pm} D_E(x_1,x_2),\quad x_1,x_2\in\mathcal{H}.
$$

The **[descent–ascent inequality (DAI)](UniformNondegeneracy/DAI/Basic.lean)** with weights $\rho_\pm\ge0$ is

$$
\rho_+\Phi_+(x,y)+\rho_-\Phi_-(x,z)\ge\langle\nabla_x\Phi_+(x,y),\nabla_x\Phi_-(x,z)\rangle,\quad \forall x,y,z\in\mathcal{H}.
$$

UN energies satisfy DAIs for suitable scales and weights. Conversely, under the balance condition $\frac{\rho_+}{\Lambda_+}=\frac{\rho_-}{\Lambda_-}$, [DAI yields two-sided secant bounds](UniformNondegeneracy/DAI/Secant.lean), and [two DAIs with suitable scales and weights](UniformNondegeneracy/DAI/ToUN.lean) recover UN.

## Alternating descent–ascent

UN energies admit a surprisingly simple algorithm: **alternating descent–ascent (ADA)**, which alternates full-gradient descent and ascent and converges globally to the unique stationary point $x^\star$ at a linear rate. Starting from any $x_0\in\mathcal{H}$ and either initial phase, ADA iterates as

```
if next_step == "descent":
    x_{t+1} = x_t - g(x_t) / Lambda_+
    next_step = "ascent"
else:
    x_{t+1} = x_t + g(x_t) / Lambda_-
    next_step = "descent"
```

For admissible choices of $\Lambda_\pm$, meaning that $\Lambda_+\ge L_+$, $\Lambda_-\ge L_-$, and $\Lambda_+-\Lambda_-\in(-\mu_-,\mu_+)$, define the effective condition number $\kappa$ by

$$
1-\frac{1}{\kappa}=\max_{\lambda\in\mathcal{S}}\left(1-\frac{\lambda}{\Lambda_+}\right)\left(1+\frac{\lambda}{\Lambda_-}\right).
$$

Then, for every $T\in\mathbb{N}$, the ADA iteration satisfies the [linear convergence bound](UniformNondegeneracy/Algorithms/ADA/Complexity.lean)

$$
\min_{0\le t\le T}\|g(x_t)\|\lesssim\|g(x_0)\|\cdot\exp(-\Theta(T/\kappa)).
$$

## Library structure

| Area | Responsibility |
| --- | --- |
| [Core](UniformNondegeneracy/Core) | Curvature bounds and the definition of UN |
| [Analysis](UniformNondegeneracy/Analysis) | General Taylor and Bregman estimates, gradient-step bounds, and residual decay |
| [Geometry](UniformNondegeneracy/Geometry) | Global gradient inversion, unique stationary points, transformations, duality, signed PL bounds, and refined secant inequalities |
| [Envelopes](UniformNondegeneracy/Envelopes) | Resolvents, two-sided envelopes, derivatives, and comparison inequalities |
| [DAI](UniformNondegeneracy/DAI) | Descent–ascent inequalities, their derivation from UN, and the converse secant bounds |
| [Algorithms/ADA](UniformNondegeneracy/Algorithms/ADA) | ADA iterations and explicit complexity bounds for the best-iterate gradient residual |
| [Examples](UniformNondegeneracy/Examples) | Scalar and diagonal quadratics, and strongly convex energies with Lipschitz gradients |

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

## References

- [First-Order Optimization under Uniform Nondegeneracy: Geometry, Computation, and Information](https://arxiv.org/abs/2609.06946)
- [Descent–Ascent Structure of Uniform Nondegeneracy](https://arxiv.org/abs/2610.06115)
