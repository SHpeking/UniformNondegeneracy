module

public import UniformNondegeneracy.Analysis.Bregman

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Energy transformations

Linear tilts, relative energies, quadratic shifts, and scalar multiplication, with their gradients and Bregman differences.
-/

noncomputable section

namespace UN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Subtract a linear functional; `p` is its Riesz representative. -/
def linearTilt (E : H → ℝ) (p : H) : H → ℝ :=
  fun x => E x - ⟪p, x⟫

/-- The Bregman difference viewed as an energy in its first argument. -/
def relativeEnergy (E : H → ℝ) (x₂ : H) : H → ℝ :=
  fun x₁ => bregman E x₁ x₂

/-- Subtract a quadratic with curvature `c`, centered at `x₂`. -/
def quadraticShift (E : H → ℝ) (c : ℝ) (x₂ : H) : H → ℝ :=
  fun x₁ => E x₁ - c / 2 * ‖x₁ - x₂‖ ^ 2

variable {E : H → ℝ}

local notation "g" => gradient E

theorem hasGradientAt_neg {x : H} (hE : DifferentiableAt ℝ E x) :
    HasGradientAt (fun x₁ => -E x₁) (-g x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hE.hasGradientAt.hasFDerivAt.neg using 1
  ext v
  simp [InnerProductSpace.toDual]

theorem gradient_neg (hE : Differentiable ℝ E) :
    gradient (fun x => -E x) = fun x => -g x :=
  gradient_eq fun x => hasGradientAt_neg (hE x)

theorem hasGradientAt_linearTilt {x : H} (hE : DifferentiableAt ℝ E x) (p : H) :
    HasGradientAt (UN.linearTilt E p) (g x - p) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  unfold UN.linearTilt
  convert hE.hasGradientAt.hasFDerivAt.sub ((innerSL ℝ p).hasFDerivAt) using 1 <;>
    ext v <;> simp [InnerProductSpace.toDual]

theorem gradient_linearTilt (hE : Differentiable ℝ E) (p : H) :
    gradient (UN.linearTilt E p) = fun x => g x - p :=
  gradient_eq fun x => hasGradientAt_linearTilt (hE x) p

theorem hasGradientAt_relativeEnergy {x₁ : H} (hE : DifferentiableAt ℝ E x₁) (x₂ : H) :
    HasGradientAt (UN.relativeEnergy E x₂) (g x₁ - g x₂) x₁ := by
  rw [hasGradientAt_iff_hasFDerivAt]
  unfold UN.relativeEnergy
  have hi := ((innerSL ℝ (g x₂)).hasFDerivAt.comp x₁ ((hasFDerivAt_id x₁).sub_const x₂))
  convert (hE.hasGradientAt.hasFDerivAt.sub_const (E x₂)).sub hi using 1 <;>
    ext v <;> simp [bregman, InnerProductSpace.toDual]

theorem gradient_relativeEnergy (hE : Differentiable ℝ E) (x₂ : H) :
    gradient (UN.relativeEnergy E x₂) = fun x₁ => g x₁ - g x₂ :=
  gradient_eq fun x₁ => hasGradientAt_relativeEnergy (hE x₁) x₂

theorem hasGradientAt_quadraticShift {x₁ : H} (hE : DifferentiableAt ℝ E x₁) (c : ℝ) (x₂ : H) :
    HasGradientAt (UN.quadraticShift E c x₂) (g x₁ - c • (x₁ - x₂)) x₁ := by
  rw [hasGradientAt_iff_hasFDerivAt]
  unfold UN.quadraticShift
  convert hE.hasGradientAt.hasFDerivAt.sub (hasGradientAt_quadratic c x₂ x₁).hasFDerivAt using 1
  ext v
  simp [InnerProductSpace.toDual]

theorem gradient_quadraticShift (hE : Differentiable ℝ E) (c : ℝ) (x₂ : H) :
    gradient (UN.quadraticShift E c x₂) = fun x₁ => g x₁ - c • (x₁ - x₂) :=
  gradient_eq fun x₁ => hasGradientAt_quadraticShift (hE x₁) c x₂

theorem hasGradientAt_const_mul {x : H} (hE : DifferentiableAt ℝ E x) (a : ℝ) :
    HasGradientAt (fun x => a * E x) (a • g x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hE.hasGradientAt.hasFDerivAt.const_mul a using 1
  ext v
  simp [InnerProductSpace.toDual]

theorem gradient_const_mul (hE : Differentiable ℝ E) (a : ℝ) :
    gradient (fun x => a * E x) = fun x => a • g x :=
  gradient_eq fun x => hasGradientAt_const_mul (hE x) a

theorem bregman_neg (hE : Differentiable ℝ E) (x₁ x₂ : H) :
    bregman (fun x => -E x) x₁ x₂ = -bregman E x₁ x₂ := by
  simp only [bregman, gradient_neg hE, inner_neg_left]
  ring

theorem bregman_linearTilt (hE : Differentiable ℝ E) (p : H) (x₁ x₂ : H) :
    bregman (UN.linearTilt E p) x₁ x₂ = bregman E x₁ x₂ := by
  simp only [bregman, gradient_linearTilt hE, linearTilt, inner_sub_left, inner_sub_right]
  ring

theorem bregman_relativeEnergy (hE : Differentiable ℝ E) (x₀ x₁ x₂ : H) :
    bregman (UN.relativeEnergy E x₀) x₁ x₂ = bregman E x₁ x₂ := by
  simp only [bregman, gradient_relativeEnergy hE, relativeEnergy, inner_sub_left, inner_sub_right]
  ring

/-- A quadratic shift subtracts the same quadratic from every Bregman difference. -/
theorem bregman_quadraticShift (hE : Differentiable ℝ E) (c : ℝ) (x₀ x₁ x₂ : H) :
    bregman (UN.quadraticShift E c x₀) x₁ x₂ = bregman E x₁ x₂ - c / 2 * ‖x₁ - x₂‖ ^ 2 := by
  simp only [bregman, gradient_quadraticShift hE, quadraticShift, inner_sub_left,
    real_inner_smul_left, norm_sub_sq_real, inner_sub_right, real_inner_self_eq_norm_sq]
  simp only [real_inner_comm]
  ring

theorem bregman_const_mul (hE : Differentiable ℝ E) (a : ℝ) (x₁ x₂ : H) :
    bregman (fun x => a * E x) x₁ x₂ = a * bregman E x₁ x₂ := by
  simp only [bregman, gradient_const_mul hE, real_inner_smul_left]
  ring

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
@[simp] theorem quadraticShift_zero (E : H → ℝ) (x₀ : H) :
    quadraticShift E 0 x₀ = E := by
  funext x
  simp [quadraticShift]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
@[simp] theorem quadraticShift_quadraticShift (E : H → ℝ) (c₁ c₂ : ℝ) (x₀ : H) :
    quadraticShift (quadraticShift E c₁ x₀) c₂ x₀ = quadraticShift E (c₁ + c₂) x₀ := by
  funext x
  simp only [quadraticShift]
  ring

end UN
