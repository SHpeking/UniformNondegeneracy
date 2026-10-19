module

public import UniformNondegeneracy.Geometry.Basic

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Transformations preserving UN
-/

noncomputable section

namespace UN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Subtract a linear functional; `p` is its Riesz representative. -/
def linearTilt (E : H → ℝ) (p : H) : H → ℝ :=
  fun x => E x - ⟪p, x⟫

/-- Energy relative to `x₂`; its gradient at `x` is `g x - g x₂`. -/
def relativeEnergy (E : H → ℝ) (g : H → H) (x₂ : H) : H → ℝ :=
  fun x₁ => bregman E g x₁ x₂

/-- Subtract a quadratic with curvature `c`, centered at `x₂`. -/
def quadraticShift (E : H → ℝ) (c : ℝ) (x₂ : H) : H → ℝ :=
  fun x₁ => E x₁ - c / 2 * ‖x₁ - x₂‖ ^ 2

namespace IsUN

variable {bounds : CurvatureBounds} {E : H → ℝ} {g : H → H}

local notation "μ₊" => bounds.muPlus
local notation "μ₋" => bounds.muMinus
local notation "L₊" => bounds.lPlus
local notation "L₋" => bounds.lMinus

theorem neg (hUN : IsUN bounds E g) :
    IsUN bounds.swap (fun x₁ => -E x₁) (fun x₁ => -g x₁) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x₁
    rw [hasGradientAt_iff_hasFDerivAt]
    convert (hUN.has_gradient x₁).hasFDerivAt.neg using 1;
      ext v; simp [InnerProductSpace.toDual]
  · intro x₁ x₂
    dsimp [CurvatureBounds.swap]
    rw [show -g x₁ - -g x₂ + μ₊ • (x₁ - x₂) = -(g x₁ - g x₂ - μ₊ • (x₁ - x₂)) by module,
      show -g x₁ - -g x₂ - μ₋ • (x₁ - x₂) = -(g x₁ - g x₂ + μ₋ • (x₁ - x₂)) by module]
    simpa only [inner_neg_neg, real_inner_comm] using hUN.inner_secant x₁ x₂
  · intro x₁ x₂
    dsimp [CurvatureBounds.swap]
    rw [show -g x₁ - -g x₂ + L₊ • (x₁ - x₂) = -(g x₁ - g x₂ - L₊ • (x₁ - x₂)) by module,
      show -g x₁ - -g x₂ - L₋ • (x₁ - x₂) = -(g x₁ - g x₂ + L₋ • (x₁ - x₂)) by module]
    simpa only [inner_neg_neg, real_inner_comm] using hUN.outer_secant x₁ x₂

theorem linearTilt (hUN : IsUN bounds E g) (p : H) :
    IsUN bounds (UN.linearTilt E p) (fun x₁ => g x₁ - p) := by
  unfold UN.linearTilt
  refine ⟨?_, ?_, ?_⟩
  · intro x₁
    rw [hasGradientAt_iff_hasFDerivAt]
    convert (hUN.has_gradient x₁).hasFDerivAt.sub ((innerSL ℝ p).hasFDerivAt) using 1 <;>
      ext v <;> simp [InnerProductSpace.toDual]
  · intro x₁ x₂
    simpa only [sub_sub_sub_cancel_right] using hUN.inner_secant x₁ x₂
  · intro x₁ x₂
    simpa only [sub_sub_sub_cancel_right] using hUN.outer_secant x₁ x₂

theorem relativeEnergy (hUN : IsUN bounds E g) (x₂ : H) :
    IsUN bounds (UN.relativeEnergy E g x₂) (fun x₁ => g x₁ - g x₂) := by
  unfold UN.relativeEnergy
  refine ⟨?_, ?_, ?_⟩
  · intro x₁
    rw [hasGradientAt_iff_hasFDerivAt]
    have hi := ((innerSL ℝ (g x₂)).hasFDerivAt.comp x₁ ((hasFDerivAt_id x₁).sub_const x₂))
    convert ((hUN.has_gradient x₁).hasFDerivAt.sub_const (E x₂)).sub hi using 1 <;>
      ext v <;> simp [bregman, InnerProductSpace.toDual]
  · intro x₁ other
    simpa only [sub_sub_sub_cancel_right] using hUN.inner_secant x₁ other
  · intro x₁ other
    simpa only [sub_sub_sub_cancel_right] using hUN.outer_secant x₁ other

theorem stationaryPoint_relativeEnergy (hUN : IsUN bounds E g) (x₂ : H) :
    stationaryPoint (fun x₁ => g x₁ - g x₂) = x₂ := by
  exact ((hUN.relativeEnergy x₂).gradient_eq_zero_iff x₂).mp (sub_self _) |>.symm

theorem stationaryValue_relativeEnergy (hUN : IsUN bounds E g) (x₂ : H) :
    stationaryValue (UN.relativeEnergy E g x₂) (fun x₁ => g x₁ - g x₂) = 0 := by
  simp [stationaryValue, hUN.stationaryPoint_relativeEnergy, UN.relativeEnergy, bregman_self]

/-- Subtracting a quadratic with curvature in the inner gap preserves UN. -/
theorem quadraticShift (hUN : IsUN bounds E g) (c : ℝ)
    (hLower : -μ₋ < c) (hUpper : c < μ₊)
    (x₂ : H) :
    IsUN (bounds.shift c hLower hUpper) (UN.quadraticShift E c x₂) (fun x₁ => g x₁ - c • (x₁ - x₂)) := by
  unfold UN.quadraticShift
  refine ⟨?_, ?_, ?_⟩
  · intro x₁
    rw [hasGradientAt_iff_hasFDerivAt]
    convert (hUN.has_gradient x₁).hasFDerivAt.sub
      (hasGradientAt_quadratic c x₂ x₁).hasFDerivAt using 1;
      ext v; simp [InnerProductSpace.toDual]
  · intro x₁ other
    convert hUN.inner_secant x₁ other using 1;
      dsimp [CurvatureBounds.shift]; congr 1 <;> module
  · intro x₁ other
    convert hUN.outer_secant x₁ other using 1;
      dsimp [CurvatureBounds.shift]; congr 1 <;> module

end IsUN
end UN
