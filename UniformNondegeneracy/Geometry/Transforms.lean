module

public import UniformNondegeneracy.Analysis.EnergyTransforms
public import UniformNondegeneracy.Geometry.Basic

@[expose] public section

open scoped RealInnerProductSpace

/-!
# Transformations preserving UN
-/

noncomputable section

namespace UN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

variable {E : H → ℝ}

local notation "g" => gradient E

namespace IsUN

variable {bounds : CurvatureBounds}

local notation "μ₊" => bounds.muPlus
local notation "μ₋" => bounds.muMinus
local notation "L₊" => bounds.lPlus
local notation "L₋" => bounds.lMinus

theorem neg (hUN : IsUN bounds E) :
    IsUN bounds.swap (fun x => -E x) := by
  apply IsUN.of_hasGradient (fun x => hasGradientAt_neg (hUN.differentiable x))
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

theorem linearTilt (hUN : IsUN bounds E) (p : H) :
    IsUN bounds (UN.linearTilt E p) := by
  apply IsUN.of_hasGradient (fun x => hasGradientAt_linearTilt (hUN.differentiable x) p)
  · intro x₁ x₂
    simpa only [sub_sub_sub_cancel_right] using hUN.inner_secant x₁ x₂
  · intro x₁ x₂
    simpa only [sub_sub_sub_cancel_right] using hUN.outer_secant x₁ x₂

theorem relativeEnergy (hUN : IsUN bounds E) (x₂ : H) :
    IsUN bounds (UN.relativeEnergy E x₂) := by
  apply IsUN.of_hasGradient (fun x₁ => hasGradientAt_relativeEnergy (hUN.differentiable x₁) x₂)
  · intro x₁ other
    simpa only [sub_sub_sub_cancel_right] using hUN.inner_secant x₁ other
  · intro x₁ other
    simpa only [sub_sub_sub_cancel_right] using hUN.outer_secant x₁ other

theorem stationaryPoint_relativeEnergy (hUN : IsUN bounds E) (x₂ : H) :
    stationaryPoint (UN.relativeEnergy E x₂) = x₂ := by
  have h := (hUN.relativeEnergy x₂).gradient_eq_zero_iff x₂
  rw [gradient_relativeEnergy hUN.differentiable] at h
  exact (h.mp (sub_self _)).symm

theorem stationaryValue_relativeEnergy (hUN : IsUN bounds E) (x₂ : H) :
    stationaryValue (UN.relativeEnergy E x₂) = 0 := by
  simp [stationaryValue, hUN.stationaryPoint_relativeEnergy, UN.relativeEnergy, bregman_self]

/-- Subtracting a quadratic with curvature in the inner gap preserves UN. -/
theorem quadraticShift (hUN : IsUN bounds E) (c : ℝ)
    (hLower : -μ₋ < c) (hUpper : c < μ₊) (x₂ : H) :
    IsUN (bounds.shift c hLower hUpper) (UN.quadraticShift E c x₂) := by
  apply IsUN.of_hasGradient (fun x₁ => hasGradientAt_quadraticShift (hUN.differentiable x₁) c x₂)
  · intro x₁ other
    convert hUN.inner_secant x₁ other using 1;
      dsimp [CurvatureBounds.shift]; congr 1 <;> module
  · intro x₁ other
    convert hUN.outer_secant x₁ other using 1;
      dsimp [CurvatureBounds.shift]; congr 1 <;> module

end IsUN
end UN
