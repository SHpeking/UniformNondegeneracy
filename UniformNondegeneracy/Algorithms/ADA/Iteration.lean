module

public import UniformNondegeneracy.DAI.Steps
public import UniformNondegeneracy.Analysis.PrefixMin

@[expose] public section

/-!
# Alternating descent–ascent trajectories

`trajectory` counts individual gradient updates; `cycleStart` and `cycleMiddle` count descent–ascent cycles. The initial phase may be descent or ascent.
-/

noncomputable section

namespace UN

open DAI

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

namespace ADA

inductive Phase where
  | descent
  | ascent
  deriving DecidableEq, Repr

def Phase.flip : Phase → Phase
  | .descent => .ascent
  | .ascent => .descent

@[simp] theorem Phase.flip_flip (phase : Phase) : phase.flip.flip = phase := by
  cases phase <;> rfl

/-- Phase of the update taking iterate `k` to iterate `k + 1`. -/
def phaseAt (firstPhase : Phase) (k : ℕ) : Phase :=
  if k % 2 = 0 then firstPhase else firstPhase.flip

@[simp] theorem phaseAt_zero (firstPhase : Phase) :
    phaseAt firstPhase 0 = firstPhase := by
  simp [phaseAt]

theorem phaseAt_succ (firstPhase : Phase) (k : ℕ) :
    phaseAt firstPhase (k + 1) = (phaseAt firstPhase k).flip := by
  have hmod := Nat.mod_lt k (by omega : 0 < 2)
  by_cases he : k % 2 = 0
  · have ho : (k + 1) % 2 ≠ 0 := by omega
    simp [phaseAt, he, ho]
  · have ho : (k + 1) % 2 = 0 := by omega
    simp [phaseAt, he, ho]

theorem phaseAt_even (firstPhase : Phase) (t : ℕ) :
    phaseAt firstPhase (2 * t) = firstPhase := by
  simp [phaseAt]

theorem phaseAt_odd (firstPhase : Phase) (t : ℕ) :
    phaseAt firstPhase (2 * t + 1) = firstPhase.flip := by
  simp [phaseAt]

def step (g : H → H) (Λ : Scales) : Phase → H → H
  | .descent => descentStep g Λ
  | .ascent => ascentStep g Λ

/-- ADA iterates from index zero, with the chosen initial phase. -/
def trajectory (g : H → H) (Λ : Scales)
    (firstPhase : Phase) (x₀ : H) : ℕ → H
  | 0 => x₀
  | k + 1 => step g Λ (phaseAt firstPhase k) (trajectory g Λ firstPhase x₀ k)

@[simp] theorem trajectory_zero (g : H → H) (Λ : Scales)
    (firstPhase : Phase) (x₀ : H) :
    trajectory g Λ firstPhase x₀ 0 = x₀ := rfl

@[simp] theorem trajectory_succ (g : H → H) (Λ : Scales)
    (firstPhase : Phase) (x₀ : H) (k : ℕ) :
    trajectory g Λ firstPhase x₀ (k + 1) = step g Λ (phaseAt firstPhase k) (trajectory g Λ firstPhase x₀ k) := rfl

/-- A trajectory tail starts from the corresponding point and phase. -/
theorem trajectory_tail (g : H → H) (Λ : Scales)
    (firstPhase : Phase) (x₀ : H) (k₀ k : ℕ) :
    trajectory g Λ (phaseAt firstPhase k₀) (trajectory g Λ firstPhase x₀ k₀) k = trajectory g Λ firstPhase x₀ (k₀ + k) := by
  have hphase : ∀ i, phaseAt (phaseAt firstPhase k₀) i = phaseAt firstPhase (k₀ + i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [← Nat.add_assoc, phaseAt_succ, phaseAt_succ, ih]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [trajectory_succ, ih, hphase, ← Nat.add_assoc, trajectory_succ]

theorem trajectory_of_gradient_eq_zero (g : H → H) (Λ : Scales)
    (firstPhase : Phase) (x₀ : H) (hStationary : g x₀ = 0)
    (k : ℕ) :
    trajectory g Λ firstPhase x₀ k = x₀ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [trajectory_succ, ih]
    cases phaseAt firstPhase k <;> simp [step, descentStep, ascentStep, gradientStep, hStationary]

/-- One descent step followed by one ascent step. -/
def descentAscentCycle (g : H → H) (Λ : Scales) (x : H) : H :=
  ascentStep g Λ (descentStep g Λ x)

/-- Point before descent in cycle `t`: $y_t$. -/
def cycleStart (g : H → H) (Λ : Scales) (x₀ : H) : ℕ → H
  | 0 => x₀
  | t + 1 => descentAscentCycle g Λ (cycleStart g Λ x₀ t)

/-- Point after descent and before ascent in cycle `t`: $z_t$. -/
def cycleMiddle (g : H → H) (Λ : Scales) (x₀ : H) (t : ℕ) : H :=
  descentStep g Λ (cycleStart g Λ x₀ t)

@[simp] theorem cycleStart_zero (g : H → H) (Λ : Scales) (x₀ : H) :
    cycleStart g Λ x₀ 0 = x₀ := rfl

@[simp] theorem cycleStart_succ (g : H → H) (Λ : Scales) (x₀ : H) (t : ℕ) :
    cycleStart g Λ x₀ (t + 1) = ascentStep g Λ (cycleMiddle g Λ x₀ t) := rfl

theorem trajectory_descent_even (g : H → H) (Λ : Scales) (x₀ : H) (t : ℕ) :
    trajectory g Λ .descent x₀ (2 * t) = cycleStart g Λ x₀ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [show 2 * (t + 1) = (2 * t + 1) + 1 by omega]
    rw [trajectory_succ, phaseAt_odd, trajectory_succ, phaseAt_even, ih]
    rfl

theorem trajectory_descent_odd (g : H → H) (Λ : Scales) (x₀ : H) (t : ℕ) :
    trajectory g Λ .descent x₀ (2 * t + 1) = cycleMiddle g Λ x₀ t := by
  rw [trajectory_succ, phaseAt_even, trajectory_descent_even]
  rfl

/-- Negating the gradient and exchanging scales exchanges the two phases. -/
theorem step_neg_swap (g : H → H) (Λ : Scales) (phase : Phase) (x : H) :
    step (fun x => -g x) Λ.swap phase.flip x = step g Λ phase x := by
  cases phase <;> simp [step, Phase.flip, descentStep, ascentStep, gradientStep,
    Scales.swap, Scales.tauPlus, Scales.tauMinus]

theorem trajectory_neg_swap (g : H → H) (Λ : Scales)
    (firstPhase : Phase) (x₀ : H) (k : ℕ) :
    trajectory (fun x => -g x) Λ.swap firstPhase.flip x₀ k = trajectory g Λ firstPhase x₀ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [trajectory_succ, trajectory_succ, ih]
    have hp : phaseAt firstPhase.flip k = (phaseAt firstPhase k).flip := by
      unfold phaseAt
      split <;> rfl
    rw [hp, step_neg_swap]

/-- Minimum gradient norm over iterates `0, …, N`. -/
def bestResidual (g : H → H) (Λ : Scales)
    (firstPhase : Phase) (x₀ : H) (N : ℕ) : ℝ :=
  prefixMin (fun k => ‖g (trajectory g Λ firstPhase x₀ k)‖) N

@[simp] theorem bestResidual_zero (g : H → H) (Λ : Scales)
    (firstPhase : Phase) (x₀ : H) :
    bestResidual g Λ firstPhase x₀ 0 = ‖g x₀‖ := rfl

theorem bestResidual_nonneg (g : H → H) (Λ : Scales)
    (firstPhase : Phase) (x₀ : H) (N : ℕ) :
    0 ≤ bestResidual g Λ firstPhase x₀ N := by
  exact prefixMin_nonneg _ (fun _ => norm_nonneg _) N

theorem bestResidual_attained (g : H → H) (Λ : Scales)
    (firstPhase : Phase) (x₀ : H) (N : ℕ) :
    ∃ k ≤ N, bestResidual g Λ firstPhase x₀ N = ‖g (trajectory g Λ firstPhase x₀ k)‖ := by
  exact prefixMin_attained _ N

theorem bestResidual_le_initial (g : H → H) (Λ : Scales)
    (firstPhase : Phase) (x₀ : H) (N : ℕ) :
    bestResidual g Λ firstPhase x₀ N ≤ ‖g x₀‖ := by
  exact prefixMin_le_at _ (Nat.zero_le N)

theorem bestResidual_neg_swap (g : H → H) (Λ : Scales)
    (firstPhase : Phase) (x₀ : H) (N : ℕ) :
    bestResidual (fun x => -g x) Λ.swap firstPhase.flip x₀ N = bestResidual g Λ firstPhase x₀ N := by
  unfold bestResidual
  congr 1
  funext k
  rw [trajectory_neg_swap, norm_neg]

end ADA
end UN
