module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.ExtendFrom
public import Mathlib.Tactic

@[expose] public section

/-!
# Global inversion from uniform inverse-derivative bounds

Local inverses continue along line segments when their derivatives have a uniform norm bound. Completeness gives continuation at finite endpoints, and uniqueness of lifts gives a global inverse.
-/

noncomputable section

open Set Filter Topology
open scoped unitInterval

namespace UN.GlobalInverse

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {F : X → Y} {A : X → X ≃L[ℝ] Y}

private theorem isLocalHomeomorph (hF : ∀ x, HasStrictFDerivAt F (A x : X →L[ℝ] Y) x) :
    IsLocalHomeomorph F := by
  intro x
  exact ⟨(hF x).toOpenPartialHomeomorph F, (hF x).mem_toOpenPartialHomeomorph_source, rfl⟩

private theorem lift_hasDerivWithinAt
    (hF : ∀ x, HasStrictFDerivAt F (A x : X →L[ℝ] Y) x)
    {γ : ℝ → X} {S : Set ℝ} {p v : Y}
    (hγ : ContinuousOn γ S) (hLift : ∀ s ∈ S, F (γ s) = p + s • v)
    {s : ℝ} (hs : s ∈ S) :
    HasDerivWithinAt γ ((A (γ s)).symm v) S s := by
  have hInv := (hF (γ s)).to_localInverse.hasFDerivAt
  rw [hLift s hs] at hInv
  have hLine : HasDerivAt (fun t : ℝ => p + t • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add p
  apply (hInv.comp_hasDerivWithinAt s hLine.hasDerivWithinAt).congr_of_eventuallyEq
  · have he := (hγ s hs).eventually (hF (γ s)).eventually_left_inverse
    filter_upwards [he, self_mem_nhdsWithin] with t ht htS
    simpa only [Function.comp_apply, hLift t htS] using ht.symm
  · simpa only [Function.comp_apply, ← hLift s hs] using (hF (γ s)).localInverse_apply_image.symm

private theorem lift_lipschitzOn
    (hF : ∀ x, HasStrictFDerivAt F (A x : X →L[ℝ] Y) x)
    {M : NNReal} (hBound : ∀ x, ‖(A x).symm.toContinuousLinearMap‖ ≤ M)
    {γ : ℝ → X} {T : ℝ} {p v : Y}
    (hγ : ContinuousOn γ (Icc 0 T)) (hLift : ∀ s ∈ Icc 0 T, F (γ s) = p + s • v) :
    LipschitzOnWith (M * ‖v‖₊) γ (Icc 0 T) := by
  apply (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun s hs => lift_hasDerivWithinAt hF hγ hLift hs)
  intro s hs
  have h := (A (γ s)).symm.toContinuousLinearMap.le_opNorm v
  exact_mod_cast h.trans (mul_le_mul_of_nonneg_right (hBound _) (norm_nonneg v))

omit [NormedSpace ℝ X] in
private theorem continuousOn_extendFrom_of_uniformContinuousOn
    {γ : ℝ → X} {S : Set ℝ} (hγ : UniformContinuousOn γ S) :
    ContinuousOn (extendFrom S γ) (closure S) := by
  apply continuousOn_extendFrom Subset.rfl
  intro s hs
  have := mem_closure_iff_nhdsWithin_neBot.mp hs
  apply cauchy_map_iff_exists_tendsto.mp
  exact (cauchy_nhds.mono nhdsWithin_le_nhds).map_of_le hγ inf_le_right

private structure SegmentLift (F : X → Y) (x₀ : X) (v : Y) (T : ℝ) where
  curve : ℝ → X
  continuous : ContinuousOn curve (Icc 0 T)
  initial : curve 0 = x₀
  maps : ∀ s ∈ Icc 0 T, F (curve s) = F x₀ + s • v

private def SegmentLift.restrict {x₀ : X} {v : Y} {T T₁ : ℝ}
    (γ : SegmentLift F x₀ v T) (hT : T₁ ≤ T) : SegmentLift F x₀ v T₁ where
  curve := γ.curve
  continuous := γ.continuous.mono (Icc_subset_Icc_right hT)
  initial := γ.initial
  maps s hs := γ.maps s (Icc_subset_Icc_right hT hs)

omit [NormedSpace ℝ X] [CompleteSpace X] in
private theorem SegmentLift.agree
    (hF : IsLocalHomeomorph F) {x₀ : X} {v : Y} {T T₁ : ℝ}
    (γ : SegmentLift F x₀ v T) (γ₁ : SegmentLift F x₀ v T₁)
    (hT : 0 ≤ T) (hTT₁ : T ≤ T₁) :
    EqOn γ.curve γ₁.curve (Icc 0 T) := by
  apply (T2Space.isSeparatedMap F).eqOn_of_comp_eqOn hF.isLocallyInjective isPreconnected_Icc
    γ.continuous (γ₁.continuous.mono (Icc_subset_Icc_right hTT₁))
  · intro s hs
    exact (γ.maps s hs).trans (γ₁.maps s (Icc_subset_Icc_right hTT₁ hs)).symm
  · exact ⟨le_rfl, hT⟩
  · exact γ.initial.trans γ₁.initial.symm

omit [NormedSpace ℝ X] [CompleteSpace X] in
private theorem SegmentLift.extend
    (hF : IsLocalHomeomorph F) {x₀ : X} {v : Y} {T : ℝ}
    (γ : SegmentLift F x₀ v T) (hT : 0 ≤ T) :
    ∃ T₁ > T, Nonempty (SegmentLift F x₀ v T₁) := by
  let e := hF.localInverseAt (γ.curve T)
  let line := fun s : ℝ => F x₀ + s • v
  have hLine : Continuous line := by fun_prop
  have hTarget : line T ∈ e.source := by
    dsimp only [line]
    rw [← γ.maps T ⟨hT, le_rfl⟩]
    exact hF.apply_self_mem_localInverseAt_source
  obtain ⟨ε, hε, hεBall⟩ := Metric.mem_nhds_iff.mp
    (hLine.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hTarget))
  let T₁ := T + ε / 2
  have hTT₁ : T < T₁ := by dsimp [T₁]; linarith
  have hRight (s : ℝ) (hs : s ∈ Icc T T₁) : line s ∈ e.source := by
    apply hεBall
    simp only [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
    dsimp [T₁] at hs
    linarith [hs.2]
  have hJoin : γ.curve T = e (line T) := by
    dsimp only [line]
    rw [← γ.maps T ⟨hT, le_rfl⟩]
    exact hF.localInverseAt_apply_self.symm
  refine ⟨T₁, hTT₁, ⟨{
    curve := fun s => if s ≤ T then γ.curve s else e (line s)
    continuous := ?_
    initial := by simp only [hT, ↓reduceIte, γ.initial]
    maps := ?_
  }⟩⟩
  · apply ContinuousOn.if
    · intro s hs
      have hsT : s = T := frontier_Iic_subset T hs.2
      simpa only [hsT] using hJoin
    · apply γ.continuous.mono
      intro s hs
      exact ⟨hs.1.1, by simpa only [show {s : ℝ | s ≤ T} = Iic T from rfl, closure_Iic, mem_Iic] using hs.2⟩
    · apply e.continuousOn.comp hLine.continuousOn
      intro s hs
      apply hRight
      refine ⟨?_, hs.1.2⟩
      simp only [not_le] at hs
      have := closure_lt_subset_le continuous_const continuous_id hs.2
      exact this
  · intro s hs
    split_ifs with hsT
    · exact γ.maps s ⟨hs.1, hsT⟩
    · exact hF.apply_localInverseAt_of_mem (hRight s ⟨le_of_not_ge hsT, hs.2⟩)

private theorem exists_segmentLift
    (hF : ∀ x, HasStrictFDerivAt F (A x : X →L[ℝ] Y) x)
    {M : NNReal} (hBound : ∀ x, ‖(A x).symm.toContinuousLinearMap‖ ≤ M)
    (x₀ : X) (v : Y) :
    Nonempty (SegmentLift F x₀ v 1) := by
  classical
  let S : Set ℝ := {T | T ∈ Icc 0 1 ∧ Nonempty (SegmentLift F x₀ v T)}
  have hZero : Nonempty (SegmentLift F x₀ v 0) := ⟨{
    curve := fun _ => x₀
    continuous := continuous_const.continuousOn
    initial := rfl
    maps := by intro s hs; have : s = 0 := le_antisymm hs.2 hs.1; simp [this]
  }⟩
  have h0 : 0 ∈ S := ⟨⟨le_rfl, zero_le_one⟩, hZero⟩
  have hS : S.Nonempty := ⟨0, h0⟩
  have hBdd : BddAbove S := ⟨1, fun _ h => h.1.2⟩
  let T := sSup S
  have hT0 : 0 ≤ T := le_csSup hBdd h0
  have hT1 : T ≤ 1 := csSup_le hS (fun _ h => h.1.2)
  have hHomeo := isLocalHomeomorph hF
  have hAtSup : Nonempty (SegmentLift F x₀ v T) := by
    by_cases hT : T = 0
    · simpa only [hT] using hZero
    have hTpos : 0 < T := lt_of_le_of_ne hT0 (Ne.symm hT)
    have hExists (s : ℝ) (hs : s ∈ Ico 0 T) : Nonempty (SegmentLift F x₀ v s) := by
      obtain ⟨t, ht, hst⟩ := (lt_csSup_iff hBdd hS).mp hs.2
      exact ⟨ht.2.some.restrict hst.le⟩
    let γ : ℝ → X := fun s => if hs : s ∈ Ico 0 T then (hExists s hs).some.curve s else x₀
    have hAgree {t : ℝ} (ht : t ∈ Ico 0 T) :
        EqOn γ (hExists t ht).some.curve (Icc 0 t) := by
      intro s hs
      have hsT : s ∈ Ico 0 T := ⟨hs.1, hs.2.trans_lt ht.2⟩
      dsimp only [γ]
      rw [dite_eq_left hsT]
      exact ((hExists s hsT).some.agree hHomeo (hExists t ht).some hs.1 hs.2) ⟨hs.1, le_rfl⟩
    have hLip : LipschitzOnWith (M * ‖v‖₊) γ (Ico 0 T) := by
      rw [lipschitzOnWith_iff_norm_sub_le]
      intro s hs t ht
      let u := max s t
      have hu : u ∈ Ico 0 T := ⟨hs.1.trans (le_max_left _ _), max_lt hs.2 ht.2⟩
      let hγu := (hExists u hu).some
      have hsu : s ∈ Icc 0 u := ⟨hs.1, le_max_left _ _⟩
      have htu : t ∈ Icc 0 u := ⟨ht.1, le_max_right _ _⟩
      rw [hAgree hu hsu, hAgree hu htu]
      exact (lipschitzOnWith_iff_norm_sub_le.mp
        (lift_lipschitzOn hF hBound hγu.continuous hγu.maps)) hsu htu
    let γ₁ := extendFrom (Ico 0 T) γ
    have hClosure : closure (Ico 0 T) = Icc 0 T := closure_Ico hTpos.ne
    have hCont : ContinuousOn γ₁ (Icc 0 T) := by
      rw [← hClosure]
      exact continuousOn_extendFrom_of_uniformContinuousOn hLip.uniformContinuousOn
    have hExt : EqOn γ₁ γ (Ico 0 T) := extendFrom_extends hLip.continuousOn
    have hMap : EqOn (F ∘ γ₁) (fun s => F x₀ + s • v) (Ico 0 T) := by
      intro s hs
      rw [Function.comp_apply, hExt hs, hAgree hs ⟨hs.1, le_rfl⟩]
      exact (hExists s hs).some.maps s ⟨hs.1, le_rfl⟩
    refine ⟨⟨γ₁, hCont, ?_, ?_⟩⟩
    · rw [hExt ⟨le_rfl, hTpos⟩, hAgree ⟨le_rfl, hTpos⟩ ⟨le_rfl, le_rfl⟩]
      exact (hExists 0 ⟨le_rfl, hTpos⟩).some.initial
    · exact hMap.of_subset_closure (hHomeo.continuous.comp_continuousOn hCont)
        (by fun_prop) Ico_subset_Icc_self (by rw [hClosure])
  by_cases hT : T = 1
  · simpa only [hT] using hAtSup
  have hTlt : T < 1 := lt_of_le_of_ne hT1 hT
  obtain ⟨T₁, hTT₁, ⟨γ⟩⟩ := hAtSup.some.extend hHomeo hT0
  let T₂ := min T₁ 1
  have hTT₂ : T < T₂ := lt_min hTT₁ hTlt
  have hT₂ : T₂ ∈ S :=
    ⟨⟨hT0.trans hTT₂.le, min_le_right _ _⟩, ⟨γ.restrict (min_le_left _ _)⟩⟩
  exact (hTT₂.not_ge (le_csSup hBdd hT₂)).elim

/-- Uniformly bounded inverse derivatives give a bijection and a global inverse Lipschitz bound. -/
theorem bijective_and_antilipschitz_of_hasStrictFDerivAt
    (hF : ∀ x, HasStrictFDerivAt F (A x : X →L[ℝ] Y) x)
    {M : NNReal} (hBound : ∀ x, ‖(A x).symm.toContinuousLinearMap‖ ≤ M) :
    Function.Bijective F ∧ AntilipschitzWith M F := by
  let γ (p : Y) := (exists_segmentLift hF hBound (0 : X) (p - F 0)).some
  let Γ : I × Y → X := fun q => (γ q.2).curve q.1
  let line : C(I × Y, Y) := ⟨fun q => F 0 + (q.1 : ℝ) • (q.2 - F 0), by fun_prop⟩
  have hHomeo := isLocalHomeomorph hF
  have hΓ : Continuous Γ := by
    apply hHomeo.continuous_lift (T2Space.isSeparatedMap F) line
    · funext q
      exact (γ q.2).maps q.1 q.1.2
    · have hInitial : (fun p => Γ (0, p)) = fun _ => (0 : X) := by
        funext p
        exact (γ p).initial
      rw [hInitial]
      exact continuous_const
    · intro p
      exact (γ p).continuous.comp_continuous continuous_subtype_val (fun s => s.2)
  let FInv : Y → X := fun p => Γ (1, p)
  have hInv : Continuous FInv := hΓ.comp (by fun_prop)
  have hRight : Function.RightInverse FInv F := by
    intro p
    change F ((γ p).curve (1 : I)) = p
    rw [Set.Icc.coe_one]
    simpa only [one_smul, add_sub_cancel] using (γ p).maps 1 ⟨zero_le_one, le_rfl⟩
  have hZero : FInv (F 0) = 0 := by
    have hConst := (T2Space.isSeparatedMap F).const_of_comp hHomeo.isLocallyInjective
      ((γ (F 0)).continuous.comp_continuous continuous_subtype_val (fun s => s.2))
      (fun s t => by simp only [Function.comp_apply, (γ (F 0)).maps s s.2, (γ (F 0)).maps t t.2, sub_self, smul_zero])
      (1 : I) (0 : I)
    exact hConst.trans (γ (F 0)).initial
  have hLeft : Function.LeftInverse FInv F := by
    have hEq := (T2Space.isSeparatedMap F).eq_of_comp_eq hHomeo.isLocallyInjective
      (hInv.comp hHomeo.continuous) continuous_id
      (show F ∘ (FInv ∘ F) = F ∘ id from funext fun x => hRight (F x)) 0 hZero
    exact fun x => congrFun hEq x
  have hBij : Function.Bijective F := ⟨hLeft.injective, hRight.surjective⟩
  refine ⟨hBij, ?_⟩
  rw [antilipschitzWith_iff_le_mul_dist]
  intro x₁ x₂
  let δ := (exists_segmentLift hF hBound x₂ (F x₁ - F x₂)).some
  have hEnd : δ.curve 1 = x₁ := hBij.injective (by
    simpa only [one_smul, add_sub_cancel] using δ.maps 1 ⟨zero_le_one, le_rfl⟩)
  have hLip := (lift_lipschitzOn hF hBound δ.continuous δ.maps).dist_le_mul
    1 (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
    0 (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
  simpa only [hEnd, δ.initial, NNReal.coe_mul, coe_nnnorm, dist_eq_norm, sub_zero, norm_one, mul_one] using hLip

/-- A continuously differentiable map with uniformly bounded inverse derivatives is globally invertible. -/
theorem bijective_and_antilipschitz
    (hF : ContDiff ℝ 1 F) (hDeriv : ∀ x, HasFDerivAt F (A x : X →L[ℝ] Y) x)
    {M : NNReal} (hBound : ∀ x, ‖(A x).symm.toContinuousLinearMap‖ ≤ M) :
    Function.Bijective F ∧ AntilipschitzWith M F :=
  bijective_and_antilipschitz_of_hasStrictFDerivAt
    (fun x => hF.contDiffAt.hasStrictFDerivAt' (hDeriv x) one_ne_zero) hBound

end UN.GlobalInverse
