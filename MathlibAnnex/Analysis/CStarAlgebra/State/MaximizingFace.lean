/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.State.Ideal
import Mathlib.Topology.Order.Compact

/-!
# Pure states retaining an evaluation on an annihilator face

A maximizing face of the existing weak-star annihilator face supplies a pure
state without decreasing a strictly positive real evaluation. The tested
algebra element need not be positive or self-adjoint. No compact-operator,
GSS, representation, or quotient hypothesis occurs in this theorem.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

section Unital

variable {D : Type u} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

/-- A positive detecting evaluation on the weak-star annihilator face can be
retained by a pure state of the entire unital algebra. The maximizing face is
constructed and proved extreme; purity is not a hypothesis on the input state. -/
theorem exists_pureState_annihilating_of_pos_weakStateFace
    (J : TwoSidedIdeal D) (b : D) (psi : WeakDual ℂ D)
    (hpsi : psi ∈ weakStateFace J) (hpos : 0 < (psi b).re) :
    ∃ phi : StrongDual ℂ D, phi ∈ stateSpace D ∧ IsPureState D phi ∧
      (∀ j : D, j ∈ J → phi j = 0) ∧
      (psi b).re ≤ (phi b).re ∧ 0 < (phi b).re := by
  letI : IsScalarTower ℝ ℂ (WeakDual ℂ D) :=
    inferInstanceAs (IsScalarTower ℝ ℂ (StrongDual ℂ D))
  letI : LocallyConvexSpace ℝ (WeakDual ℂ D) :=
    inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℂ D)))
  let C : Set (WeakDual ℂ D) := weakStateFace J
  let ev : WeakDual ℂ D → ℝ := fun p => (p b).re
  have hev : Continuous ev := Complex.continuous_re.comp (WeakDual.eval_continuous b)
  have hC : IsCompact C := isCompact_weakStateFace J
  obtain ⟨chi, hchi, hmax⟩ := hC.exists_isMaxOn ⟨psi, hpsi⟩ hev.continuousOn
  let m : ℝ := ev chi
  have hupper : ∀ p ∈ C, ev p ≤ m := hmax
  have hm : 0 < m := hpos.trans_le (hupper psi hpsi)
  let F : Set (WeakDual ℂ D) := {p | p ∈ C ∧ ev p = m}
  have hFnonempty : F.Nonempty := ⟨chi, hchi, rfl⟩
  have hFcompact : IsCompact F :=
    hC.inter_right (isClosed_eq hev continuous_const)
  have hFextreme : IsExtreme ℝ C F := by
    refine ⟨fun _ hp => hp.1, ?_⟩
    intro p hp q hq r hr hseg
    refine ⟨hp, ?_⟩
    rcases hseg with ⟨s, t, hs, ht, hst, hsum⟩
    have hvalue := congrArg (fun z : WeakDual ℂ D => z b) hsum
    change s • p b + t • q b = r b at hvalue
    have hsum' : s * ev p + t * ev q = ev r := by
      simpa [ev, Complex.real_smul] using congrArg Complex.re hvalue
    rw [hr.2] at hsum'
    have hstm : s * m + t * m = m := by
      rw [← add_mul, hst, one_mul]
    have hp_le := hupper p hp
    have hq_le := hupper q hq
    apply le_antisymm hp_le
    by_contra hlt
    have hp_lt : ev p < m := lt_of_not_ge hlt
    have hstrict : 0 < s * (m - ev p) := mul_pos hs (sub_pos.mpr hp_lt)
    have hother : 0 ≤ t * (m - ev q) :=
      mul_nonneg ht.le (sub_nonneg.mpr hq_le)
    nlinarith
  obtain ⟨eta, heta⟩ := hFcompact.extremePoints_nonempty hFnonempty
  have hetaC : eta ∈ C.extremePoints ℝ :=
    hFextreme.extremePoints_subset_extremePoints heta
  have hetaState : eta ∈ (weakStateSpace D).extremePoints ℝ :=
    (isExtreme_weakStateFace J).extremePoints_subset_extremePoints hetaC
  have hpure : IsPureState D eta.toStrongDual := by
    change eta.toStrongDual ∈ (stateSpace D).extremePoints ℝ
    rw [mem_extremePoints_iff_left] at hetaState ⊢
    refine ⟨hetaState.1, ?_⟩
    intro p hp q hq hseg
    let p' : WeakDual ℂ D := StrongDual.toWeakDual p
    let q' : WeakDual ℂ D := StrongDual.toWeakDual q
    have hp' : p' ∈ weakStateSpace D := hp
    have hq' : q' ∈ weakStateSpace D := hq
    have hseg' : eta ∈ openSegment ℝ p' q' := by
      rcases hseg with ⟨s, t, hs, ht, hst, hsum⟩
      refine ⟨s, t, hs, ht, hst, ?_⟩
      apply DFunLike.ext _ _
      intro a
      change s • p a + t • q a = eta a
      exact congrArg (fun z : StrongDual ℂ D => z a) hsum
    have heq : p' = eta := hetaState.2 p' hp' q' hq' hseg'
    apply ContinuousLinearMap.ext
    intro a
    exact congrArg (fun z : WeakDual ℂ D => z a) heq
  have heval : ev eta = m := heta.1.2
  refine ⟨eta.toStrongDual, hpure.1, hpure, heta.1.1.2, ?_, ?_⟩
  · change ev psi ≤ ev eta
    rw [heval]
    exact hupper psi hpsi
  · change 0 < ev eta
    rwa [heval]

end Unital

end MathlibAnnex.Analysis.CStarAlgebra
