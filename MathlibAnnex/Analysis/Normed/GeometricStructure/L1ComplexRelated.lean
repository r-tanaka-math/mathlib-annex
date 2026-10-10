/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.Normed.GeometricStructure.L1ComplexLinked
import Mathlib.Data.Finite.Prod
import Mathlib.Tactic.SplitIfs

/-!
# Finite phase range and complex ℓ¹ components

One direction multiplies the finite ranges along an actual `EqvGen` chain.
The other direction replaces the coordinates in one phase class at a time;
each consecutive pair has at most two relative phases. Neither direction
assumes a classification of components or a kernel-family provider.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set ComplexConjugate
open scoped lp ENNReal

namespace NormedSpace

/-- A linked pair has finite relative phase range. -/
theorem finite_range_l1PhaseRatio_of_linked (u v : ℓ^∞(ℕ, ℂ))
    (hu : ∀ n, ‖u n‖ = 1) (hv : ∀ n, ‖v n‖ = 1)
    (h : (geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).Linked
      (l1ComplexKernelPoint u hu) (l1ComplexKernelPoint v hv)) :
    (Set.range (l1PhaseRatio u v)).Finite := by
  obtain ⟨r, s, hrs⟩ := (linked_l1ComplexKernelPoint_iff u v hu hv).1 h
  apply ((Set.finite_singleton s).insert r).subset
  rintro _ ⟨n, rfl⟩
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hrs n

/-- Finiteness of phase range is symmetric, without finiteness of the index set. -/
theorem finite_range_l1PhaseRatio_swap (u v : ℓ^∞(ℕ, ℂ))
    (h : (Set.range (l1PhaseRatio u v)).Finite) :
    (Set.range (l1PhaseRatio v u)).Finite := by
  apply (h.image conj).subset
  rintro _ ⟨n, rfl⟩
  exact ⟨l1PhaseRatio u v n, Set.mem_range_self n, (l1PhaseRatio_swap u v n).symm⟩

/-- Finitely many phase values are preserved under concatenation of a chain. -/
theorem finite_range_l1PhaseRatio_trans (u v w : ℓ^∞(ℕ, ℂ)) (hv : ∀ n, ‖v n‖ = 1)
    (huv : (Set.range (l1PhaseRatio u v)).Finite)
    (hvw : (Set.range (l1PhaseRatio v w)).Finite) :
    (Set.range (l1PhaseRatio u w)).Finite := by
  apply ((huv.prod hvw).image (fun p : ℂ × ℂ => p.1 * p.2)).subset
  rintro _ ⟨n, rfl⟩
  exact ⟨(l1PhaseRatio u v n, l1PhaseRatio v w n),
    ⟨Set.mem_range_self n, Set.mem_range_self n⟩, l1PhaseRatio_mul u v w hv n⟩

/-- An actual finite chain between kernel points has finite relative phase range. -/
theorem finite_range_l1PhaseRatio_of_related (u v : ℓ^∞(ℕ, ℂ))
    (hu : ∀ n, ‖u n‖ = 1) (hv : ∀ n, ‖v n‖ = 1)
    (h : (geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).Related
      (l1ComplexKernelPoint u hu) (l1ComplexKernelPoint v hv)) :
    (Set.range (l1PhaseRatio u v)).Finite := by
  have hgeneral {I J : GeometricStructureSpace ℂ ℓ¹(ℕ, ℂ)}
      (hIJ : (geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).Related I J) :
      ∀ (a b : ℓ^∞(ℕ, ℂ)) (ha : ∀ n, ‖a n‖ = 1) (hb : ∀ n, ‖b n‖ = 1),
        l1ComplexKernelPoint a ha = I → l1ComplexKernelPoint b hb = J →
          (Set.range (l1PhaseRatio a b)).Finite := by
    change Relation.EqvGen (geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).Linked I J at hIJ
    induction hIJ with
    | rel I J hIJ =>
        intro a b ha hb hI hJ
        apply finite_range_l1PhaseRatio_of_linked a b ha hb
        rwa [hI, hJ]
    | refl I =>
        intro a b ha hb hI hJ
        apply finite_range_l1PhaseRatio_of_linked a b ha hb
        exact Or.inl (hI.trans hJ.symm)
    | symm I J _ ih =>
        intro a b ha hb hI hJ
        exact finite_range_l1PhaseRatio_swap b a (ih b a hb ha hJ hI)
    | trans I J K _ _ ih₁ ih₂ =>
        intro a b ha hb hI hK
        obtain ⟨c, hc, hJ⟩ := exists_l1ComplexKernelPoint_eq J
        exact finite_range_l1PhaseRatio_trans a c b hc
          (ih₁ a c ha hc hI hJ) (ih₂ c b hc hb hJ hK)
  exact hgeneral h u v hu hv rfl rfl

/-- Replace all coordinates in the specified finite collection of relative-phase
classes. This is an actual bounded coefficient sequence, not a formal chain label. -/
def l1PhasePatch (u v : ℓ^∞(ℕ, ℂ)) (hu : ∀ n, ‖u n‖ = 1) (hv : ∀ n, ‖v n‖ = 1)
    (s : Finset ℂ) : ℓ^∞(ℕ, ℂ) :=
  lp.inftyOfNormOne (fun n => if l1PhaseRatio u v n ∈ s then v n else u n)
    (fun n => by split_ifs <;> first | exact hv n | exact hu n)

@[simp]
theorem l1PhasePatch_apply (u v : ℓ^∞(ℕ, ℂ))
    (hu : ∀ n, ‖u n‖ = 1) (hv : ∀ n, ‖v n‖ = 1) (s : Finset ℂ) (n : ℕ) :
    l1PhasePatch u v hu hv s n = if l1PhaseRatio u v n ∈ s then v n else u n := rfl

@[simp]
theorem norm_l1PhasePatch (u v : ℓ^∞(ℕ, ℂ))
    (hu : ∀ n, ‖u n‖ = 1) (hv : ∀ n, ‖v n‖ = 1) (s : Finset ℂ) (n : ℕ) :
    ‖l1PhasePatch u v hu hv s n‖ = 1 := by
  rw [l1PhasePatch_apply]
  split_ifs <;> first | exact hv n | exact hu n

@[simp]
theorem l1PhasePatch_empty (u v : ℓ^∞(ℕ, ℂ))
    (hu : ∀ n, ‖u n‖ = 1) (hv : ∀ n, ‖v n‖ = 1) :
    l1PhasePatch u v hu hv ∅ = u := by
  apply Subtype.ext
  funext n
  simp [l1PhasePatch_apply]

/-- Once every attained phase class has been replaced the sequence is `v`. -/
theorem l1PhasePatch_eq_right (u v : ℓ^∞(ℕ, ℂ))
    (hu : ∀ n, ‖u n‖ = 1) (hv : ∀ n, ‖v n‖ = 1) (s : Finset ℂ)
    (hs : ∀ n, l1PhaseRatio u v n ∈ s) :
    l1PhasePatch u v hu hv s = v := by
  apply Subtype.ext
  funext n
  simp only [l1PhasePatch_apply, hs, if_true]

/-- Inserting one class changes the relative phase only to `r` or to `1`. -/
theorem l1PhaseRatio_patch_insert (u v : ℓ^∞(ℕ, ℂ))
    (hu : ∀ n, ‖u n‖ = 1) (hv : ∀ n, ‖v n‖ = 1) (s : Finset ℂ) (r : ℂ) (n : ℕ) :
    l1PhaseRatio (l1PhasePatch u v hu hv s) (l1PhasePatch u v hu hv (insert r s)) n = 1 ∨
      l1PhaseRatio (l1PhasePatch u v hu hv s) (l1PhasePatch u v hu hv (insert r s)) n = r := by
  classical
  change (if l1PhaseRatio u v n ∈ s then v n else u n) *
      conj (if l1PhaseRatio u v n ∈ insert r s then v n else u n) = 1 ∨
    (if l1PhaseRatio u v n ∈ s then v n else u n) *
      conj (if l1PhaseRatio u v n ∈ insert r s then v n else u n) = r
  by_cases hs : l1PhaseRatio u v n ∈ s
  · left
    have hi : l1PhaseRatio u v n ∈ insert r s := Finset.mem_insert_of_mem hs
    rw [if_pos hs, if_pos hi]
    exact Complex.mul_conj_eq_one_of_norm_eq_one (hv n)
  · by_cases hr : l1PhaseRatio u v n = r
    · right
      have hi : l1PhaseRatio u v n ∈ insert r s := Finset.mem_insert.2 (Or.inl hr)
      rw [if_neg hs, if_pos hi]
      exact hr
    · left
      have hi : l1PhaseRatio u v n ∉ insert r s := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨hr, hs⟩
      rw [if_neg hs, if_neg hi]
      exact Complex.mul_conj_eq_one_of_norm_eq_one (hu n)

/-- Each finite stage belongs to the same actual GSS component as the initial point. -/
theorem related_l1ComplexKernelPoint_phasePatch (u v : ℓ^∞(ℕ, ℂ))
    (hu : ∀ n, ‖u n‖ = 1) (hv : ∀ n, ‖v n‖ = 1) (s : Finset ℂ) :
    (geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).Related
      (l1ComplexKernelPoint u hu)
      (l1ComplexKernelPoint (l1PhasePatch u v hu hv s) (norm_l1PhasePatch u v hu hv s)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [l1PhasePatch_empty] using
        (geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).related_refl (l1ComplexKernelPoint u hu)
  | @insert r s _ ih =>
      apply (geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).related_trans ih
      apply (geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).related_of_linked
      apply (linked_l1ComplexKernelPoint_iff _ _
        (norm_l1PhasePatch u v hu hv s) (norm_l1PhasePatch u v hu hv (insert r s))).2
      exact ⟨1, r, l1PhaseRatio_patch_insert u v hu hv s r⟩

/-- Finitely many phase values give a finite linked chain by class replacement. -/
theorem related_l1ComplexKernelPoint_of_finite_range (u v : ℓ^∞(ℕ, ℂ))
    (hu : ∀ n, ‖u n‖ = 1) (hv : ∀ n, ‖v n‖ = 1)
    (h : (Set.range (l1PhaseRatio u v)).Finite) :
    (geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).Related
      (l1ComplexKernelPoint u hu) (l1ComplexKernelPoint v hv) := by
  have hpatch := related_l1ComplexKernelPoint_phasePatch u v hu hv h.toFinset
  have heq : l1PhasePatch u v hu hv h.toFinset = v :=
    l1PhasePatch_eq_right u v hu hv h.toFinset (fun n => h.mem_toFinset.2 (Set.mem_range_self n))
  simpa only [heq] using hpatch

/-- The component relation for complex ℓ¹: exactly finite relative phase range. -/
theorem related_l1ComplexKernelPoint_iff (u v : ℓ^∞(ℕ, ℂ))
    (hu : ∀ n, ‖u n‖ = 1) (hv : ∀ n, ‖v n‖ = 1) :
    (geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).Related
      (l1ComplexKernelPoint u hu) (l1ComplexKernelPoint v hv) ↔
      (Set.range (l1PhaseRatio u v)).Finite :=
  ⟨finite_range_l1PhaseRatio_of_related u v hu hv,
    related_l1ComplexKernelPoint_of_finite_range u v hu hv⟩

end NormedSpace
