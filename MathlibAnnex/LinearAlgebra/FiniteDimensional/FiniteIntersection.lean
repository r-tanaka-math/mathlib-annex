/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Data.Nat.Find

/-!
# Finite intersections in finite-dimensional vector spaces

Arbitrary indexed submodule families and linear-functional kernels have the same
intersection as a finite subfamily. Empty families and zero spaces are included.
This algebraic module has no closure-space or GSS imports.
-/

@[expose] public section
set_option autoImplicit false

universe u v w
namespace Submodule
variable {𝕜 : Type u} [DivisionRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
variable {ι : Type w}

/-- Any family of subspaces of a finite-dimensional vector space has the
same intersection as some finite subfamily. Empty index types are included. -/
theorem exists_finset_iInf_eq_of_finiteDimensional (P : ι → Submodule 𝕜 V) :
    ∃ s : Finset ι, (⨅ i, P i) = ⨅ i ∈ s, P i := by
  classical
  let Q (s : Finset ι) : Submodule 𝕜 V := ⨅ i ∈ s, P i
  have hex : ∃ n : ℕ, ∃ s : Finset ι, Module.finrank 𝕜 (Q s) = n :=
    ⟨Module.finrank 𝕜 (Q ∅), ∅, rfl⟩
  obtain ⟨s, hs⟩ := Nat.find_spec hex
  have hmin (t : Finset ι) : Module.finrank 𝕜 (Q s) ≤ Module.finrank 𝕜 (Q t) := by
    rw [hs]
    exact Nat.find_min' hex ⟨t, rfl⟩
  have hins (i : ι) : Q (insert i s) = Q s ⊓ P i := by
    ext x
    simp only [Q, mem_iInf, mem_inf]
    constructor
    · intro hx
      exact ⟨fun j hj => hx j (Finset.mem_insert_of_mem hj),
        hx i (Finset.mem_insert_self i s)⟩
    · rintro ⟨hx, hi⟩ j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hi
      · exact hx j hj
  have hle (i : ι) : Q s ≤ P i := by
    have heq : Q s ⊓ P i = Q s :=
      eq_of_le_of_finrank_le inf_le_left (by
        have hdim := hmin (insert i s)
        change Module.finrank 𝕜 (Q s) ≤ Module.finrank 𝕜 (Q (insert i s)) at hdim
        rw [hins] at hdim
        exact hdim)
    rw [← heq]
    exact inf_le_right
  refine ⟨s, le_antisymm ?_ (le_iInf hle)⟩
  exact le_iInf fun i => le_iInf fun _ => iInf_le P i

/-- A selected set of indices has a finite subset with exactly the same
intersection. No finiteness of the set of points is asserted. -/
theorem exists_finite_subset_iInter_eq_of_finiteDimensional
    (P : ι → Submodule 𝕜 V) (s : Set ι) :
    ∃ t : Set ι, t ⊆ s ∧ t.Finite ∧
      (⋂ i ∈ t, (P i : Set V)) = ⋂ i ∈ s, (P i : Set V) := by
  classical
  obtain ⟨q, hq⟩ := exists_finset_iInf_eq_of_finiteDimensional (fun i : s => P i.val)
  refine ⟨Subtype.val '' (q : Set s), ?_, q.finite_toSet.image Subtype.val, ?_⟩
  · rintro i ⟨j, _, rfl⟩
    exact j.property
  · ext x
    constructor
    · intro hx
      have hxq : x ∈ (⨅ i ∈ q, P i.val : Submodule 𝕜 V) := by
        apply (mem_iInf _).mpr
        intro i
        apply (mem_iInf _).mpr
        intro hi
        exact Set.mem_iInter.mp (Set.mem_iInter.mp hx i.val) ⟨i, hi, rfl⟩
      have hxs : x ∈ (⨅ i : s, P i.val : Submodule 𝕜 V) := by
        rw [hq]
        exact hxq
      apply Set.mem_iInter.mpr
      intro i
      apply Set.mem_iInter.mpr
      intro hi
      exact (mem_iInf _).mp hxs ⟨i, hi⟩
    · intro hx
      apply Set.mem_iInter.mpr
      intro i
      apply Set.mem_iInter.mpr
      rintro ⟨j, _, rfl⟩
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hx j.val) j.property

end Submodule

namespace LinearMap
variable {𝕜 : Type u} [DivisionRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
variable {ι : Type w}

/-- In particular, arbitrary linear functional kernels are finitely determined;
zero functionals and an empty family are allowed. -/
theorem exists_finite_subset_iInter_ker_eq_of_finiteDimensional
    (f : ι → V →ₗ[𝕜] 𝕜) (s : Set ι) :
    ∃ t : Set ι, t ⊆ s ∧ t.Finite ∧
      (⋂ i ∈ t, ((f i).ker : Set V)) = ⋂ i ∈ s, ((f i).ker : Set V) :=
  Submodule.exists_finite_subset_iInter_eq_of_finiteDimensional (fun i => (f i).ker) s
end LinearMap
