/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.Normed.GeometricStructure.L1ComplexComponent
import MathlibAnnex.Topology.ClosureSpace.Topological
import Mathlib.Topology.Order

/-!
# The primitive and geometric spectra of complex ℓ¹

Every component has zero intersection. Consequently PS is the singleton family
`{{0}}`, while GS has the indiscrete closure. Equality of component intersections
does not identify the components themselves. The ordinary topology below is
constructed only on GS, not on the non-topologizable original GSS.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set
open scoped lp ENNReal

namespace NormedSpace

/-- Every actual primitive point is the zero subset of ℓ¹. -/
theorem primitiveGeometricSpectrum_val_l1Complex
    (J : PrimitiveGeometricSpectrum ℂ ℓ¹(ℕ, ℂ)) : J.val = {0} := by
  obtain ⟨C, rfl⟩ := geometricSpectrumToPrimitive_surjective ℂ ℓ¹(ℕ, ℂ) J
  exact geometricSpectrumKernel_l1Complex C

/-- The primitive spectrum has at most one point; this is not a statement about GS. -/
theorem subsingleton_primitiveGeometricSpectrum_l1Complex :
    Subsingleton (PrimitiveGeometricSpectrum ℂ ℓ¹(ℕ, ℂ)) := by
  refine ⟨fun J K => Subtype.ext ?_⟩
  exact (primitiveGeometricSpectrum_val_l1Complex J).trans
    (primitiveGeometricSpectrum_val_l1Complex K).symm

/-- A constant unimodular sequence supplies an actual component. -/
theorem nonempty_geometricSpectrum_l1Complex : Nonempty (GeometricSpectrum ℂ ℓ¹(ℕ, ℂ)) := by
  let u := lp.inftyOfNormOne (fun _ : ℕ => (1 : ℂ)) (fun _ => norm_one)
  exact ⟨toGeometricSpectrum ℂ ℓ¹(ℕ, ℂ) (l1ComplexKernelPoint u (fun _ => norm_one))⟩

/-- The primitive family is exactly the one-element family whose member is `{0}`. -/
theorem primitiveGeometricSpectrumFamily_l1Complex :
    primitiveGeometricSpectrumFamily ℂ ℓ¹(ℕ, ℂ) = {{0}} := by
  obtain ⟨C⟩ := nonempty_geometricSpectrum_l1Complex
  rw [primitiveGeometricSpectrumFamily_eq_range]
  apply Set.ext
  intro J
  constructor
  · rintro ⟨D, rfl⟩
    exact Set.mem_singleton_iff.2 (geometricSpectrumKernel_l1Complex D)
  · intro hJ
    have hJ0 := Set.mem_singleton_iff.1 hJ
    exact ⟨C, (geometricSpectrumKernel_l1Complex C).trans hJ0.symm⟩

/-- Gamma has constant set-valued output, without an injectivity claim. -/
theorem geometricSpectrumToPrimitive_val_l1Complex (C : GeometricSpectrum ℂ ℓ¹(ℕ, ℂ)) :
    (geometricSpectrumToPrimitive ℂ ℓ¹(ℕ, ℂ) C).val = {0} :=
  geometricSpectrumKernel_l1Complex C

/-- Every nonempty subset of GS has full closure, even when it meets only one component. -/
theorem geometricSpectrumClosure_closure_l1Complex_of_nonempty
    (S : Set (GeometricSpectrum ℂ ℓ¹(ℕ, ℂ))) (hS : S.Nonempty) :
    (geometricSpectrumClosure ℂ ℓ¹(ℕ, ℂ)).closure S = Set.univ := by
  obtain ⟨D, hD⟩ := hS
  rw [geometricSpectrumClosure_closure]
  apply Set.eq_univ_iff_forall.2
  intro C a ha
  rw [geometricSpectrumKernel_l1Complex]
  have hDa := ha D hD
  rwa [geometricSpectrumKernel_l1Complex] at hDa

/-- A uniform closure formula: membership in the closure is exactly nonemptiness
of the selected subset. In particular the empty selection stays empty. -/
theorem geometricSpectrumClosure_closure_l1Complex
    (S : Set (GeometricSpectrum ℂ ℓ¹(ℕ, ℂ))) :
    (geometricSpectrumClosure ℂ ℓ¹(ℕ, ℂ)).closure S = {C | S.Nonempty} := by
  classical
  apply Set.ext
  intro C
  constructor
  · intro hC
    change S.Nonempty
    by_contra hS
    have he : S = ∅ := Set.eq_empty_iff_forall_notMem.2 (fun x hx => hS ⟨x, hx⟩)
    rw [he, ClosureSpace.closure_empty] at hC
    exact hC
  · intro hS
    rw [geometricSpectrumClosure_closure_l1Complex_of_nonempty S hS]
    exact Set.mem_univ C

/-- The only closed subsets of GS are the empty set and the whole GS. -/
theorem isClosed_geometricSpectrumClosure_l1Complex_iff
    (S : Set (GeometricSpectrum ℂ ℓ¹(ℕ, ℂ))) :
    (geometricSpectrumClosure ℂ ℓ¹(ℕ, ℂ)).IsClosed S ↔ S = ∅ ∨ S = Set.univ := by
  constructor
  · intro h
    rcases S.eq_empty_or_nonempty with he | hn
    · exact Or.inl he
    · have hcl := ((geometricSpectrumClosure ℂ ℓ¹(ℕ, ℂ)).isClosed_iff S).1 h
      exact Or.inr (hcl.symm.trans
        (geometricSpectrumClosure_closure_l1Complex_of_nonempty S hn))
  · rintro (rfl | rfl)
    · exact (geometricSpectrumClosure ℂ ℓ¹(ℕ, ℂ)).isClosed_empty
    · exact (geometricSpectrumClosure ℂ ℓ¹(ℕ, ℂ)).isClosed_univ

/-- Finite-union preservation follows from the computed closure, not from T1. -/
theorem isTopologizable_geometricSpectrumClosure_l1Complex :
    (geometricSpectrumClosure ℂ ℓ¹(ℕ, ℂ)).IsTopologizable := by
  intro S T
  rcases S.eq_empty_or_nonempty with rfl | hS
  · rw [Set.empty_union, ClosureSpace.closure_empty, Set.empty_union]
  · have hST : (S ∪ T).Nonempty := by
      obtain ⟨x, hx⟩ := hS
      exact ⟨x, Or.inl hx⟩
    rw [geometricSpectrumClosure_closure_l1Complex_of_nonempty _ hST,
      geometricSpectrumClosure_closure_l1Complex_of_nonempty _ hS, Set.univ_union]

/-- The actual ordinary topology associated to the geometric-spectrum closure. -/
def l1ComplexGeometricSpectrumTopology : TopologicalSpace (GeometricSpectrum ℂ ℓ¹(ℕ, ℂ)) :=
  (geometricSpectrumClosure ℂ ℓ¹(ℕ, ℂ)).toTopologicalSpace
    isTopologizable_geometricSpectrumClosure_l1Complex

/-- Mathlib orders topologies by reverse inclusion: `top` is the indiscrete topology. -/
theorem l1ComplexGeometricSpectrumTopology_eq_top :
    l1ComplexGeometricSpectrumTopology = ⊤ := by
  apply TopologicalSpace.ext_isClosed
  intro S
  change @_root_.IsClosed _ ((geometricSpectrumClosure ℂ ℓ¹(ℕ, ℂ)).toTopologicalSpace
    isTopologizable_geometricSpectrumClosure_l1Complex) S ↔ @_root_.IsClosed _ ⊤ S
  rw [ClosureSpace.isClosed_toTopologicalSpace_iff,
    isClosed_geometricSpectrumClosure_l1Complex_iff]
  letI : TopologicalSpace (GeometricSpectrum ℂ ℓ¹(ℕ, ℂ)) := ⊤
  exact (IndiscreteTopology.isClosed_iff S).symm

/-- On every subset, the ordinary topology has exactly the already computed closure. -/
theorem closure_l1ComplexGeometricSpectrumTopology
    (S : Set (GeometricSpectrum ℂ ℓ¹(ℕ, ℂ))) :
    @_root_.closure _ l1ComplexGeometricSpectrumTopology S =
      (geometricSpectrumClosure ℂ ℓ¹(ℕ, ℂ)).closure S :=
  ClosureSpace.closure_toTopologicalSpace _ _ S

/-- The primitive spectrum has the ordinary singleton-space closure. -/
theorem primitiveGeometricSpectrumClosure_closure_l1Complex
    (S : Set (PrimitiveGeometricSpectrum ℂ ℓ¹(ℕ, ℂ))) :
    (primitiveGeometricSpectrumClosure ℂ ℓ¹(ℕ, ℂ)).closure S = S := by
  letI := subsingleton_primitiveGeometricSpectrum_l1Complex
  apply Set.Subset.antisymm ?_ ((primitiveGeometricSpectrumClosure ℂ ℓ¹(ℕ, ℂ)).subset_closure S)
  intro J hJ
  rcases S.eq_empty_or_nonempty with he | ⟨K, hK⟩
  · rw [he, ClosureSpace.closure_empty] at hJ
    exact hJ.elim
  · exact (Subsingleton.elim K J) ▸ hK

/-- The primitive closure is also topologizable, by its explicit closure formula. -/
theorem isTopologizable_primitiveGeometricSpectrumClosure_l1Complex :
    (primitiveGeometricSpectrumClosure ℂ ℓ¹(ℕ, ℂ)).IsTopologizable := by
  intro S T
  rw [primitiveGeometricSpectrumClosure_closure_l1Complex,
    primitiveGeometricSpectrumClosure_closure_l1Complex,
    primitiveGeometricSpectrumClosure_closure_l1Complex]

end NormedSpace
