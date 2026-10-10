/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.Primitive
import MathlibAnnex.Topology.ClosureSpace.HullKernel
import MathlibAnnex.Topology.ClosureSpace.TopologicalMaps

/-!
# Ordinary hull-kernel and irreducible-spectrum topologies

Finite-union preservation is proved using meet-primality of the actual
representation kernels. T0 by itself would not suffice. Empty selections
have the genuine top ideal as their intersection. The topology on the
irreducible spectrum is the pullback along kappa, not the quotient of any
weak-star topology and not a topology transported from geometric spectra.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The hull-kernel closure on the independently constructed primitive family. -/
def primitiveSpectrumClosure : ClosureSpace (PrimitiveSpectrum A) :=
  ClosureSpace.HullKernel.space (primitiveKernelFamily A) (univ_notMem_primitiveKernelFamily A)

namespace PrimitiveSpectrum
variable {A}

/-- The intersection of the ACTUAL two-sided ideals selected by S. -/
def kernelIntersection (S : Set (PrimitiveSpectrum A)) : TwoSidedIdeal A :=
  ⨅ P : S, P.val.toTwoSidedIdeal

@[simp]
theorem mem_kernelIntersection (S : Set (PrimitiveSpectrum A)) (a : A) :
    a ∈ kernelIntersection S ↔ ∀ P : PrimitiveSpectrum A, P ∈ S → a ∈ P.val := by
  simp only [kernelIntersection, TwoSidedIdeal.mem_iInf, mem_toTwoSidedIdeal, Subtype.forall]

@[simp]
theorem kernelIntersection_empty : kernelIntersection (∅ : Set (PrimitiveSpectrum A)) = ⊤ := by
  apply TwoSidedIdeal.ext
  intro a
  simp only [mem_kernelIntersection, Set.mem_empty_iff_false, false_implies, implies_true,
    TwoSidedIdeal.mem_top]

theorem kernelIntersection_union (S T : Set (PrimitiveSpectrum A)) :
    kernelIntersection (S ∪ T) = kernelIntersection S ⊓ kernelIntersection T := by
  apply TwoSidedIdeal.ext
  intro a
  simp only [mem_kernelIntersection, TwoSidedIdeal.mem_inf, Set.mem_union]
  constructor
  · intro h
    exact ⟨fun P hP => h P (Or.inl hP), fun P hP => h P (Or.inr hP)⟩
  · rintro ⟨hS, hT⟩ P (hP | hP)
    · exact hS P hP
    · exact hT P hP

theorem coe_kernelIntersection (S : Set (PrimitiveSpectrum A)) :
    (kernelIntersection S : Set A) = ClosureSpace.HullKernel.kernel (primitiveKernelFamily A) S := by
  ext a
  exact mem_kernelIntersection S a

theorem mem_primitiveSpectrumClosure_iff (S : Set (PrimitiveSpectrum A)) (P : PrimitiveSpectrum A) :
    P ∈ (primitiveSpectrumClosure A).closure S ↔ kernelIntersection S ≤ P.toTwoSidedIdeal := by
  change ClosureSpace.HullKernel.kernel (primitiveKernelFamily A) S ⊆ P.val ↔ _
  rw [← coe_kernelIntersection, ← P.coe_toTwoSidedIdeal]
  rfl

end PrimitiveSpectrum

/-- The nontrivial topological axiom follows from actual primitive-kernel
meet-primality. No order-generating assumption on ALL two-sided ideals is needed. -/
theorem primitiveSpectrumClosure_union (S T : Set (PrimitiveSpectrum A)) :
    (primitiveSpectrumClosure A).closure (S ∪ T) =
      (primitiveSpectrumClosure A).closure S ∪ (primitiveSpectrumClosure A).closure T := by
  ext P
  rw [PrimitiveSpectrum.mem_primitiveSpectrumClosure_iff,
    PrimitiveSpectrum.kernelIntersection_union, P.inf_le_toTwoSidedIdeal_iff,
    Set.mem_union, PrimitiveSpectrum.mem_primitiveSpectrumClosure_iff,
    PrimitiveSpectrum.mem_primitiveSpectrumClosure_iff]

theorem isTopologizable_primitiveSpectrumClosure : (primitiveSpectrumClosure A).IsTopologizable :=
  primitiveSpectrumClosure_union A

/-- The usual hull-kernel topology on actual primitive kernels. -/
instance PrimitiveSpectrum.instTopologicalSpace : TopologicalSpace (PrimitiveSpectrum A) :=
  (primitiveSpectrumClosure A).toTopologicalSpace (isTopologizable_primitiveSpectrumClosure A)

/-- The ordinary topological closure is literally the hull of the kernel. -/
theorem closure_primitiveSpectrum (S : Set (PrimitiveSpectrum A)) :
    _root_.closure S = {P | ∀ a : A, (∀ Q : PrimitiveSpectrum A, Q ∈ S → a ∈ Q.val) → a ∈ P.val} :=
  ClosureSpace.closure_toTopologicalSpace _ _ S

/-- The equivalent ideal-valued ordinary closure formula. -/
theorem mem_closure_primitiveSpectrum_iff (S : Set (PrimitiveSpectrum A)) (P : PrimitiveSpectrum A) :
    P ∈ _root_.closure S ↔ PrimitiveSpectrum.kernelIntersection S ≤ P.toTwoSidedIdeal := by
  rw [ClosureSpace.closure_toTopologicalSpace]
  exact PrimitiveSpectrum.mem_primitiveSpectrumClosure_iff S P

/-- The independent irreducible-spectrum closure is induced by the actual kappa. -/
def irreducibleSpectrumClosure : ClosureSpace (IrreducibleSpectrum A) :=
  (primitiveSpectrumClosure A).induced IrreducibleSpectrum.kernel

theorem isTopologizable_irreducibleSpectrumClosure :
    (irreducibleSpectrumClosure A).IsTopologizable :=
  ClosureSpace.isTopologizable_induced (isTopologizable_primitiveSpectrumClosure A) _

/-- The pullback closure written without image or preimage notation. -/
theorem irreducibleSpectrumClosure_closure (S : Set (IrreducibleSpectrum A)) :
    (irreducibleSpectrumClosure A).closure S =
      {q | ∀ a : A, (∀ r : IrreducibleSpectrum A, r ∈ S →
        a ∈ (IrreducibleSpectrum.kernel r).val) → a ∈ (IrreducibleSpectrum.kernel q).val} := by
  ext q
  change (∀ a : A, (∀ P : PrimitiveSpectrum A,
    P ∈ IrreducibleSpectrum.kernel '' S → a ∈ P.val) →
      a ∈ (IrreducibleSpectrum.kernel q).val) ↔ _
  constructor
  · intro h a ha
    apply h a
    rintro P ⟨r, hr, rfl⟩
    exact ha r hr
  · intro h a ha
    exact h a (fun r hr => ha (IrreducibleSpectrum.kernel r) ⟨r, hr, rfl⟩)

/-- The spectrum topology, constructed from the kernel pullback. -/
instance IrreducibleSpectrum.instTopologicalSpace : TopologicalSpace (IrreducibleSpectrum A) :=
  (irreducibleSpectrumClosure A).toTopologicalSpace (isTopologizable_irreducibleSpectrumClosure A)

/-- This equality rules out accidentally using the pure-state quotient topology. -/
theorem irreducibleSpectrum_topology_eq_induced :
    (IrreducibleSpectrum.instTopologicalSpace A) =
      TopologicalSpace.induced IrreducibleSpectrum.kernel (PrimitiveSpectrum.instTopologicalSpace A) :=
  ClosureSpace.toTopologicalSpace_induced _ (isTopologizable_primitiveSpectrumClosure A) _

theorem closure_irreducibleSpectrum (S : Set (IrreducibleSpectrum A)) :
    _root_.closure S = IrreducibleSpectrum.kernel ⁻¹'
      _root_.closure (IrreducibleSpectrum.kernel '' S) := by
  rw [ClosureSpace.closure_toTopologicalSpace, ClosureSpace.closure_toTopologicalSpace]
  rfl

/-- Ordinary continuity of kappa, with no injectivity assertion. -/
theorem continuous_irreducibleSpectrum_kernel :
    Continuous (IrreducibleSpectrum.kernel : IrreducibleSpectrum A → PrimitiveSpectrum A) := by
  apply (ClosureSpace.continuous_toTopologicalSpace_iff _ _
    (isTopologizable_irreducibleSpectrumClosure A)
    (isTopologizable_primitiveSpectrumClosure A) _).2
  exact ClosureSpace.continuous_induced _ _

/-- Surjectivity, rather than injectivity, gives the exact image-closure identity. -/
theorem image_closure_irreducibleSpectrum_kernel (S : Set (IrreducibleSpectrum A)) :
    IrreducibleSpectrum.kernel '' _root_.closure S =
      _root_.closure (IrreducibleSpectrum.kernel '' S) := by
  rw [ClosureSpace.closure_toTopologicalSpace, ClosureSpace.closure_toTopologicalSpace]
  exact ClosureSpace.image_induced_closure _ _ IrreducibleSpectrum.kernel_surjective S

end MathlibAnnex.Analysis.CStarAlgebra
