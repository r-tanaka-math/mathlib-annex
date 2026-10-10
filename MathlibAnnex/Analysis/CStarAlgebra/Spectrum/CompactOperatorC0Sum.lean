/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactOperatorC0SumClassification
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.Topology

/-!
# The spectrum of a c₀-sum of compact-operator algebras

The independently defined irreducible and primitive spectra of a dependent
c₀-sum of compact-operator algebras are identified with the index type.  The
identification uses the actual unitary classification of irreducible
representations, not equality of kernels.  Explicit single-coordinate compact
operators isolate every point, proving discreteness in the existing hull-kernel
topologies.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.whnf.reducibleClassField false
noncomputable section

open Set InnerProductSpace
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uι uH uK

namespace CompactOperatorC0Sum

variable {ι : Type uι} (H : ι → Type uH)
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)] [∀ i, Nontrivial (H i)]

private abbrev compactSpectrumOrder : PartialOrder (CompactOperatorC0Sum H) :=
  _root_.CStarAlgebra.spectralOrder (CompactOperatorC0Sum H)

attribute [local instance] compactSpectrumOrder

private abbrev compactSpectrumStarOrder : StarOrderedRing (CompactOperatorC0Sum H) :=
  _root_.CStarAlgebra.spectralOrderedRing (CompactOperatorC0Sum H)

attribute [local instance] compactSpectrumStarOrder

private abbrev SpectrumFiber (i : ι) :=
  ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i)

/-- The irreducible-spectrum point represented by the `i`-th coordinate action. -/
def coordinateSpectrumPoint (i : ι) : IrreducibleSpectrum (CompactOperatorC0Sum H) :=
  IrreducibleSpectrum.ofRepresentation (coordinateRepresentation H i)
    (isIrreducible_coordinateRepresentation H i)

/-- The primitive-kernel point represented by the `i`-th coordinate action. -/
def coordinatePrimitivePoint (i : ι) : PrimitiveSpectrum (CompactOperatorC0Sum H) :=
  PrimitiveSpectrum.ofRepresentation (coordinateRepresentation H i)
    (isIrreducible_coordinateRepresentation H i)

@[simp]
theorem kernel_coordinateSpectrumPoint (i : ι) :
    IrreducibleSpectrum.kernel (coordinateSpectrumPoint H i) =
      coordinatePrimitivePoint H i := by
  exact IrreducibleSpectrum.kernel_ofRepresentation
    (coordinateRepresentation H i) (isIrreducible_coordinateRepresentation H i)

/-- Distinct coordinates give distinct points before passing to kernels. -/
theorem coordinateSpectrumPoint_injective :
    Function.Injective (coordinateSpectrumPoint H) := by
  intro i j hij
  by_contra hne
  have hU : (coordinateRepresentation H i).UnitaryEquivalent
      (coordinateRepresentation H j) :=
    (IrreducibleSpectrum.ofRepresentation_eq_iff
      (coordinateRepresentation H i) (coordinateRepresentation H j)
      (isIrreducible_coordinateRepresentation H i)
      (isIrreducible_coordinateRepresentation H j)).1 hij
  exact not_unitaryEquivalent_coordinateRepresentation_of_ne H hne hU

/-- Every irreducible-spectrum point is represented by one coordinate. -/
theorem coordinateSpectrumPoint_surjective :
    Function.Surjective (coordinateSpectrumPoint H) := by
  intro q
  obtain ⟨phi, rfl⟩ := IrreducibleSpectrum.ofPureState_surjective q
  obtain ⟨i, hi⟩ := exists_coordinate_unitaryEquivalent
    H phi.gnsRepresentation phi.isIrreducible_gnsRepresentation
  refine ⟨i, ?_⟩
  exact (IrreducibleSpectrum.ofRepresentation_eq_ofPureState_iff
    (coordinateRepresentation H i) (isIrreducible_coordinateRepresentation H i) phi).2 hi

/-- The index type is the actual small irreducible spectrum. -/
def coordinateSpectrumEquiv : ι ≃ IrreducibleSpectrum (CompactOperatorC0Sum H) :=
  Equiv.ofBijective (coordinateSpectrumPoint H)
    ⟨coordinateSpectrumPoint_injective H, coordinateSpectrumPoint_surjective H⟩

@[simp]
theorem coordinateSpectrumEquiv_apply (i : ι) :
    coordinateSpectrumEquiv H i = coordinateSpectrumPoint H i := rfl

/-- Distinct coordinates have distinct primitive points. -/
theorem coordinatePrimitivePoint_injective :
    Function.Injective (coordinatePrimitivePoint H) := by
  intro i j hij
  by_contra hne
  apply coordinateKernel_ne_of_ne H hne
  apply SetLike.coe_injective
  exact congrArg Subtype.val hij

/-- Every primitive point is the kernel of one coordinate representation. -/
theorem coordinatePrimitivePoint_surjective :
    Function.Surjective (coordinatePrimitivePoint H) := by
  intro P
  obtain ⟨phi, rfl⟩ := PrimitiveSpectrum.ofPureState_surjective P
  obtain ⟨i, hi⟩ := exists_coordinate_unitaryEquivalent
    H phi.gnsRepresentation phi.isIrreducible_gnsRepresentation
  refine ⟨i, ?_⟩
  apply Subtype.ext
  change (NonUnitalCStarRepresentation.kernelIdeal (coordinateRepresentation H i) :
      Set (CompactOperatorC0Sum H)) =
    (NonUnitalCStarRepresentation.kernelIdeal phi.gnsRepresentation :
      Set (CompactOperatorC0Sum H))
  exact congrArg SetLike.coe hi.kernelIdeal_eq

/-- The index type is also the independently constructed primitive spectrum. -/
def coordinatePrimitiveEquiv : ι ≃ PrimitiveSpectrum (CompactOperatorC0Sum H) :=
  Equiv.ofBijective (coordinatePrimitivePoint H)
    ⟨coordinatePrimitivePoint_injective H, coordinatePrimitivePoint_surjective H⟩

@[simp]
theorem coordinatePrimitiveEquiv_apply (i : ι) :
    coordinatePrimitiveEquiv H i = coordinatePrimitivePoint H i := rfl

/-- A single-coordinate compact operator which is nonzero precisely in the
selected coordinate. -/
theorem exists_coordinate_separator (i : ι) :
    ∃ x : CompactOperatorC0Sum H,
      coordinateEvaluation H i x ≠ 0 ∧
        ∀ j : ι, j ≠ i → coordinateEvaluation H j x = 0 := by
  classical
  obtain ⟨v, hv⟩ := exists_ne (0 : H i)
  let a : SpectrumFiber H i := ⟨rankOne ℂ v v, isCompactOperator_rankOne v v⟩
  let x : CompactOperatorC0Sum H :=
    C0DirectSum.single (fun j => SpectrumFiber H j) i a
  refine ⟨x, ?_, ?_⟩
  · change C0DirectSum.eval (fun k => SpectrumFiber H k) i
      (C0DirectSum.single (fun k => SpectrumFiber H k) i a) ≠ 0
    rw [C0DirectSum.eval_single_same]
    intro ha
    apply rankOne_ne_zero (𝕜 := ℂ) hv hv
    exact congrArg Subtype.val ha
  · intro j hji
    change C0DirectSum.eval (fun k => SpectrumFiber H k) j x = 0
    exact C0DirectSum.eval_single_of_ne (fun k => SpectrumFiber H k) hji a

/-- For a fixed algebra element, the primitive ideals which contain it form a
closed hull-kernel set. -/
theorem isClosed_setOf_mem_primitive_kernel (a : CompactOperatorC0Sum H) :
    IsClosed {P : PrimitiveSpectrum (CompactOperatorC0Sum H) | a ∈ P.val} := by
  apply isClosed_of_closure_subset
  intro P hP
  rw [closure_primitiveSpectrum] at hP
  exact hP a (fun Q hQ => hQ)

/-- The corresponding set in the irreducible spectrum is closed by continuity
of the genuine kernel map. -/
theorem isClosed_setOf_mem_irreducible_kernel (a : CompactOperatorC0Sum H) :
    IsClosed {q : IrreducibleSpectrum (CompactOperatorC0Sum H) |
      a ∈ (IrreducibleSpectrum.kernel q).val} := by
  exact (isClosed_setOf_mem_primitive_kernel H a).preimage
    (continuous_irreducibleSpectrum_kernel (A := CompactOperatorC0Sum H))

/-- An explicit coordinate separator isolates one irreducible-spectrum point. -/
theorem isOpen_singleton_coordinateSpectrumPoint (i : ι) :
    IsOpen ({coordinateSpectrumPoint H i} :
      Set (IrreducibleSpectrum (CompactOperatorC0Sum H))) := by
  obtain ⟨x, hxi, hxother⟩ := exists_coordinate_separator H i
  have hopen : IsOpen {q : IrreducibleSpectrum (CompactOperatorC0Sum H) |
      x ∉ (IrreducibleSpectrum.kernel q).val} :=
    (isClosed_setOf_mem_irreducible_kernel H x).isOpen_compl
  have heq : {q : IrreducibleSpectrum (CompactOperatorC0Sum H) |
      x ∉ (IrreducibleSpectrum.kernel q).val} = {coordinateSpectrumPoint H i} := by
    ext q
    obtain ⟨j, rfl⟩ := coordinateSpectrumPoint_surjective H q
    constructor
    · intro hx
      have hji : j = i := by
        by_contra hne
        apply hx
        rw [kernel_coordinateSpectrumPoint]
        change x ∈ NonUnitalCStarRepresentation.kernelIdeal (coordinateRepresentation H j)
        rw [mem_coordinateKernel]
        exact hxother j hne
      exact Set.mem_singleton_iff.2 (congrArg (coordinateSpectrumPoint H) hji)
    · intro hq hx
      have hpoint : coordinateSpectrumPoint H j = coordinateSpectrumPoint H i :=
        Set.mem_singleton_iff.1 hq
      have hji : j = i := coordinateSpectrumPoint_injective H hpoint
      subst j
      rw [kernel_coordinateSpectrumPoint] at hx
      change x ∈ NonUnitalCStarRepresentation.kernelIdeal (coordinateRepresentation H i) at hx
      exact hxi ((mem_coordinateKernel H i x).1 hx)
  rwa [heq] at hopen

/-- An explicit coordinate separator also isolates one primitive point. -/
theorem isOpen_singleton_coordinatePrimitivePoint (i : ι) :
    IsOpen ({coordinatePrimitivePoint H i} :
      Set (PrimitiveSpectrum (CompactOperatorC0Sum H))) := by
  obtain ⟨x, hxi, hxother⟩ := exists_coordinate_separator H i
  have hopen : IsOpen {P : PrimitiveSpectrum (CompactOperatorC0Sum H) | x ∉ P.val} :=
    (isClosed_setOf_mem_primitive_kernel H x).isOpen_compl
  have heq : {P : PrimitiveSpectrum (CompactOperatorC0Sum H) | x ∉ P.val} =
      {coordinatePrimitivePoint H i} := by
    ext P
    obtain ⟨j, rfl⟩ := coordinatePrimitivePoint_surjective H P
    constructor
    · intro hx
      have hji : j = i := by
        by_contra hne
        apply hx
        change x ∈ NonUnitalCStarRepresentation.kernelIdeal (coordinateRepresentation H j)
        rw [mem_coordinateKernel]
        exact hxother j hne
      exact Set.mem_singleton_iff.2 (congrArg (coordinatePrimitivePoint H) hji)
    · intro hP hx
      have hpoint : coordinatePrimitivePoint H j = coordinatePrimitivePoint H i :=
        Set.mem_singleton_iff.1 hP
      have hji : j = i := coordinatePrimitivePoint_injective H hpoint
      subst j
      change x ∈ NonUnitalCStarRepresentation.kernelIdeal (coordinateRepresentation H i) at hx
      exact hxi ((mem_coordinateKernel H i x).1 hx)
  rwa [heq] at hopen

/-- The independent irreducible spectrum has the discrete topology. -/
noncomputable instance instDiscreteTopologyIrreducibleSpectrum :
    DiscreteTopology (IrreducibleSpectrum (CompactOperatorC0Sum H)) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro q
  obtain ⟨i, rfl⟩ := coordinateSpectrumPoint_surjective H q
  exact isOpen_singleton_coordinateSpectrumPoint H i

/-- The independent primitive spectrum has the discrete topology. -/
noncomputable instance instDiscreteTopologyPrimitiveSpectrum :
    DiscreteTopology (PrimitiveSpectrum (CompactOperatorC0Sum H)) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro P
  obtain ⟨i, rfl⟩ := coordinatePrimitivePoint_surjective H P
  exact isOpen_singleton_coordinatePrimitivePoint H i

/-- Forward direction of Paper Lemma 8.10 for the actual dependent c₀-sum:
every irreducible representation is a coordinate compact representation, its
independent spectra are indexed by `ι`, and both hull-kernel topologies are
discrete. -/
theorem coordinate_classification_and_spectra_bijective :
    (∀ (K : Type uK) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
        [CompleteSpace K],
      ∀ rho : NonUnitalCStarRepresentation (CompactOperatorC0Sum H) K,
        rho.IsIrreducible →
          ∃! i : ι, (coordinateRepresentation H i).UnitaryEquivalent rho) ∧
      Function.Bijective (coordinateSpectrumPoint H) ∧
      Function.Bijective (coordinatePrimitivePoint H) := by
  refine ⟨?_, ⟨
    ⟨coordinateSpectrumPoint_injective H, coordinateSpectrumPoint_surjective H⟩,
    ⟨coordinatePrimitivePoint_injective H, coordinatePrimitivePoint_surjective H⟩⟩⟩
  intro K _ _ _ rho hrho
  exact existsUnique_coordinate_unitaryEquivalent H rho hrho

end CompactOperatorC0Sum

end MathlibAnnex.Analysis.CStarAlgebra
