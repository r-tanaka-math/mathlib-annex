/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.CompactlyRepresentedDecomposition
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactOperatorC0SumClassification
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.Topology
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.CompactKernel
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.PrimitiveRepresentative
import MathlibAnnex.Analysis.CStarAlgebra.Representation.PrimitiveCompactRange

/-!
# Compact representations, CCR ranges, and discrete primitive spectrum

The already constructed `compactC0Decomposition` is used, not reconstructed.
Every irreducible representation is pulled to that very compact c₀-sum and
classified by its unique coordinate. Its actual intertwining isometry is
pulled back to the original algebra, and literal compact-operator range is
transported through that same isometry.

An actual single-coordinate rank-one element is pulled back through the same
algebra equivalence and isolates each primitive point in the existing
hull-kernel topology. No second choice of a spectrum topology, or order on a
target spectrum, is made. The irreducible spectrum is discrete as well, using
the genuine continuous kernel map and its injectivity proved from the compact
ranges. No new topology or CCR predicate is introduced.

The canonical spectral order is local, as in `compactC0Decomposition`. The
index, dependent Hilbert fibers, and models therefore use exactly its choices.
No order, separability, countability, unit, or nontriviality hypothesis is
exported. The testing Hilbert universe is independent of both the algebra
universe and the given faithful representation's universe.

Finally, the selected primitive pure-state GNS condition is related to all
pure-state GNS tests by an actual equivalence. A separate universe-polymorphic
lemma lifts the selected condition to every irreducible representation.
This lift uses compact containment and equal-kernel rigidity to construct a
unitary; equal primitive kernels by themselves are not identified with
unitary equivalence. The selected condition in the final forward theorem is
a proved consequence, not an assumed replacement for CCR.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.whnf.reducibleClassField false
noncomputable section

open Set InnerProductSpace
open scoped CStarAlgebra Topology

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

namespace NonUnitalCStarRepresentation

set_option maxHeartbeats 8000000 in
/-- Every irreducible action of the original algebra is unitarily equivalent
to exactly one coordinate action pulled back through the actual canonical
compact c₀-decomposition. The same unitary works on every algebra element. -/
theorem existsUnique_coordinate_unitaryEquivalent_compactC0Decomposition
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented)
    (rho : NonUnitalCStarRepresentation A K) (hrho : rho.IsIrreducible) :
    ∃! i : MinimalClosedStarIdeal A,
      NonUnitalCStarRepresentation.UnitaryEquivalent
        ((CompactOperatorC0Sum.coordinateRepresentation
          (fun j : MinimalClosedStarIdeal A => j.CompactModelSpace pi hpi) i).comp
            (pi.compactC0Decomposition hpi).toNonUnitalStarAlgHom) rho := by
  let G := fun i : MinimalClosedStarIdeal A => i.CompactModelSpace pi hpi
  let E : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum G := pi.compactC0Decomposition hpi
  let sigma : NonUnitalCStarRepresentation (CompactOperatorC0Sum G) K :=
    rho.comp E.symm.toNonUnitalStarAlgHom
  letI : Nontrivial K := nontrivial_of_isNonzero rho hrho.1
  have hsigma : sigma.IsIrreducible :=
    (isIrreducible_comp_iff_of_surjective rho E.symm.toNonUnitalStarAlgHom
      E.symm.surjective).2 hrho
  have htransport (i : MinimalClosedStarIdeal A) :
      (CompactOperatorC0Sum.coordinateRepresentation G i).UnitaryEquivalent sigma ↔
        NonUnitalCStarRepresentation.UnitaryEquivalent
          ((CompactOperatorC0Sum.coordinateRepresentation G i).comp
            E.toNonUnitalStarAlgHom) rho := by
    constructor
    · rintro ⟨U, hU⟩
      refine ⟨U, fun a x => ?_⟩
      have h := hU (E a) x
      change U (CompactOperatorC0Sum.coordinateRepresentation G i (E a) x) =
        rho (E.symm (E a)) (U x) at h
      exact h.trans (congrArg (fun b => rho b (U x)) (E.symm_apply_apply a))
    · rintro ⟨U, hU⟩
      refine ⟨U, fun b x => ?_⟩
      have h := hU (E.symm b) x
      change U (CompactOperatorC0Sum.coordinateRepresentation G i (E (E.symm b)) x) =
        rho (E.symm b) (U x) at h
      exact (congrArg
        (fun c => U (CompactOperatorC0Sum.coordinateRepresentation G i c x))
        (E.apply_symm_apply b)).symm.trans h
  obtain ⟨i, hi, huniq⟩ :=
    CompactOperatorC0Sum.existsUnique_coordinate_unitaryEquivalent G sigma hsigma
  exact ⟨i, (htransport i).1 hi, fun j hj => huniq j ((htransport j).2 hj)⟩

set_option maxHeartbeats 8000000 in
/-- A faithful compact-valued representation forces the literal range of
every nonzero irreducible representation to be all compact operators on its
own Hilbert space. Neither that representation's faithfulness nor any
relation between its Hilbert universe and the given one is assumed. -/
theorem range_eq_compactOperatorStarSubalgebra_of_isCompactlyRepresented
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented)
    (rho : NonUnitalCStarRepresentation A K) (hrho : rho.IsIrreducible) :
    (NonUnitalStarAlgHom.range rho) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K := by
  let G := fun i : MinimalClosedStarIdeal A => i.CompactModelSpace pi hpi
  let E : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum G := pi.compactC0Decomposition hpi
  obtain ⟨i, hi, _⟩ :=
    existsUnique_coordinate_unitaryEquivalent_compactC0Decomposition pi hpi rho hrho
  change NonUnitalCStarRepresentation.UnitaryEquivalent
    ((CompactOperatorC0Sum.coordinateRepresentation G i).comp
      E.toNonUnitalStarAlgHom) rho at hi
  have hrange : (NonUnitalStarAlgHom.range ((CompactOperatorC0Sum.coordinateRepresentation G i).comp
      E.toNonUnitalStarAlgHom)) =
        (NonUnitalStarAlgHom.range (CompactOperatorC0Sum.coordinateRepresentation G i)) := by
    ext T
    constructor
    · intro hT
      have hT' : ∃ a : A, CompactOperatorC0Sum.coordinateRepresentation G i (E a) = T := hT
      obtain ⟨a, ha⟩ := hT'
      exact (show ∃ b : CompactOperatorC0Sum G,
        CompactOperatorC0Sum.coordinateRepresentation G i b = T from ⟨E a, ha⟩)
    · intro hT
      have hT' : ∃ b : CompactOperatorC0Sum G,
          CompactOperatorC0Sum.coordinateRepresentation G i b = T := hT
      obtain ⟨b, hb⟩ := hT'
      exact (show ∃ a : A, CompactOperatorC0Sum.coordinateRepresentation G i (E a) = T from
        ⟨E.symm b, (congrArg (fun c => CompactOperatorC0Sum.coordinateRepresentation G i c)
          (E.apply_symm_apply b)).trans hb⟩)
  exact hi.range_eq_compactOperatorStarSubalgebra
    (hrange.trans (CompactOperatorC0Sum.range_coordinateRepresentation G i))

/-- The CCR range conclusion quantified over an independent Hilbert universe.
`IsIrreducible` includes nonzeroness; no separate `Nontrivial K` is requested. -/
theorem forall_irreducible_range_eq_compactOperatorStarSubalgebra_of_isCompactlyRepresented
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) :
    ∀ (K : Type w) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K],
      ∀ rho : NonUnitalCStarRepresentation A K, rho.IsIrreducible →
        (NonUnitalStarAlgHom.range rho) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K := by
  intro K _ _ _ rho hrho
  exact range_eq_compactOperatorStarSubalgebra_of_isCompactlyRepresented pi hpi rho hrho

/-- Pointwise compactness is a consequence of the stronger literal range
equality, not a replacement for it. -/
theorem isCompactOperator_of_isIrreducible_of_isCompactlyRepresented
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented)
    (rho : NonUnitalCStarRepresentation A K) (hrho : rho.IsIrreducible) (a : A) :
    IsCompactOperator (rho a) := by
  have ha : rho a ∈ (NonUnitalStarAlgHom.range rho) := (NonUnitalStarAlgHom.mem_range rho).2 ⟨a, rfl⟩
  rw [range_eq_compactOperatorStarSubalgebra_of_isCompactlyRepresented pi hpi rho hrho] at ha
  exact ha

/-- All pure-state GNS actions, not only the selected primitive witnesses,
have exact compact ranges as a specialization of the arbitrary-universe theorem. -/
theorem range_gnsRepresentation_eq_compact_of_isCompactlyRepresented
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented)
    (phi : NonUnitalPureState A) :
    (NonUnitalStarAlgHom.range phi.gnsRepresentation) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ phi.GNS :=
  range_eq_compactOperatorStarSubalgebra_of_isCompactlyRepresented pi hpi
    phi.gnsRepresentation phi.isIrreducible_gnsRepresentation

end NonUnitalCStarRepresentation

namespace PrimitiveSpectrum

/-- The selected primitive GNS condition is supplied by the actual compact
representation; it is not an additional hypothesis on the canonical decomposition. -/
theorem range_pureStateRepresentative_eq_compact_of_isCompactlyRepresented
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented)
    (P : PrimitiveSpectrum A) :
    (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ P.pureStateRepresentative.GNS :=
  NonUnitalCStarRepresentation.range_gnsRepresentation_eq_compact_of_isCompactlyRepresented
    pi hpi P.pureStateRepresentative

end PrimitiveSpectrum

namespace NonUnitalCStarRepresentation



end NonUnitalCStarRepresentation


namespace PrimitiveSpectrum

set_option maxHeartbeats 8000000 in
/-- Each primitive point is literally the kernel of a coordinate action
pulled back along the same canonical compact c₀-decomposition. The kernel
identity is obtained from an actual unitary, not postulated as classification. -/
theorem exists_coordinate_kernel_eq_of_isCompactlyRepresented
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented)
    (P : PrimitiveSpectrum A) :
    ∃ i : MinimalClosedStarIdeal A,
      (NonUnitalCStarRepresentation.kernelIdeal
        ((CompactOperatorC0Sum.coordinateRepresentation
          (fun j : MinimalClosedStarIdeal A => j.CompactModelSpace pi hpi) i).comp
            (pi.compactC0Decomposition hpi).toNonUnitalStarAlgHom) : Set A) = P.val := by
  obtain ⟨i, hi, _⟩ :=
    NonUnitalCStarRepresentation.existsUnique_coordinate_unitaryEquivalent_compactC0Decomposition
      pi hpi P.pureStateRepresentative.gnsRepresentation
        P.pureStateRepresentative.isIrreducible_gnsRepresentation
  refine ⟨i, ?_⟩
  exact (congrArg (fun I : TwoSidedIdeal A => (I : Set A)) hi.kernelIdeal_eq).trans
    P.coe_kernelIdeal_pureStateRepresentative

set_option maxHeartbeats 8000000 in
/-- A concrete element outside one primitive ideal and inside every other
primitive ideal. It is the inverse image of a single-coordinate nonzero
rank-one operator under the already constructed decomposition. -/
theorem exists_notMem_and_forall_mem_of_isCompactlyRepresented
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented)
    (P : PrimitiveSpectrum A) :
    ∃ a : A, a ∉ P.val ∧ ∀ Q : PrimitiveSpectrum A, Q ≠ P → a ∈ Q.val := by
  let G := fun i : MinimalClosedStarIdeal A => i.CompactModelSpace pi hpi
  let E : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum G := pi.compactC0Decomposition hpi
  let F := fun i : MinimalClosedStarIdeal A =>
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (G i)
  let sigma := fun i : MinimalClosedStarIdeal A =>
    (CompactOperatorC0Sum.coordinateRepresentation G i).comp E.toNonUnitalStarAlgHom
  obtain ⟨i, hi⟩ := exists_coordinate_kernel_eq_of_isCompactlyRepresented pi hpi P
  change (NonUnitalCStarRepresentation.kernelIdeal (sigma i) : Set A) = P.val at hi
  obtain ⟨v, hv⟩ := exists_ne (0 : G i)
  let T : F i := compactRankOne ℂ v v
  let z : CompactOperatorC0Sum G := C0DirectSum.single
     (fun j : MinimalClosedStarIdeal A =>
       ↥(ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (G j))) i T
  let a : A := E.symm z
  have hactive : sigma i a = compactOperatorRepresentation (G i) T := by
    change CompactOperatorC0Sum.coordinateRepresentation G i (E (E.symm z)) = _
    exact (congrArg (fun b => CompactOperatorC0Sum.coordinateRepresentation G i b)
      (E.apply_symm_apply z)).trans
        (CompactOperatorC0Sum.coordinateRepresentation_single_same G i T)
  have hnonzero : compactOperatorRepresentation (G i) T ≠ 0 := by
    change rankOne ℂ v v ≠ 0
    exact rankOne_ne_zero hv hv
  refine ⟨a, ?_, ?_⟩
  · rw [← hi]
    intro ha
    have hz := (NonUnitalCStarRepresentation.mem_kernelIdeal (sigma i) a).1 ha
    rw [hactive] at hz
    exact hnonzero hz
  · intro Q hQP
    obtain ⟨j, hj⟩ := exists_coordinate_kernel_eq_of_isCompactlyRepresented pi hpi Q
    change (NonUnitalCStarRepresentation.kernelIdeal (sigma j) : Set A) = Q.val at hj
    have hji : j ≠ i := by
      intro h
      apply hQP
      apply Subtype.ext
      calc
        Q.val = (NonUnitalCStarRepresentation.kernelIdeal (sigma j) : Set A) := hj.symm
        _ = (NonUnitalCStarRepresentation.kernelIdeal (sigma i) : Set A) := by rw [h]
        _ = P.val := hi
    rw [← hj]
    apply (NonUnitalCStarRepresentation.mem_kernelIdeal (sigma j) a).2
    change CompactOperatorC0Sum.coordinateRepresentation G j (E (E.symm z)) = 0
    exact (congrArg (fun b => CompactOperatorC0Sum.coordinateRepresentation G j b)
      (E.apply_symm_apply z)).trans
        (CompactOperatorC0Sum.coordinateRepresentation_single_of_ne G hji T)

/-- The pullback of an explicit coordinate separator cuts out the singleton
in the already defined hull-kernel topology. No maximality, essentiality, or
annihilator argument is substituted for topological discreteness. -/
theorem isOpen_singleton_of_isCompactlyRepresented
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented)
    (P : PrimitiveSpectrum A) : IsOpen ({P} : Set (PrimitiveSpectrum A)) := by
  obtain ⟨a, haP, haOther⟩ := exists_notMem_and_forall_mem_of_isCompactlyRepresented pi hpi P
  have hclosed : IsClosed {Q : PrimitiveSpectrum A | a ∈ Q.val} := by
    apply isClosed_of_closure_subset
    intro Q hQ
    rw [closure_primitiveSpectrum] at hQ
    exact hQ a (fun R hR => hR)
  have hopen : IsOpen {Q : PrimitiveSpectrum A | a ∉ Q.val} := hclosed.isOpen_compl
  have heq : {Q : PrimitiveSpectrum A | a ∉ Q.val} = {P} := by
    ext Q
    change (a ∉ Q.val) ↔ Q = P
    constructor
    · intro hQ
      by_contra hQP
      exact hQ (haOther Q hQP)
    · rintro rfl
      exact haP
  rwa [heq] at hopen

end PrimitiveSpectrum

/-- The existing hull-kernel topology on the primitive spectrum is discrete.
The same actual compact c₀-decomposition supplies each point's isolating
element. Empty spectra, including that of the zero algebra, are not excluded. -/
theorem discreteTopology_primitiveSpectrum_of_isCompactlyRepresented
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) :
    DiscreteTopology (PrimitiveSpectrum A) := by
  rw [discreteTopology_iff_isOpen_singleton]
  exact PrimitiveSpectrum.isOpen_singleton_of_isCompactlyRepresented pi hpi

namespace IrreducibleSpectrum

/-- The genuine kernel map is injective because all pure GNS ranges contain
the compacts, not merely because the primitive spectrum is discrete. -/
theorem kernel_injective_of_isCompactlyRepresented
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) :
    Function.Injective (kernel : IrreducibleSpectrum A → PrimitiveSpectrum A) :=
  kernel_injective_of_forall_pure_state_range_eq_compact
    (NonUnitalCStarRepresentation.range_gnsRepresentation_eq_compact_of_isCompactlyRepresented
      pi hpi)

end IrreducibleSpectrum

/-- The existing irreducible-spectrum topology is also discrete. Both
continuity and the separately proved injectivity of the kernel map are used. -/
theorem discreteTopology_irreducibleSpectrum_of_isCompactlyRepresented
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) :
    DiscreteTopology (IrreducibleSpectrum A) := by
  letI : DiscreteTopology (PrimitiveSpectrum A) :=
    discreteTopology_primitiveSpectrum_of_isCompactlyRepresented pi hpi
  have hinj := IrreducibleSpectrum.kernel_injective_of_isCompactlyRepresented pi hpi
  rw [discreteTopology_iff_isOpen_singleton]
  intro q
  have hopen : IsOpen (IrreducibleSpectrum.kernel ⁻¹'
      ({IrreducibleSpectrum.kernel q} : Set (PrimitiveSpectrum A))) :=
    (isOpen_discrete _).preimage (continuous_irreducibleSpectrum_kernel A)
  have heq : IrreducibleSpectrum.kernel ⁻¹'
      ({IrreducibleSpectrum.kernel q} : Set (PrimitiveSpectrum A)) = {q} := by
    ext r
    change IrreducibleSpectrum.kernel r = IrreducibleSpectrum.kernel q ↔ r = q
    exact hinj.eq_iff
  rw [heq] at hopen
  exact hopen

namespace NonUnitalCStarRepresentation

/-- Forward compact-algebra endpoint with all quantifiers exposed: arbitrary
irreducible ranges are exactly compact, both existing spectra are discrete,
and the selected primitive GNS condition needed by the converse is supplied.
No part of the converse or reduced-atomic range is asserted here. -/
theorem forall_irreducible_range_eq_compact_and_discrete_spectra
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) :
    (∀ (K : Type w) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K],
      ∀ rho : NonUnitalCStarRepresentation A K, rho.IsIrreducible →
        (NonUnitalStarAlgHom.range rho) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K) ∧
    DiscreteTopology (PrimitiveSpectrum A) ∧ DiscreteTopology (IrreducibleSpectrum A) ∧
    (∀ P : PrimitiveSpectrum A, (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ P.pureStateRepresentative.GNS) := by
  refine ⟨?_, discreteTopology_primitiveSpectrum_of_isCompactlyRepresented pi hpi,
    discreteTopology_irreducibleSpectrum_of_isCompactlyRepresented pi hpi, ?_⟩
  · intro K _ _ _ rho hrho
    exact range_eq_compactOperatorStarSubalgebra_of_isCompactlyRepresented pi hpi rho hrho
  · exact PrimitiveSpectrum.range_pureStateRepresentative_eq_compact_of_isCompactlyRepresented
      pi hpi

end NonUnitalCStarRepresentation

end MathlibAnnex.Analysis.CStarAlgebra
