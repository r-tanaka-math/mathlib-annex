/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.CompactDimensionTransport
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.CompactTrichotomyTransport
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartClassification
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartUnitaryInvariance
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactIdealRigidity

/-!
# Rigidity of a bounded-operator target from its geometric structure space

The source algebra is the actual full operator algebra, represented as the top
non-unital star subalgebra.  A specified full GSS homeomorphism is first
restricted, through the SAME faithful pure-state image supplied by the existing
transport theorem, to a homeomorphism of normal parts.  Finite dimension uses
the existing finite-dimensional comparison and irreducible-range theorem.
Infinite dimension uses both directions of the specified homeomorphism in the
selected-pair classification, so that the resulting sandwich has equality of
operator images rather than only inclusion.

No type-I-factor provider and no Glimm--Sakai equivalence is used here.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v uI uJ
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι : Type uI} {κ : Type uJ}

attribute [local instance] HomKernelQuotient.imageCStarAlgebra
  HomKernelQuotient.isClosed_image

namespace NonUnitalCStarRepresentation

universe w
variable {A : Type w} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]

/-- An actual unitary intertwiner transports literal full operator range.
This is stronger than transport of compact containment and uses no
faithfulness hypothesis beyond the supplied range equality. -/
theorem UnitaryEquivalent.range_eq_top_of_range_eq_top
    {pi : NonUnitalCStarRepresentation A H} {rho : NonUnitalCStarRepresentation A K}
    (h : pi.UnitaryEquivalent rho) (hpi : (NonUnitalStarAlgHom.range pi) = ⊤) : (NonUnitalStarAlgHom.range rho) = ⊤ := by
  obtain ⟨U, hU⟩ := h
  apply SetLike.ext
  intro T
  constructor
  · intro _
    trivial
  · intro _
    let R : H →L[ℂ] H := U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      T ∘L U.toContinuousLinearEquiv.toContinuousLinearMap
    have hR : R ∈ (NonUnitalStarAlgHom.range pi) := by rw [hpi]; trivial
    obtain ⟨a, ha⟩ := (NonUnitalStarAlgHom.mem_range pi).1 hR
    apply (NonUnitalStarAlgHom.mem_range rho).2
    refine ⟨a, ?_⟩
    ext y
    calc
      rho a y = U (pi a (U.symm y)) := by
        simpa using (hU a (U.symm y)).symm
      _ = T y := by rw [ha]; simp [R]

/-- Full operator range is invariant under an actual unitary equivalence. -/
theorem UnitaryEquivalent.range_eq_top_iff
    {pi : NonUnitalCStarRepresentation A H} {rho : NonUnitalCStarRepresentation A K}
    (h : pi.UnitaryEquivalent rho) : (NonUnitalStarAlgHom.range pi) = ⊤ ↔ (NonUnitalStarAlgHom.range rho) = ⊤ :=
  ⟨h.range_eq_top_of_range_eq_top, h.symm.range_eq_top_of_range_eq_top⟩

end NonUnitalCStarRepresentation

local instance : IsClosed
    ((⊤ : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H)) := by
  change IsClosed (Set.univ : Set (H →L[ℂ] H))
  exact isClosed_univ

/-- The inclusion action of the actual top operator algebra is irreducible. -/
theorem isIrreducible_subtype_top [Nontrivial H] :
    NonUnitalCStarRepresentation.IsIrreducible
      (A := ↥(⊤ : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))) (H := H)
      (NonUnitalStarSubalgebraClass.subtype
        (⊤ : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))) := by
  obtain ⟨hne, hreduce⟩ := isIrreducible_operatorIdentityRepresentation (H := H)
  constructor
  · obtain ⟨a, ha⟩ := hne
    refine ⟨⟨a, by trivial⟩, ?_⟩
    change a ≠ 0
    simpa only [operatorIdentityRepresentation_apply] using ha
  · intro L hL
    apply hreduce L
    refine ⟨hL.1, ?_⟩
    intro a x hx
    change a x ∈ L ∧ ContinuousLinearMap.adjoint a x ∈ L
    exact hL.2 ⟨a, by trivial⟩ x hx

set_option backward.isDefEq.respectTransparency false in
/-- If the image of a bounded linear adjoint sandwich on `T` is the whole
operator algebra, then `T` itself is the whole target operator algebra. -/
theorem eq_top_of_image_adjointSandwich_eq_top
    (T : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K))
    (U V : H ≃L[ℂ] K)
    (hEq : InnerProductSpace.adjointSandwich U.toContinuousLinearMap
      V.toContinuousLinearMap '' (T : Set (K →L[ℂ] K)) =
        ((⊤ : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H))) :
    T = ⊤ := by
  apply SetLike.ext
  intro b
  constructor
  · intro _
    trivial
  · intro _
    have hb : InnerProductSpace.adjointSandwich U.toContinuousLinearMap
        V.toContinuousLinearMap b ∈
          ((⊤ : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H)) := by
      trivial
    rw [← hEq] at hb
    obtain ⟨a, ha, hab⟩ := hb
    have hab' := congrArg
      (InnerProductSpace.adjointSandwich U.symm.toContinuousLinearMap
        V.symm.toContinuousLinearMap) hab
    have heq : a = b := by
      simpa only [InnerProductSpace.adjointSandwich_symm_apply] using hab'
    change b ∈ (T : Set (K →L[ℂ] K))
    simpa only [heq] using ha

set_option backward.isDefEq.respectTransparency false in
/-- The same conclusion for a bounded conjugate-linear pair. -/
theorem eq_top_of_image_conjugateAdjointSandwich_eq_top
    (T : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K))
    (U V : H ≃SL[starRingEnd ℂ] K)
    (hEq : InnerProductSpace.conjugateAdjointSandwich U.toContinuousLinearMap
      V.toContinuousLinearMap '' (T : Set (K →L[ℂ] K)) =
        ((⊤ : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H))) :
    T = ⊤ := by
  apply SetLike.ext
  intro b
  constructor
  · intro _
    trivial
  · intro _
    have hb : InnerProductSpace.conjugateAdjointSandwich U.toContinuousLinearMap
        V.toContinuousLinearMap b ∈
          ((⊤ : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H)) := by
      trivial
    rw [← hEq] at hb
    obtain ⟨a, ha, hab⟩ := hb
    have hab' := congrArg
      (InnerProductSpace.conjugateAdjointSandwich U.symm.toContinuousLinearMap
        V.symm.toContinuousLinearMap) hab
    have heq : a = b := by
      simpa only [InnerProductSpace.conjugateAdjointSandwich_symm_apply] using hab'
    change b ∈ (T : Set (K →L[ℂ] K))
    simpa only [heq] using ha

section NormalPart

variable [Nontrivial H] [Nontrivial K]
variable (T : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K))
variable [IsClosed (T : Set (K →L[ℂ] K))]
variable (hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T))

local instance : NonUnitalCStarAlgebra T :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra T (h_closed := inferInstance)
local instance : PartialOrder T := _root_.CStarAlgebra.spectralOrder T
local instance : StarOrderedRing T := _root_.CStarAlgebra.spectralOrderedRing T

include hT in
/-- A full normal-part homeomorphism from the actual `B(H)` forces the target
concrete irreducible algebra to be all of `B(K)`.  The finite branch does not
use projective dimension at least three; the infinite branch uses both full
continuities of this SAME homeomorphism. -/
theorem eq_top_of_normalPart_homeomorph
    (e : ClosureSpace.Homeomorph
      ((NormedSpace.geometricStructureClosure ℂ
        (⊤ : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))).subspace
          (normalPart (⊤ : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))))
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T))) :
    T = ⊤ := by
  let S := (⊤ : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
  letI : IsClosed (S : Set (H →L[ℂ] H)) := by
    change IsClosed (Set.univ : Set (H →L[ℂ] H))
    exact isClosed_univ
  have hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S) :=
    isIrreducible_subtype_top (H := H)
  by_cases hfinite : FiniteDimensional ℂ H
  · letI : FiniteDimensional ℂ H := hfinite
    have hK : FiniteDimensional ℂ K :=
      (finite_iff_of_normalPart_finiteHomeomorph S T hS hT
        e.toFiniteHomeomorph).1 hfinite
    letI : FiniteDimensional ℂ K := hK
    exact eq_top_of_isIrreducible_subtype_of_finiteDimensional T hT
  · rcases (exists_normalPart_selected_operator_eq S T hS hT
      e.toFiniteHomeomorph hfinite e.continuous_toFun e.continuous_invFun).2 with
      ⟨U, V, _, _, _, _, _orientation, hEq⟩ |
      ⟨U, V, _, _, _, _, _orientation, hEq⟩
    · exact eq_top_of_image_adjointSandwich_eq_top T U V hEq
    · exact eq_top_of_image_conjugateAdjointSandwich_eq_top T U V hEq

include hT in
/-- The full GSS version uses the SAME faithful target image furnished by
`exists_faithful_normalPart_transport`.  The final unitary returns literal
full range to the original target action; no second faithful representation
of `T` is selected. -/
theorem eq_top_of_geometricStructure_homeomorph
    (e : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ
        (⊤ : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)))
      (NormedSpace.geometricStructureClosure ℂ T)) :
    T = ⊤ := by
  let S := (⊤ : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
  letI : IsClosed (S : Set (H →L[ℂ] H)) := by
    change IsClosed (Set.univ : Set (H →L[ℂ] H))
    exact isClosed_univ
  have hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S) :=
    isIrreducible_subtype_top (H := H)
  obtain ⟨phi, hfaith, r, _hpre, _hinv, himage⟩ :=
    exists_faithful_normalPart_transport S hS e
  have hR : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype
      (NonUnitalStarAlgHom.range phi.gnsRepresentation)) :=
    (NonUnitalCStarRepresentation.isIrreducible_imageRepresentation_iff
      phi.gnsRepresentation).2 phi.isIrreducible_gnsRepresentation
  letI : Nontrivial phi.GNS :=
    NonUnitalCStarRepresentation.nontrivial_of_isNonzero
      phi.gnsRepresentation phi.isIrreducible_gnsRepresentation.1
  let f := normalPartHomeomorphOfImage (e.trans r.symm) himage
  have hRtop : (NonUnitalStarAlgHom.range phi.gnsRepresentation) = ⊤ :=
    eq_top_of_normalPart_homeomorph (NonUnitalStarAlgHom.range phi.gnsRepresentation) hR f
  have hker : NonUnitalCStarRepresentation.kernelIdeal phi.gnsRepresentation =
      NonUnitalCStarRepresentation.kernelIdeal
        (NonUnitalStarSubalgebraClass.subtype T) := by
    ext a
    constructor
    · intro ha
      have hz : phi.gnsRepresentation a = 0 :=
        (NonUnitalCStarRepresentation.mem_kernelIdeal phi.gnsRepresentation a).1 ha
      have ha0 : a = 0 := hfaith (by simpa only [map_zero] using hz)
      subst a
      exact (NonUnitalCStarRepresentation.mem_kernelIdeal
        (NonUnitalStarSubalgebraClass.subtype T) 0).2 (map_zero _)
    · intro ha
      have hz : (a : K →L[ℂ] K) = 0 :=
        (NonUnitalCStarRepresentation.mem_kernelIdeal
          (NonUnitalStarSubalgebraClass.subtype T) a).1 ha
      have ha0 : a = 0 := Subtype.ext hz
      subst a
      exact (NonUnitalCStarRepresentation.mem_kernelIdeal
        phi.gnsRepresentation 0).2 (map_zero _)
  have hcompact : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ phi.GNS ≤
      (NonUnitalStarAlgHom.range phi.gnsRepresentation) := by rw [hRtop]; exact le_top
  have hU :=
    NonUnitalCStarRepresentation.unitaryEquivalent_of_kernelIdeal_eq_of_compact_le_range
      phi.gnsRepresentation (NonUnitalStarSubalgebraClass.subtype T)
      hT hker hcompact
  have hsub : (NonUnitalStarAlgHom.range (NonUnitalStarSubalgebraClass.subtype T)) = T := by
    apply le_antisymm
    · intro a ha
      obtain ⟨b, rfl⟩ := (NonUnitalStarAlgHom.mem_range
        (NonUnitalStarSubalgebraClass.subtype T)).1 ha
      exact b.property
    · intro a ha
      exact (NonUnitalStarAlgHom.mem_range
        (NonUnitalStarSubalgebraClass.subtype T)).2 ⟨⟨a, ha⟩, rfl⟩
  exact hsub.symm.trans (hU.range_eq_top_of_range_eq_top hRtop)

include hT in
/-- Arbitrary Hilbert bases of the two concrete actions have equivalent index
types.  This is the actual Hilbert dimension comparison, not Hamel rank or
`finrank` in an infinite-dimensional space. -/
theorem nonempty_hilbertBasis_index_equiv_of_geometricStructure_homeomorph
    (e : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ
        (⊤ : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)))
      (NormedSpace.geometricStructureClosure ℂ T))
    (b : HilbertBasis ι ℂ H)
    (c : HilbertBasis κ ℂ K) : Nonempty (ι ≃ κ) := by
  let S := (⊤ : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
  letI : IsClosed (S : Set (H →L[ℂ] H)) := by
    change IsClosed (Set.univ : Set (H →L[ℂ] H))
    exact isClosed_univ
  have hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S) :=
    isIrreducible_subtype_top (H := H)
  exact Cardinal.lift_mk_eq'.mp
    (hilbertBasis_lift_mk_eq_of_geometricStructure_homeomorph_of_compact_le
      S T hS hT e (Or.inl le_top) b c)

include hT in
/-- The specified full GSS homeomorphism yields an actual unitary equivalence
of the Hilbert spaces.  It is constructed by reindexing the two actual
Hilbert-basis coordinate spaces. -/
theorem nonempty_linearIsometryEquiv_of_geometricStructure_homeomorph
    (e : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ
        (⊤ : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)))
      (NormedSpace.geometricStructureClosure ℂ T)) :
    Nonempty (H ≃ₗᵢ[ℂ] K) := by
  obtain ⟨ι, b, _hb⟩ := exists_hilbertBasis ℂ H
  obtain ⟨κ, c, _hc⟩ := exists_hilbertBasis ℂ K
  obtain ⟨q⟩ :=
    nonempty_hilbertBasis_index_equiv_of_geometricStructure_homeomorph
      T hT e b c
  let d : HilbertBasis ι ℂ K :=
    HilbertBasis.mk (c.orthonormal.comp q q.injective) (by
      rw [q.surjective.range_comp]
      exact c.dense_span.ge)
  exact ⟨b.repr.trans d.repr.symm⟩

end NormalPart

end MathlibAnnex.Analysis.CStarAlgebra
