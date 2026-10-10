/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.FaithfulNormalPart
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartCompactComparison
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactIdealRigidity
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactTrichotomy
import MathlibAnnex.Topology.ClosureSpace.SubspaceMaps

/-!
# Transport of the local compact trichotomy by a full GSS homeomorphism

This file proves the operator-algebra alternatives used in Theorem 8.9.  The
specified full homeomorphism is not replaced.  The target is represented once
by the faithful pure-state image supplied by `exists_faithful_normalPart_transport`,
and the same literal preimage map is used throughout.

The local Blackadar alternative is imported from
`Representation/CompactTrichotomy.lean`; it is not reproved here.  Equality
with the compact algebra uses both directions of the actual normal-part
homeomorphism.  One-way continuity is used only for compact containment.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Set

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type w} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

attribute [local instance] HomKernelQuotient.imageCStarAlgebra
  HomKernelQuotient.isClosed_image

/-- Restrict a full GSS homeomorphism to normal parts once its actual image is known. -/
def normalPartHomeomorphOfImage
    {S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)}
    {T : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K)}
    (e : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ S)
      (NormedSpace.geometricStructureClosure ℂ T))
    (himage : e.toEquiv '' normalPart S = normalPart T) :
    ClosureSpace.Homeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) :=
  e.subspace (normalPart S) (normalPart T) fun I => by
    constructor
    · intro hI
      rw [← himage]
      exact ⟨I, hI, rfl⟩
    · intro hI
      rw [← himage] at hI
      obtain ⟨J, hJ, hJI⟩ := hI
      exact (e.toEquiv.injective hJI) ▸ hJ

@[simp]
theorem normalPartHomeomorphOfImage_apply
    {S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)}
    {T : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K)}
    (e : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ S)
      (NormedSpace.geometricStructureClosure ℂ T))
    (himage : e.toEquiv '' normalPart S = normalPart T)
    (I : normalPart S) :
    ((normalPartHomeomorphOfImage e himage).toEquiv I).val = e.toEquiv I.val := rfl

@[simp]
theorem normalPartHomeomorphOfImage_symm_apply
    {S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)}
    {T : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K)}
    (e : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ S)
      (NormedSpace.geometricStructureClosure ℂ T))
    (himage : e.toEquiv '' normalPart S = normalPart T)
    (J : normalPart T) :
    ((normalPartHomeomorphOfImage e himage).toEquiv.symm J).val =
      e.toEquiv.symm J.val := rfl

section NormalPart

variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable (T : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K))
variable [IsClosed (S : Set (H →L[ℂ] H))] [IsClosed (T : Set (K →L[ℂ] K))]
variable (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
variable (hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T))
variable (e : ClosureSpace.Homeomorph
  ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
  ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)))

include hS hT e in
/-- Compact containment is invariant under an actual full normal-part homeomorphism.
Only the forward continuity of the relevant direction is used in each implication. -/
theorem compactOperatorStarSubalgebra_le_iff_of_normalPart_homeomorph :
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ S ↔
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K ≤ T := by
  letI : Nontrivial H :=
    NonUnitalCStarRepresentation.nontrivial_of_isNonzero
      (NonUnitalStarSubalgebraClass.subtype S) hS.1
  letI : Nontrivial K :=
    NonUnitalCStarRepresentation.nontrivial_of_isNonzero
      (NonUnitalStarSubalgebraClass.subtype T) hT.1
  constructor
  · intro hcompact
    let f := e.symm.toFiniteHomeomorph.trans
      (normalPartToCompactFiniteHomeomorph S hS)
    have hf :
        ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).Continuous
          (NormedSpace.geometricStructureClosure ℂ
            (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H)) f.toEquiv :=
      (continuous_normalPartToCompactFiniteHomeomorph S hS hcompact).comp
        e.continuous_invFun
    exact compactOperatorStarSubalgebra_le_of_continuous_finiteHomeomorph T hT f hf
  · intro hcompact
    let f := e.toFiniteHomeomorph.trans
      (normalPartToCompactFiniteHomeomorph T hT)
    have hf :
        ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
          (NormedSpace.geometricStructureClosure ℂ
            (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K)) f.toEquiv :=
      (continuous_normalPartToCompactFiniteHomeomorph T hT hcompact).comp
        e.continuous_toFun
    exact compactOperatorStarSubalgebra_le_of_continuous_finiteHomeomorph S hS f hf

include hS hT e in
/-- Equality with the compact algebra is invariant under a full normal-part homeomorphism.
This statement uses both continuous directions of the specified map. -/
theorem eq_compactOperatorStarSubalgebra_iff_of_normalPart_homeomorph :
    S = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ↔
      T = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K := by
  letI : Nontrivial H :=
    NonUnitalCStarRepresentation.nontrivial_of_isNonzero
      (NonUnitalStarSubalgebraClass.subtype S) hS.1
  letI : Nontrivial K :=
    NonUnitalCStarRepresentation.nontrivial_of_isNonzero
      (NonUnitalStarSubalgebraClass.subtype T) hT.1
  constructor
  · intro hcompact
    subst S
    have f : ClosureSpace.Homeomorph
        ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T))
        (NormedSpace.geometricStructureClosure ℂ
          (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H)) :=
      e.symm.trans (compactNormalPartHomeomorph (H := H))
    exact eq_compactOperatorStarSubalgebra_of_homeomorph T hT f
  · intro hcompact
    subst T
    have f : ClosureSpace.Homeomorph
        ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
        (NormedSpace.geometricStructureClosure ℂ
          (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K)) :=
      e.trans (compactNormalPartHomeomorph (H := K))
    exact eq_compactOperatorStarSubalgebra_of_homeomorph S hS f

include hS hT e in
/-- The proper compact-containing alternative is invariant as well. -/
theorem compactOperatorStarSubalgebra_lt_iff_of_normalPart_homeomorph :
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H < S ↔
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K < T := by
  have hle := compactOperatorStarSubalgebra_le_iff_of_normalPart_homeomorph S T hS hT e
  have heq := eq_compactOperatorStarSubalgebra_iff_of_normalPart_homeomorph S T hS hT e
  constructor
  · intro h
    refine lt_of_le_of_ne (hle.mp h.le) ?_
    intro hEq
    have hScompact : S = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H :=
      heq.mpr hEq.symm
    exact h.ne hScompact.symm
  · intro h
    refine lt_of_le_of_ne (hle.mpr h.le) ?_
    intro hEq
    have hTcompact : T = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K :=
      heq.mp hEq.symm
    exact h.ne hTcompact.symm

include hS in
/-- The zero compact-intersection alternative is the negation of compact containment. -/
theorem forall_compact_eq_zero_iff_not_compactOperatorStarSubalgebra_le
    (hclosed : IsClosed (S : Set (H →L[ℂ] H))) :
    (∀ a : H →L[ℂ] H, a ∈ S → IsCompactOperator a → a = 0) ↔
      ¬ ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ S := by
  letI : Nontrivial H :=
    NonUnitalCStarRepresentation.nontrivial_of_isNonzero
      (NonUnitalStarSubalgebraClass.subtype S) hS.1
  constructor
  · intro hzero hle
    obtain ⟨a, ha⟩ := (isIrreducible_compactOperatorRepresentation H).1
    have hz : a.val = 0 := hzero a.val (hle a.property) a.property
    exact ha hz
  · intro hnot a haS haK
    by_contra ha0
    exact hnot (compactOperatorStarSubalgebra_le_of_exists_nonzero_compact
      S hclosed hS ⟨a, haS, haK, ha0⟩)

include hS hT e in
/-- The carrier-level zero compact-intersection alternative is invariant. -/
theorem forall_compact_eq_zero_iff_of_normalPart_homeomorph
    (hclosedS : IsClosed (S : Set (H →L[ℂ] H)))
    (hclosedT : IsClosed (T : Set (K →L[ℂ] K))) :
    (∀ a : H →L[ℂ] H, a ∈ S → IsCompactOperator a → a = 0) ↔
      ∀ b : K →L[ℂ] K, b ∈ T → IsCompactOperator b → b = 0 := by
  rw [forall_compact_eq_zero_iff_not_compactOperatorStarSubalgebra_le
      S hS hclosedS,
    forall_compact_eq_zero_iff_not_compactOperatorStarSubalgebra_le
      T hT hclosedT,
    compactOperatorStarSubalgebra_le_iff_of_normalPart_homeomorph S T hS hT e]

include hS hT e in
/-- Literal bottom-ideal form of zero compact-intersection transport. -/
theorem compactIntersectionIdeal_eq_bot_iff_of_normalPart_homeomorph
    (hclosedS : IsClosed (S : Set (H →L[ℂ] H)))
    (hclosedT : IsClosed (T : Set (K →L[ℂ] K))) :
    compactIntersectionIdeal S hclosedS hS = ⊥ ↔
      compactIntersectionIdeal T hclosedT hT = ⊥ := by
  rw [compactIntersectionIdeal_eq_bot_iff S hclosedS hS,
    compactIntersectionIdeal_eq_bot_iff T hclosedT hT,
    forall_compact_eq_zero_iff_of_normalPart_homeomorph
      S T hS hT e hclosedS hclosedT]

end NormalPart

section FaithfulImage

variable (T : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K))
variable [hclosedT : IsClosed (T : Set (K →L[ℂ] K))]
local instance : NonUnitalCStarAlgebra T :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra T (h_closed := hclosedT)
local instance : PartialOrder T := _root_.CStarAlgebra.spectralOrder T
local instance : StarOrderedRing T := _root_.CStarAlgebra.spectralOrderedRing T
variable (hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T))
variable (rho : NonUnitalCStarRepresentation T L)
variable (hrho : rho.IsIrreducible)
variable (hinj : Function.Injective rho)

include hclosedT hT hrho hinj in
/-- A faithful irreducible image preserves and reflects compact containment.
The comparison is the actual unitary from compact-ideal rigidity. -/
theorem compactOperatorStarSubalgebra_le_iff_range_of_injective :
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K ≤ T ↔
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ L ≤ (NonUnitalStarAlgHom.range rho) := by
  constructor
  · intro hcompact
    letI : Nontrivial K :=
      NonUnitalCStarRepresentation.nontrivial_of_isNonzero
        (NonUnitalStarSubalgebraClass.subtype T) hT.1
    have hU := unitaryEquivalent_inclusion_of_injective
      T hclosedT hcompact rho hrho hinj
    have hRange : (NonUnitalStarAlgHom.range (NonUnitalStarSubalgebraClass.subtype T)) = T := by
      apply le_antisymm
      · intro a ha
        obtain ⟨b, rfl⟩ := (NonUnitalStarAlgHom.mem_range
          (NonUnitalStarSubalgebraClass.subtype T)).1 ha
        exact b.property
      · intro a ha
        exact (NonUnitalStarAlgHom.mem_range
          (NonUnitalStarSubalgebraClass.subtype T)).2 ⟨⟨a, ha⟩, rfl⟩
    exact hU.compactOperatorStarSubalgebra_le_range (hcompact.trans hRange.ge)
  · intro hcompact
    have hker : NonUnitalCStarRepresentation.kernelIdeal rho =
        NonUnitalCStarRepresentation.kernelIdeal
          (NonUnitalStarSubalgebraClass.subtype T) := by
      apply le_antisymm
      · intro a ha
        have hz : rho a = 0 :=
          (NonUnitalCStarRepresentation.mem_kernelIdeal rho a).1 ha
        have : a = 0 := hinj (by simpa only [map_zero] using hz)
        subst a
        exact (NonUnitalCStarRepresentation.mem_kernelIdeal
          (NonUnitalStarSubalgebraClass.subtype T) 0).2 (map_zero _)
      · intro a ha
        have hz : (a : K →L[ℂ] K) = 0 :=
          (NonUnitalCStarRepresentation.mem_kernelIdeal
            (NonUnitalStarSubalgebraClass.subtype T) a).1 ha
        have : a = 0 := Subtype.ext hz
        subst a
        exact (NonUnitalCStarRepresentation.mem_kernelIdeal rho 0).2 (map_zero _)
    have hU := NonUnitalCStarRepresentation.unitaryEquivalent_of_kernelIdeal_eq_of_compact_le_range
      rho (NonUnitalStarSubalgebraClass.subtype T) hT hker hcompact
    have hRange : (NonUnitalStarAlgHom.range (NonUnitalStarSubalgebraClass.subtype T)) = T := by
      apply le_antisymm
      · intro a ha
        obtain ⟨b, rfl⟩ := (NonUnitalStarAlgHom.mem_range
          (NonUnitalStarSubalgebraClass.subtype T)).1 ha
        exact b.property
      · intro a ha
        exact (NonUnitalStarAlgHom.mem_range
          (NonUnitalStarSubalgebraClass.subtype T)).2 ⟨⟨a, ha⟩, rfl⟩
    exact (hU.compactOperatorStarSubalgebra_le_range hcompact).trans hRange.le

include hclosedT hT hrho hinj in
/-- A faithful irreducible image preserves and reflects equality with the compact algebra. -/
theorem eq_compactOperatorStarSubalgebra_iff_range_of_injective :
    T = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K ↔
      (NonUnitalStarAlgHom.range rho) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ L := by
  constructor
  · intro hEq
    have hcompact : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K ≤ T := hEq.ge
    letI : Nontrivial K :=
      NonUnitalCStarRepresentation.nontrivial_of_isNonzero
        (NonUnitalStarSubalgebraClass.subtype T) hT.1
    have hU := unitaryEquivalent_inclusion_of_injective
      T hclosedT hcompact rho hrho hinj
    have hRange : (NonUnitalStarAlgHom.range (NonUnitalStarSubalgebraClass.subtype T)) = T := by
      apply le_antisymm
      · intro a ha
        obtain ⟨b, rfl⟩ := (NonUnitalStarAlgHom.mem_range
          (NonUnitalStarSubalgebraClass.subtype T)).1 ha
        exact b.property
      · intro a ha
        exact (NonUnitalStarAlgHom.mem_range
          (NonUnitalStarSubalgebraClass.subtype T)).2 ⟨⟨a, ha⟩, rfl⟩
    exact hU.range_eq_compactOperatorStarSubalgebra (hRange.trans hEq)
  · intro hEq
    have hcompact : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ L ≤ (NonUnitalStarAlgHom.range rho) := hEq.ge
    have hker : NonUnitalCStarRepresentation.kernelIdeal rho =
        NonUnitalCStarRepresentation.kernelIdeal
          (NonUnitalStarSubalgebraClass.subtype T) := by
      apply le_antisymm
      · intro a ha
        have hz : rho a = 0 :=
          (NonUnitalCStarRepresentation.mem_kernelIdeal rho a).1 ha
        have : a = 0 := hinj (by simpa only [map_zero] using hz)
        subst a
        exact (NonUnitalCStarRepresentation.mem_kernelIdeal
          (NonUnitalStarSubalgebraClass.subtype T) 0).2 (map_zero _)
      · intro a ha
        have hz : (a : K →L[ℂ] K) = 0 :=
          (NonUnitalCStarRepresentation.mem_kernelIdeal
            (NonUnitalStarSubalgebraClass.subtype T) a).1 ha
        have : a = 0 := Subtype.ext hz
        subst a
        exact (NonUnitalCStarRepresentation.mem_kernelIdeal rho 0).2 (map_zero _)
    have hU := NonUnitalCStarRepresentation.unitaryEquivalent_of_kernelIdeal_eq_of_compact_le_range
      rho (NonUnitalStarSubalgebraClass.subtype T) hT hker hcompact
    have hRange : (NonUnitalStarAlgHom.range (NonUnitalStarSubalgebraClass.subtype T)) = T := by
      apply le_antisymm
      · intro a ha
        obtain ⟨b, rfl⟩ := (NonUnitalStarAlgHom.mem_range
          (NonUnitalStarSubalgebraClass.subtype T)).1 ha
        exact b.property
      · intro a ha
        exact (NonUnitalStarAlgHom.mem_range
          (NonUnitalStarSubalgebraClass.subtype T)).2 ⟨⟨a, ha⟩, rfl⟩
    exact hRange.symm.trans
      (hU.range_eq_compactOperatorStarSubalgebra hEq)

include hclosedT hT hrho hinj in
/-- Proper compact containment is preserved by the same faithful image. -/
theorem compactOperatorStarSubalgebra_lt_iff_range_of_injective :
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K < T ↔
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ L < (NonUnitalStarAlgHom.range rho) := by
  have hle := compactOperatorStarSubalgebra_le_iff_range_of_injective
    (hclosedT := hclosedT) T hT rho hrho hinj
  have heq := eq_compactOperatorStarSubalgebra_iff_range_of_injective
    (hclosedT := hclosedT) T hT rho hrho hinj
  constructor
  · intro h
    refine lt_of_le_of_ne (hle.mp h.le) ?_
    intro hEq
    have hTcompact : T = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K :=
      heq.mpr hEq.symm
    exact h.ne hTcompact.symm
  · intro h
    refine lt_of_le_of_ne (hle.mpr h.le) ?_
    intro hEq
    have hRcompact : (NonUnitalStarAlgHom.range rho) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ L :=
      heq.mp hEq.symm
    exact h.ne hRcompact.symm

include hclosedT hT hrho hinj in
/-- The zero compact-intersection alternative is preserved by a faithful irreducible image. -/
theorem forall_compact_eq_zero_iff_range_of_injective :
    (∀ a : K →L[ℂ] K, a ∈ T → IsCompactOperator a → a = 0) ↔
      ∀ b : L →L[ℂ] L, b ∈ (NonUnitalStarAlgHom.range rho) → IsCompactOperator b → b = 0 := by
  have hR : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype (NonUnitalStarAlgHom.range rho)) :=
    (NonUnitalCStarRepresentation.isIrreducible_imageRepresentation_iff rho).2 hrho
  rw [forall_compact_eq_zero_iff_not_compactOperatorStarSubalgebra_le
      T hT hclosedT,
    forall_compact_eq_zero_iff_not_compactOperatorStarSubalgebra_le
      (NonUnitalStarAlgHom.range rho) hR (HomKernelQuotient.isClosed_image rho),
    compactOperatorStarSubalgebra_le_iff_range_of_injective
      (hclosedT := hclosedT) T hT rho hrho hinj]

end FaithfulImage

section ActualTransport

variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable (T : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K))
variable [IsClosed (S : Set (H →L[ℂ] H))] [IsClosed (T : Set (K →L[ℂ] K))]
variable (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
variable (hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T))
variable (e : ClosureSpace.Homeomorph
  (NormedSpace.geometricStructureClosure ℂ S)
  (NormedSpace.geometricStructureClosure ℂ T))

local instance : NonUnitalCStarAlgebra T :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra T
    (h_closed := inferInstance)
local instance : PartialOrder T := _root_.CStarAlgebra.spectralOrder T
local instance : StarOrderedRing T := _root_.CStarAlgebra.spectralOrderedRing T

include hS hT e in
/-- The same faithful target image transports compact containment across the specified GSS map. -/
theorem compactOperatorStarSubalgebra_le_iff_of_geometricStructure_homeomorph :
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ S ↔
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K ≤ T := by
  obtain ⟨phi, hfaith, r, _hpre, _hinv, himage⟩ :=
    exists_faithful_normalPart_transport S hS e
  let f := normalPartHomeomorphOfImage (e.trans r.symm) himage
  have hR : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype (NonUnitalStarAlgHom.range phi.gnsRepresentation)) :=
    (NonUnitalCStarRepresentation.isIrreducible_imageRepresentation_iff
      phi.gnsRepresentation).2 phi.isIrreducible_gnsRepresentation
  exact (compactOperatorStarSubalgebra_le_iff_of_normalPart_homeomorph
      S (NonUnitalStarAlgHom.range phi.gnsRepresentation) hS hR f).trans
    (compactOperatorStarSubalgebra_le_iff_range_of_injective
      (hclosedT := by infer_instance) T hT phi.gnsRepresentation
        phi.isIrreducible_gnsRepresentation hfaith).symm

include hS hT e in
/-- Equality with the compact algebra is invariant under the specified full GSS homeomorphism. -/
theorem eq_compactOperatorStarSubalgebra_iff_of_geometricStructure_homeomorph :
    S = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ↔
      T = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K := by
  obtain ⟨phi, hfaith, r, _hpre, _hinv, himage⟩ :=
    exists_faithful_normalPart_transport S hS e
  let f := normalPartHomeomorphOfImage (e.trans r.symm) himage
  have hR : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype (NonUnitalStarAlgHom.range phi.gnsRepresentation)) :=
    (NonUnitalCStarRepresentation.isIrreducible_imageRepresentation_iff
      phi.gnsRepresentation).2 phi.isIrreducible_gnsRepresentation
  exact (eq_compactOperatorStarSubalgebra_iff_of_normalPart_homeomorph
      S (NonUnitalStarAlgHom.range phi.gnsRepresentation) hS hR f).trans
    (eq_compactOperatorStarSubalgebra_iff_range_of_injective
      (hclosedT := by infer_instance) T hT phi.gnsRepresentation
        phi.isIrreducible_gnsRepresentation hfaith).symm

include hS hT e in
/-- The proper compact-containing alternative is invariant under the specified GSS map. -/
theorem compactOperatorStarSubalgebra_lt_iff_of_geometricStructure_homeomorph :
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H < S ↔
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K < T := by
  have hle := compactOperatorStarSubalgebra_le_iff_of_geometricStructure_homeomorph
    S T hS hT e
  have heq := eq_compactOperatorStarSubalgebra_iff_of_geometricStructure_homeomorph
    S T hS hT e
  constructor
  · intro h
    refine lt_of_le_of_ne (hle.mp h.le) ?_
    intro hEq
    have hScompact : S = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H :=
      heq.mpr hEq.symm
    exact h.ne hScompact.symm
  · intro h
    refine lt_of_le_of_ne (hle.mpr h.le) ?_
    intro hEq
    have hTcompact : T = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K :=
      heq.mp hEq.symm
    exact h.ne hTcompact.symm

include hS hT e in
/-- All compact members vanish on one side iff they vanish on the other. -/
theorem forall_compact_eq_zero_iff_of_geometricStructure_homeomorph :
    (∀ a : H →L[ℂ] H, a ∈ S → IsCompactOperator a → a = 0) ↔
      ∀ b : K →L[ℂ] K, b ∈ T → IsCompactOperator b → b = 0 := by
  rw [forall_compact_eq_zero_iff_not_compactOperatorStarSubalgebra_le
      S hS (by infer_instance),
    forall_compact_eq_zero_iff_not_compactOperatorStarSubalgebra_le
      T hT (by infer_instance),
    compactOperatorStarSubalgebra_le_iff_of_geometricStructure_homeomorph
      S T hS hT e]

include hS hT e in
/-- Literal compact-intersection ideals are simultaneously bottom. -/
theorem compactIntersectionIdeal_eq_bot_iff_of_geometricStructure_homeomorph :
    compactIntersectionIdeal S (by infer_instance) hS = ⊥ ↔
      compactIntersectionIdeal T (by infer_instance) hT = ⊥ := by
  rw [compactIntersectionIdeal_eq_bot_iff S (by infer_instance) hS,
    compactIntersectionIdeal_eq_bot_iff T (by infer_instance) hT,
    forall_compact_eq_zero_iff_of_geometricStructure_homeomorph S T hS hT e]

end ActualTransport

end MathlibAnnex.Analysis.CStarAlgebra
