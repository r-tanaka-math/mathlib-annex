/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactRange
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.CompactOperatorSpectrum
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartClassification
import MathlibAnnex.Analysis.InnerProductSpace.CompactSandwich
import MathlibAnnex.Topology.ClosureSpace.FiniteHomeomorph

/-!
# Compact containment characterized by the actual normal-part comparison

The target is the full geometric structure space of the compact operator
algebra. Its identification with its normal part is a proved homeomorphism,
not a type synonym. Finite targets use exact interpolation, including dimensions
one and two. Infinite targets use the given map's selected bounded pair and
the actual compact sandwich equality, with both global orientations covered
by the existing classification. No continuity of the inverse is required for
compact containment. Equality is treated separately, with that hypothesis.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

attribute [local instance] ContinuousLinearMap.isClosed_compactOperatorStarSubalgebra

/-- The literal normal-part inclusion of the compact algebra is a full
homeomorphism. Nontriviality is explicit; the zero Hilbert space is not a
one-point irreducible-spectrum model. -/
def compactNormalPartHomeomorph [Nontrivial H] :
    ClosureSpace.Homeomorph
      ((NormedSpace.geometricStructureClosure ℂ
        (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H)).subspace
          (normalPart (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H)))
      (NormedSpace.geometricStructureClosure ℂ
        (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H)) := by
  let e : normalPart (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) ≃
      NormedSpace.GeometricStructureSpace ℂ
        (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) :=
    { toFun := Subtype.val
      invFun := fun I => ⟨I, by
        rw [normalPart_compactOperatorStarSubalgebra_eq_univ]
        exact Set.mem_univ I⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }
  exact ClosureSpace.homeomorphInduced _ e

@[simp]
theorem compactNormalPartHomeomorph_apply [Nontrivial H]
    (I : normalPart (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H)) :
    (compactNormalPartHomeomorph (H := H)).toEquiv I = I.val := rfl

@[simp]
theorem compactNormalPartHomeomorph_symm_val [Nontrivial H]
    (I : NormedSpace.GeometricStructureSpace ℂ
      (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H)) :
    ((compactNormalPartHomeomorph (H := H)).toEquiv.symm I).val = I := rfl

variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable [IsClosed (S : Set (H →L[ℂ] H))]
variable (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))

/-- The comparison has the actual coefficient transport with identity vector
maps; the next theorem identifies exactly when it is fully continuous. -/
def normalPartToCompactFiniteHomeomorph [Nontrivial H] :
    ClosureSpace.FiniteHomeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      (NormedSpace.geometricStructureClosure ℂ
        (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H)) :=
  (normalPartLinearFiniteHomeomorph S
    (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) hS
    (isIrreducible_compactOperatorRepresentation H)
    (LinearEquiv.refl ℂ H) (LinearEquiv.refl ℂ H)).trans
      compactNormalPartHomeomorph.toFiniteHomeomorph

/-- Evaluation is independent of the chosen representatives in the definition
of the finite homeomorphism. The full-GSS point is the original coefficient kernel. -/
theorem normalPartToCompactFiniteHomeomorph_point [Nontrivial H]
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    (normalPartToCompactFiniteHomeomorph S hS).toEquiv
        (normalPartPoint S hS x y hx hy) =
      restrictedMatrixCoefficientKernel
        (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H)
        (isIrreducible_compactOperatorRepresentation H) x y hx hy := by
  change (normalPartSemilinearMap S (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H)
    (isIrreducible_compactOperatorRepresentation H) (LinearEquiv.refl ℂ H)
    (LinearEquiv.refl ℂ H) (normalPartPoint S hS x y hx hy)).val = _
  rw [normalPartSemilinearMap_point S (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H)
    hS (isIrreducible_compactOperatorRepresentation H) (fun _ => rfl)]
  rfl

/-- The literal scalar-kernel formula in the full compact target. -/
theorem normalPartToCompactFiniteHomeomorph_point_val [Nontrivial H]
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    ((normalPartToCompactFiniteHomeomorph S hS).toEquiv
      (normalPartPoint S hS x y hx hy)).val =
        {a : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H |
          inner ℂ y ((a : H →L[ℂ] H) x) = 0} := by
  rw [normalPartToCompactFiniteHomeomorph_point S hS x y hx hy]
  rfl

/-- The inverse of the SAME comparison returns the original coefficient point. -/
theorem normalPartToCompactFiniteHomeomorph_symm_point [Nontrivial H]
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    (normalPartToCompactFiniteHomeomorph S hS).toEquiv.symm
      (restrictedMatrixCoefficientKernel
        (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H)
        (isIrreducible_compactOperatorRepresentation H) x y hx hy) =
      normalPartPoint S hS x y hx hy := by
  apply (normalPartToCompactFiniteHomeomorph S hS).toEquiv.injective
  rw [Equiv.apply_symm_apply, normalPartToCompactFiniteHomeomorph_point S hS x y hx hy]

/-- Forward full continuity follows from compact containment, not from an
inverse-continuity assumption or from a redefinition of type I. -/
theorem continuous_normalPartToCompactFiniteHomeomorph [Nontrivial H]
    (hcompact : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ S) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      (NormedSpace.geometricStructureClosure ℂ
        (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H))
      (normalPartToCompactFiniteHomeomorph S hS).toEquiv := by
  have hf := (continuous_normalPartLinearMap_iff S
    (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) hS
    (isIrreducible_compactOperatorRepresentation H)
    (ContinuousLinearEquiv.refl ℂ H) (ContinuousLinearEquiv.refl ℂ H)).2
      (fun b => by
        simpa [InnerProductSpace.adjointSandwich, ContinuousLinearMap.adjoint_id,
          ContinuousLinearMap.id_comp] using hcompact b.property)
  exact compactNormalPartHomeomorph.continuous_toFun.comp hf

include hS in
/-- The reverse implication for a specified map and an arbitrary, independently
sized, nonzero compact target. The finite branch derives full operator range;
the infinite branch uses the same selected pair of the given finite homeomorphism. -/
theorem compactOperatorStarSubalgebra_le_of_continuous_finiteHomeomorph [Nontrivial K]
    (e : ClosureSpace.FiniteHomeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      (NormedSpace.geometricStructureClosure ℂ
        (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K)))
    (he : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      (NormedSpace.geometricStructureClosure ℂ
        (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K)) e.toEquiv) :
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ S := by
  classical
  let T := ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K
  have hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T) :=
    isIrreducible_compactOperatorRepresentation K
  let f := e.trans (compactNormalPartHomeomorph (H := K)).symm.toFiniteHomeomorph
  have hf : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) f.toEquiv :=
    (compactNormalPartHomeomorph (H := K)).continuous_invFun.comp he
  by_cases hK : FiniteDimensional ℂ K
  · letI := hK
    haveI : FiniteDimensional ℂ H :=
      (finite_and_finrank_eq_of_normalPart_finiteHomeomorph T S hT hS f.symm
        (Or.inl hK)).2.1
    rw [eq_top_of_isIrreducible_subtype_of_finiteDimensional S hS]
    exact le_top
  · have hH : ¬ FiniteDimensional ℂ H := fun h =>
      hK ((finite_iff_of_normalPart_finiteHomeomorph S T hS hT f).1 h)
    rcases (exists_normalPart_selected_operator_inclusion S T hS hT f hH hf).2 with
      ⟨U, V, _, _, _, _, _orientation, hinc, _⟩ |
      ⟨U, V, _, _, _, _, _orientation, hinc, _⟩
    · intro a ha
      have hm : a ∈ InnerProductSpace.adjointSandwich
          U.toContinuousLinearMap V.toContinuousLinearMap '' (T : Set (K →L[ℂ] K)) := by
        rw [show (T : Set (K →L[ℂ] K)) = {b : K →L[ℂ] K | IsCompactOperator b} from rfl,
          InnerProductSpace.image_adjointSandwich_setOf_isCompactOperator]
        exact ha
      obtain ⟨b, hb, rfl⟩ := hm
      exact hinc ⟨b, hb⟩
    · intro a ha
      have hm : a ∈ InnerProductSpace.conjugateAdjointSandwich
          U.toContinuousLinearMap V.toContinuousLinearMap '' (T : Set (K →L[ℂ] K)) := by
        rw [show (T : Set (K →L[ℂ] K)) = {b : K →L[ℂ] K | IsCompactOperator b} from rfl,
          InnerProductSpace.image_conjugateAdjointSandwich_setOf_isCompactOperator]
        exact ha
      obtain ⟨b, hb, rfl⟩ := hm
      exact hinc ⟨b, hb⟩

/-- For the same-space identity comparison, full continuity is exactly the
representation-side compact containment condition. -/
theorem continuous_normalPartToCompactFiniteHomeomorph_iff [Nontrivial H] :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      (NormedSpace.geometricStructureClosure ℂ
        (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H))
      (normalPartToCompactFiniteHomeomorph S hS).toEquiv ↔
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ S :=
  ⟨compactOperatorStarSubalgebra_le_of_continuous_finiteHomeomorph S hS _,
    continuous_normalPartToCompactFiniteHomeomorph S hS⟩

include hS in
/-- The full-homeomorphism variant detects equality, not only containment.
Both directions of the specified map's full continuity are used in the infinite branch. -/
theorem eq_compactOperatorStarSubalgebra_of_homeomorph [Nontrivial K]
    (e : ClosureSpace.Homeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      (NormedSpace.geometricStructureClosure ℂ
        (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K))) :
    S = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H := by
  classical
  let T := ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K
  have hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T) :=
    isIrreducible_compactOperatorRepresentation K
  let f := e.trans (compactNormalPartHomeomorph (H := K)).symm
  by_cases hK : FiniteDimensional ℂ K
  · letI := hK
    haveI : FiniteDimensional ℂ H :=
      (finite_and_finrank_eq_of_normalPart_finiteHomeomorph T S hT hS
        f.symm.toFiniteHomeomorph (Or.inl hK)).2.1
    rw [eq_top_of_isIrreducible_subtype_of_finiteDimensional S hS,
      ContinuousLinearMap.compactOperatorStarSubalgebra_eq_top]
  · have hH : ¬ FiniteDimensional ℂ H := fun h =>
      hK ((finite_iff_of_normalPart_finiteHomeomorph S T hS hT f.toFiniteHomeomorph).1 h)
    rcases (exists_normalPart_selected_operator_eq S T hS hT f.toFiniteHomeomorph hH
      f.continuous_toFun f.continuous_invFun).2 with
      ⟨U, V, _, _, _, _, _orientation, hEq⟩ |
      ⟨U, V, _, _, _, _, _orientation, hEq⟩
    · apply SetLike.coe_injective
      exact hEq.symm.trans (InnerProductSpace.image_adjointSandwich_setOf_isCompactOperator U V)
    · apply SetLike.coe_injective
      exact hEq.symm.trans
        (InnerProductSpace.image_conjugateAdjointSandwich_setOf_isCompactOperator U V)

/-- Conversely, equality with the actual compact carrier supplies a full
homeomorphism, with no dimension restriction. -/
theorem nonempty_homeomorph_compact_of_eq [Nontrivial H]
    (h : S = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) :
    Nonempty (ClosureSpace.Homeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      (NormedSpace.geometricStructureClosure ℂ
        (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H))) := by
  subst S
  exact ⟨compactNormalPartHomeomorph⟩

end MathlibAnnex.Analysis.CStarAlgebra
