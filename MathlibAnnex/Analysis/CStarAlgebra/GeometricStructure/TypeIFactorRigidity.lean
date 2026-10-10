/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.BoundedOperatorRigidity
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.RepresentationTransport

/-!
# A concrete bounded-operator-model endpoint for Paper 8.15

This file deliberately does not define a type-I factor.  It records the
reusable concrete condition that a faithful representation has literal range
all bounded operators.  A GSS homeomorphism transports such a model through
the SAME faithful pure-state image selected by the existing normal-part
transport, and the two concrete full operator ranges yield an actual
non-unital star-algebra equivalence.

This is the local replacement needed by Paper 8.15, not the deferred
Glimm--Sakai equivalence or a general theory of type-I factors.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uA uB uH
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable [PartialOrder A] [StarOrderedRing A]
variable [PartialOrder B] [StarOrderedRing B]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] HomKernelQuotient.imageCStarAlgebra
  HomKernelQuotient.isClosed_image

/-- A faithful concrete representation whose literal range is the whole
bounded-operator algebra.  This predicate does not assert that the algebra is
a type-I factor and does not hide any representation-existence theorem. -/
def IsBoundedOperatorModel (pi : NonUnitalCStarRepresentation A H) : Prop :=
  Function.Injective pi ∧ (NonUnitalStarAlgHom.range pi) = ⊤

namespace IsBoundedOperatorModel

/-- A bounded-operator model of a nontrivial algebra is nonzero. -/
theorem isNonzero [Nontrivial A] {pi : NonUnitalCStarRepresentation A H}
    (hpi : IsBoundedOperatorModel pi) : pi.IsNonzero := by
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  refine ⟨a, ?_⟩
  intro hz
  exact ha (hpi.1 (by simpa only [map_zero] using hz))

/-- Surjectivity is literal surjectivity onto `B(H)`, not merely density. -/
theorem surjective {pi : NonUnitalCStarRepresentation A H}
    (hpi : IsBoundedOperatorModel pi) : Function.Surjective pi := by
  intro T
  apply (NonUnitalStarAlgHom.mem_range pi).1
  rw [hpi.2]
  trivial

/-- A faithful full-range representation of a nontrivial algebra is
irreducible because its action is the actual full operator action. -/
theorem isIrreducible [Nontrivial A] {pi : NonUnitalCStarRepresentation A H}
    (hpi : IsBoundedOperatorModel pi) : pi.IsIrreducible := by
  letI : Nontrivial H :=
    NonUnitalCStarRepresentation.nontrivial_of_isNonzero pi hpi.isNonzero
  have h := NonUnitalCStarRepresentation.isIrreducible_comp_iff_of_surjective
    (operatorIdentityRepresentation (H := H)) pi hpi.surjective
  have hcomp : (operatorIdentityRepresentation (H := H)).comp pi = pi := by
    ext a
    rfl
  rw [hcomp] at h
  exact h.mpr (isIrreducible_operatorIdentityRepresentation (H := H))

end IsBoundedOperatorModel

/-- A bounded-operator model gives an actual star-algebra equivalence with the
literal full operator algebra.  The inverse uses the proved surjectivity of
the same representation. -/
def boundedOperatorStarAlgEquiv (pi : NonUnitalCStarRepresentation A H)
    (hpi : IsBoundedOperatorModel pi) : A ≃⋆ₐ[ℂ] (H →L[ℂ] H) := by
  have hs : Function.Surjective pi := hpi.surjective
  exact
    { toFun := pi
      invFun := fun T => (hs T).choose
      left_inv := fun a => hpi.1 (hs (pi a)).choose_spec
      right_inv := fun T => (hs T).choose_spec
      map_add' := map_add pi
      map_mul' := map_mul pi
      map_star' := map_star pi
      map_smul' := map_smul pi }

@[simp]
theorem boundedOperatorStarAlgEquiv_apply
    (pi : NonUnitalCStarRepresentation A H) (hpi : IsBoundedOperatorModel pi) (a : A) :
    boundedOperatorStarAlgEquiv pi hpi a = pi a := rfl

@[simp]
theorem boundedOperatorStarAlgEquiv_symm_apply
    (pi : NonUnitalCStarRepresentation A H) (hpi : IsBoundedOperatorModel pi)
    (T : H →L[ℂ] H) :
    pi ((boundedOperatorStarAlgEquiv pi hpi).symm T) = T := by
  exact (boundedOperatorStarAlgEquiv pi hpi).apply_symm_apply T

section Transport

variable [Nontrivial A]

/-- Core transport theorem.  The target representation is the SAME faithful
pure-state image selected from the specified GSS homeomorphism.  Its full
range and the Hilbert-space unitary are both conclusions. -/
theorem exists_faithful_boundedOperatorModel_of_geometricStructure_homeomorph
    (pi : NonUnitalCStarRepresentation A H) (hpi : IsBoundedOperatorModel pi)
    (e : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B)) :
    ∃ (K : Type uB) (instN : NormedAddCommGroup K),
      letI := instN
      ∃ instI : InnerProductSpace ℂ K,
        letI := instI
        ∃ instC : CompleteSpace K,
          letI := instC
          ∃ rho : NonUnitalCStarRepresentation B K,
            IsBoundedOperatorModel rho ∧ Nonempty (H ≃ₗᵢ[ℂ] K) := by
  letI : Nontrivial H :=
    NonUnitalCStarRepresentation.nontrivial_of_isNonzero pi hpi.isNonzero
  letI : IsClosed
      ((⊤ : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H)) := by
    change IsClosed (Set.univ : Set (H →L[ℂ] H))
    exact isClosed_univ
  have hirr : pi.IsIrreducible := hpi.isIrreducible
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  have rA : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ
        (⊤ : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)))
      (NormedSpace.geometricStructureClosure ℂ A) := by
    dsimp +instances only [HomKernelQuotient.imageCStarAlgebra,
      NonUnitalStarSubalgebra.nonUnitalCStarAlgebra]
    rw [← hpi.2]
    exact faithfulImageGeometricStructureHomeomorph pi hirr hpi.1 x x hx hx
  let eTop := rA.trans e
  have hTop : NonUnitalCStarRepresentation.IsIrreducible
      (A := ↥(⊤ : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))) (H := H)
      (NonUnitalStarSubalgebraClass.subtype
        (⊤ : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))) :=
    isIrreducible_subtype_top (H := H)
  obtain ⟨phi, hfaith, r, _hpre, _hinv, himage⟩ :=
    exists_faithful_normalPart_transport
      (⊤ : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) hTop eTop
  have hR : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype
      (NonUnitalStarAlgHom.range phi.gnsRepresentation)) :=
    (NonUnitalCStarRepresentation.isIrreducible_imageRepresentation_iff
      phi.gnsRepresentation).2 phi.isIrreducible_gnsRepresentation
  letI : Nontrivial phi.GNS :=
    NonUnitalCStarRepresentation.nontrivial_of_isNonzero
      phi.gnsRepresentation phi.isIrreducible_gnsRepresentation.1
  let f := normalPartHomeomorphOfImage (eTop.trans r.symm) himage
  have hRange : (NonUnitalStarAlgHom.range phi.gnsRepresentation) = ⊤ :=
    eq_top_of_normalPart_homeomorph (NonUnitalStarAlgHom.range phi.gnsRepresentation) hR f
  have hU : Nonempty (H ≃ₗᵢ[ℂ] phi.GNS) :=
    nonempty_linearIsometryEquiv_of_geometricStructure_homeomorph
      (NonUnitalStarAlgHom.range phi.gnsRepresentation) hR (eTop.trans r.symm)
  exact ⟨phi.GNS, inferInstance, inferInstance, inferInstance,
    phi.gnsRepresentation, ⟨hfaith, hRange⟩, hU⟩

/-- Paper-facing existence of a faithful full bounded-operator model on the
target algebra, with all Hilbert-space structure carried explicitly. -/
theorem exists_boundedOperatorModel_of_geometricStructure_homeomorph
    (pi : NonUnitalCStarRepresentation A H) (hpi : IsBoundedOperatorModel pi)
    (e : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B)) :
    ∃ (K : Type uB) (instN : NormedAddCommGroup K),
      letI := instN
      ∃ instI : InnerProductSpace ℂ K,
        letI := instI
        ∃ instC : CompleteSpace K,
          letI := instC
          ∃ rho : NonUnitalCStarRepresentation B K,
            IsBoundedOperatorModel rho := by
  obtain ⟨K, instN, instI, instC, rho, hrho, _hU⟩ :=
    exists_faithful_boundedOperatorModel_of_geometricStructure_homeomorph pi hpi e
  exact ⟨K, instN, instI, instC, rho, hrho⟩

/-- A GSS homeomorphism between algebras carrying bounded-operator models
induces an actual non-unital star-algebra equivalence.  The construction uses
the two concrete range equivalences and a unitary between the Hilbert spaces. -/
theorem nonempty_starAlgEquiv_of_boundedOperatorModel_of_geometricStructure_homeomorph
    (pi : NonUnitalCStarRepresentation A H) (hpi : IsBoundedOperatorModel pi)
    (e : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B)) :
    Nonempty (A ≃⋆ₐ[ℂ] B) := by
  obtain ⟨K, instN, instI, instC, rho, hrho, hU⟩ :=
    exists_faithful_boundedOperatorModel_of_geometricStructure_homeomorph pi hpi e
  letI := instN
  letI := instI
  letI := instC
  obtain ⟨U⟩ := hU
  exact ⟨((boundedOperatorStarAlgEquiv pi hpi).trans U.conjStarAlgEquiv).trans
    (boundedOperatorStarAlgEquiv rho hrho).symm⟩

/-- Minimal joint endpoint for Paper 8.15: one and the same transported
faithful representation is a bounded-operator model, and the original
algebras are star-isomorphic through that model and the original concrete
full range. -/
theorem exists_boundedOperatorModel_and_nonempty_starAlgEquiv
    (pi : NonUnitalCStarRepresentation A H) (hpi : IsBoundedOperatorModel pi)
    (e : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B)) :
    ∃ (K : Type uB) (instN : NormedAddCommGroup K),
      letI := instN
      ∃ instI : InnerProductSpace ℂ K,
        letI := instI
        ∃ instC : CompleteSpace K,
          letI := instC
          ∃ rho : NonUnitalCStarRepresentation B K,
            IsBoundedOperatorModel rho ∧ Nonempty (A ≃⋆ₐ[ℂ] B) := by
  obtain ⟨K, instN, instI, instC, rho, hrho, hU⟩ :=
    exists_faithful_boundedOperatorModel_of_geometricStructure_homeomorph pi hpi e
  letI := instN
  letI := instI
  letI := instC
  obtain ⟨U⟩ := hU
  refine ⟨K, instN, instI, instC, rho, hrho, ?_⟩
  exact ⟨((boundedOperatorStarAlgEquiv pi hpi).trans U.conjStarAlgEquiv).trans
    (boundedOperatorStarAlgEquiv rho hrho).symm⟩

end Transport

end MathlibAnnex.Analysis.CStarAlgebra
