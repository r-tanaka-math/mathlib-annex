/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.Subsingleton
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.TypeIFactorRigidity
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.StarAlgEquiv
import MathlibAnnex.Analysis.Normed.GeometricStructure.Separation
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Full geometric-structure rigidity for a given bounded-operator model

A specified equivalence `A ≃⋆ₐ[ℂ] (H →L[ℂ] H)` gives the actual representation
obtained by composing that equivalence with `operatorIdentityRepresentation`.
The same map is faithful and has literal full operator range. The received
bounded-operator rigidity theorem is used only in the nonzero branch. In the
zero branch, geometric separation forces the other algebra to be zero as well,
and the unique maps between the two zero algebras give the star equivalence.
No target model, nonzero algebra, or nonempty geometric space is assumed.

The final existence interfaces allow either side to supply a model. Their
Hilbert carriers and norm, inner-product, and completeness structures are
explicitly quantified in independently chosen universes; no shrinking of a
Hilbert space to an algebra's universe is used.

This is a characterization for a GIVEN full bounded-operator model. It neither
defines an abstract type-I factor nor proves a classification theorem for an
independently defined abstract type-I factor. The resulting star equivalence
is not asserted to induce the specified nonlinear geometric homeomorphism.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w z

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {B : Type v} [NonUnitalCStarAlgebra B]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type z} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

local instance instSpectralOrderBoundedOperatorModel : PartialOrder A :=
  _root_.CStarAlgebra.spectralOrder A
local instance instSpectralOrderedRingBoundedOperatorModel : StarOrderedRing A :=
  _root_.CStarAlgebra.spectralOrderedRing A

namespace NonUnitalCStarRepresentation

/-- The specified full operator model, acting by the existing identity
representation. This is the same given map, not a newly selected model. -/
def ofBoundedOperatorEquiv (E : A ≃⋆ₐ[ℂ] (H →L[ℂ] H)) :
    NonUnitalCStarRepresentation A H :=
  (operatorIdentityRepresentation (H := H)).comp E.toNonUnitalStarAlgHom

@[simp]
theorem ofBoundedOperatorEquiv_apply
    (E : A ≃⋆ₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    ofBoundedOperatorEquiv E a = E a := rfl

/-- Faithfulness of the actual identity-action composite. -/
theorem ofBoundedOperatorEquiv_injective
    (E : A ≃⋆ₐ[ℂ] (H →L[ℂ] H)) :
    Function.Injective (ofBoundedOperatorEquiv E) := by
  intro a b hab
  exact E.injective hab

/-- Its range is all bounded operators, with the preimage supplied by the
inverse of the specified equivalence. -/
theorem range_ofBoundedOperatorEquiv
    (E : A ≃⋆ₐ[ℂ] (H →L[ℂ] H)) :
    (NonUnitalStarAlgHom.range (ofBoundedOperatorEquiv E)) = ⊤ := by
  apply SetLike.ext
  intro T
  constructor
  · intro _
    trivial
  · intro _
    apply (NonUnitalStarAlgHom.mem_range (ofBoundedOperatorEquiv E)).2
    exact ⟨E.symm T, E.apply_symm_apply T⟩

/-- The existing model predicate is satisfied by this same composite. -/
theorem isBoundedOperatorModel_ofBoundedOperatorEquiv
    (E : A ≃⋆ₐ[ℂ] (H →L[ℂ] H)) :
    IsBoundedOperatorModel (ofBoundedOperatorEquiv E) :=
  ⟨ofBoundedOperatorEquiv_injective E, range_ofBoundedOperatorEquiv E⟩

/-- The operator norm is the original C-star norm. -/
theorem norm_ofBoundedOperatorEquiv
    (E : A ≃⋆ₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    ‖ofBoundedOperatorEquiv E a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (ofBoundedOperatorEquiv E)
    (ofBoundedOperatorEquiv_injective E) a

/-- The same representation is isometric, including for the zero model. -/
theorem isometry_ofBoundedOperatorEquiv
    (E : A ≃⋆ₐ[ℂ] (H →L[ℂ] H)) : Isometry (ofBoundedOperatorEquiv E) :=
  NonUnitalStarAlgHom.isometry (ofBoundedOperatorEquiv E)
    (ofBoundedOperatorEquiv_injective E)

/-- Repackaging an existing full-range representation and then using the
identity action recovers that original representation literally. -/
@[simp]
theorem ofBoundedOperatorEquiv_boundedOperatorStarAlgEquiv
    (pi : NonUnitalCStarRepresentation A H) (hpi : IsBoundedOperatorModel pi) :
    ofBoundedOperatorEquiv (boundedOperatorStarAlgEquiv pi hpi) = pi := by
  apply DFunLike.ext
  intro a
  rfl

end NonUnitalCStarRepresentation

namespace IsBoundedOperatorModel

/-- The zero algebra corresponds exactly to the zero Hilbert space for a
faithful full-range model. Full range, not merely faithfulness, is used in the
forward implication. -/
theorem subsingleton_iff {pi : NonUnitalCStarRepresentation A H}
    (hpi : IsBoundedOperatorModel pi) : Subsingleton A ↔ Subsingleton H := by
  constructor
  · intro hA
    letI : Subsingleton A := hA
    obtain ⟨a, ha⟩ := hpi.surjective (ContinuousLinearMap.id ℂ H)
    have hid : ContinuousLinearMap.id ℂ H = 0 := by
      calc
        ContinuousLinearMap.id ℂ H = pi a := ha.symm
        _ = pi 0 := congrArg pi (Subsingleton.elim a 0)
        _ = 0 := map_zero pi
    have hx : ∀ x : H, x = 0 := by
      intro x
      have h := congrArg (fun T : H →L[ℂ] H => T x) hid
      change x = 0 at h
      exact h
    exact ⟨fun x y => (hx x).trans (hx y).symm⟩
  · intro hH
    letI : Subsingleton H := hH
    refine ⟨fun a b => hpi.1 ?_⟩
    apply ContinuousLinearMap.ext
    intro x
    exact Subsingleton.elim _ _

end IsBoundedOperatorModel

/-- The full geometric-space iff for a specified faithful full-range model.
Only the nonzero branch invokes the received concrete rigidity theorem. The
other algebra need not be supplied with any representation or model. -/
theorem nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_isBoundedOperatorModel
    (pi : NonUnitalCStarRepresentation A H) (hpi : IsBoundedOperatorModel pi) :
    Nonempty (A ≃⋆ₐ[ℂ] B) ↔
      Nonempty (ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
        (NormedSpace.geometricStructureClosure ℂ B)) := by
  constructor
  · rintro ⟨F⟩
    exact ⟨geometricStructureHomeomorphOfStarAlgEquiv F⟩
  · rintro ⟨e⟩
    rcases subsingleton_or_nontrivial A with hA | hA
    · letI : Subsingleton A := hA
      exact nonempty_starAlgEquiv_of_geometricStructure_homeomorph_of_subsingleton e
    · letI : Nontrivial A := hA
      letI : PartialOrder A := _root_.CStarAlgebra.spectralOrder A
      letI : StarOrderedRing A := _root_.CStarAlgebra.spectralOrderedRing A
      letI : PartialOrder B := _root_.CStarAlgebra.spectralOrder B
      letI : StarOrderedRing B := _root_.CStarAlgebra.spectralOrderedRing B
      exact nonempty_starAlgEquiv_of_boundedOperatorModel_of_geometricStructure_homeomorph
        pi hpi e

/-- The symmetric one-sided iff when the specified model belongs to `B`.
The reverse geometric map is used, followed by the inverse star equivalence. -/
theorem nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_isBoundedOperatorModel_right
    (rho : NonUnitalCStarRepresentation B K) (hrho : IsBoundedOperatorModel rho) :
    Nonempty (A ≃⋆ₐ[ℂ] B) ↔
      Nonempty (ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
        (NormedSpace.geometricStructureClosure ℂ B)) := by
  constructor
  · rintro ⟨F⟩
    exact ⟨geometricStructureHomeomorphOfStarAlgEquiv F⟩
  · rintro ⟨e⟩
    obtain ⟨F⟩ :=
      (nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_isBoundedOperatorModel
        (B := A) rho hrho).mpr ⟨e.symm⟩
    exact ⟨F.symm⟩

/-- A specified exact equivalence with `B(H)` supplies its actual model to
the one-sided iff. `H` has an independent universe and may be zero. -/
theorem nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_boundedOperatorEquiv
    (E : A ≃⋆ₐ[ℂ] (H →L[ℂ] H)) :
    Nonempty (A ≃⋆ₐ[ℂ] B) ↔
      Nonempty (ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
        (NormedSpace.geometricStructureClosure ℂ B)) :=
  nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_isBoundedOperatorModel
    (NonUnitalCStarRepresentation.ofBoundedOperatorEquiv E)
    (NonUnitalCStarRepresentation.isBoundedOperatorModel_ofBoundedOperatorEquiv E)

/-- The corresponding given-equivalence iff with the model on the right. -/
theorem nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_boundedOperatorEquiv_right
    (E : B ≃⋆ₐ[ℂ] (K →L[ℂ] K)) :
    Nonempty (A ≃⋆ₐ[ℂ] B) ↔
      Nonempty (ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
        (NormedSpace.geometricStructureClosure ℂ B)) :=
  nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_isBoundedOperatorModel_right
    (NonUnitalCStarRepresentation.ofBoundedOperatorEquiv E)
    (NonUnitalCStarRepresentation.isBoundedOperatorModel_ofBoundedOperatorEquiv E)

/-- The target has an actual full operator model on the SAME given Hilbert
space, also in the zero case. The displayed algebra equivalence intertwines
this model with the given identity-action composite. This does not assert that
it induces the specified geometric homeomorphism. -/
theorem exists_boundedOperatorModel_of_boundedOperatorEquiv_of_geometricStructure_homeomorph
    (E : A ≃⋆ₐ[ℂ] (H →L[ℂ] H))
    (e : ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B)) :
    ∃ (F : A ≃⋆ₐ[ℂ] B) (rho : NonUnitalCStarRepresentation B H),
      IsBoundedOperatorModel rho ∧
        rho.comp F.toNonUnitalStarAlgHom =
          NonUnitalCStarRepresentation.ofBoundedOperatorEquiv E := by
  obtain ⟨F⟩ :=
    (nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_boundedOperatorEquiv
      E).mpr ⟨e⟩
  refine ⟨F, NonUnitalCStarRepresentation.ofBoundedOperatorEquiv (F.symm.trans E),
    NonUnitalCStarRepresentation.isBoundedOperatorModel_ofBoundedOperatorEquiv
      (F.symm.trans E), ?_⟩
  apply DFunLike.ext
  intro a
  change E (F.symm (F a)) = E a
  exact congrArg E (F.symm_apply_apply a)

/-- Either side may supply a full-range faithful representation. The two
Hilbert witness universes are independent of one another and of both algebra
universes. No target model or nonzero hypothesis is added. -/
theorem nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_exists_isBoundedOperatorModel
    (hModel :
      (∃ (L : Type w) (normed : NormedAddCommGroup L),
        letI : NormedAddCommGroup L := normed
        ∃ inner : InnerProductSpace ℂ L,
          letI : InnerProductSpace ℂ L := inner
          ∃ complete : CompleteSpace L,
            letI : CompleteSpace L := complete
            ∃ pi : NonUnitalCStarRepresentation A L, IsBoundedOperatorModel pi) ∨
      (∃ (L : Type z) (normed : NormedAddCommGroup L),
        letI : NormedAddCommGroup L := normed
        ∃ inner : InnerProductSpace ℂ L,
          letI : InnerProductSpace ℂ L := inner
          ∃ complete : CompleteSpace L,
            letI : CompleteSpace L := complete
            ∃ rho : NonUnitalCStarRepresentation B L, IsBoundedOperatorModel rho)) :
    Nonempty (A ≃⋆ₐ[ℂ] B) ↔
      Nonempty (ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
        (NormedSpace.geometricStructureClosure ℂ B)) := by
  rcases hModel with hA | hB
  · obtain ⟨L, normed, inner, complete, pi, hpi⟩ := hA
    letI : NormedAddCommGroup L := normed
    letI : InnerProductSpace ℂ L := inner
    letI : CompleteSpace L := complete
    exact nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_isBoundedOperatorModel
      pi hpi
  · obtain ⟨L, normed, inner, complete, rho, hrho⟩ := hB
    letI : NormedAddCommGroup L := normed
    letI : InnerProductSpace ℂ L := inner
    letI : CompleteSpace L := complete
    exact nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_isBoundedOperatorModel_right
      rho hrho

/-- The same either-side interface with exact equivalences rather than
representation predicates as witnesses. Their actual identity-action
composites, not an extra model hypothesis, enter the proof. -/
theorem nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_exists_boundedOperatorEquiv
    (hModel :
      (∃ (L : Type w) (normed : NormedAddCommGroup L),
        letI : NormedAddCommGroup L := normed
        ∃ inner : InnerProductSpace ℂ L,
          letI : InnerProductSpace ℂ L := inner
          ∃ complete : CompleteSpace L,
            letI : CompleteSpace L := complete
            Nonempty (A ≃⋆ₐ[ℂ] (L →L[ℂ] L))) ∨
      (∃ (L : Type z) (normed : NormedAddCommGroup L),
        letI : NormedAddCommGroup L := normed
        ∃ inner : InnerProductSpace ℂ L,
          letI : InnerProductSpace ℂ L := inner
          ∃ complete : CompleteSpace L,
            letI : CompleteSpace L := complete
            Nonempty (B ≃⋆ₐ[ℂ] (L →L[ℂ] L)))) :
    Nonempty (A ≃⋆ₐ[ℂ] B) ↔
      Nonempty (ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
        (NormedSpace.geometricStructureClosure ℂ B)) := by
  rcases hModel with hA | hB
  · obtain ⟨L, normed, inner, complete, ⟨E⟩⟩ := hA
    letI : NormedAddCommGroup L := normed
    letI : InnerProductSpace ℂ L := inner
    letI : CompleteSpace L := complete
    exact nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_boundedOperatorEquiv E
  · obtain ⟨L, normed, inner, complete, ⟨E⟩⟩ := hB
    letI : NormedAddCommGroup L := normed
    letI : InnerProductSpace ℂ L := inner
    letI : CompleteSpace L := complete
    exact nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_boundedOperatorEquiv_right E

end MathlibAnnex.Analysis.CStarAlgebra
