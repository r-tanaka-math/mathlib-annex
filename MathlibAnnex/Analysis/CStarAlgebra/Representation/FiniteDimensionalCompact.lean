/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.CompactRepresentationCharacterization
import MathlibAnnex.LinearAlgebra.FiniteDimensional.FiniteIntersection
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Faithful finite-dimensional representations of finite-dimensional C-star algebras

The construction uses finitely many of the already selected primitive GNS
representations. Finite-dimensionality of the algebra makes the intersection
of their linear kernels finitely determined. The full reduced atomic action
is faithful, so a finite subfamily still separates algebra elements.

Every selected pure-state GNS space is finite-dimensional: the original
algebra's orbit of the distinguished GNS vector is the range of an explicit
surjective linear map. The genuine dependent Hilbert `lp 2` sum over the
selected finite set is finite-dimensional as well. Its representation is the
existing atomic representation of the unitization restricted to the original
algebra. The star law therefore comes from genuine Hilbert-space GNS actions,
not an unjustified inner product on a left regular representation.

No unit, nonzero algebra, nonempty primitive spectrum, or nonempty finite
selection is assumed. All witness structures are supplied in the algebra's
own universe. Compactness is asserted for the constructed finite-dimensional
representation and then for the same canonical reduced atomic representation,
not for every preassigned faithful representation of the algebra.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open Set
open scoped Classical CStarAlgebra ENNReal lp

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

namespace MathlibAnnex.Analysis.CStarAlgebra

open MathlibAnnex.Analysis.InnerProductSpace

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]

namespace NonUnitalPureState

/-- The original-algebra orbit of the actual GNS vector is a surjective
linear image of the finite-dimensional algebra. -/
theorem finiteDimensional_gns [FiniteDimensional ℂ A] (phi : NonUnitalPureState A) :
    FiniteDimensional ℂ phi.GNS := by
  let orbit : A →ₗ[ℂ] phi.GNS :=
    { toFun := fun a => phi.gnsRepresentation a phi.gnsVector
      map_add' := by
        intro a b
        simp only [map_add, ContinuousLinearMap.add_apply]
      map_smul' := by
        intro c a
        change phi.gnsRepresentation (c • a) phi.gnsVector =
          c • (phi.gnsRepresentation a phi.gnsVector)
        simp only [map_smul, ContinuousLinearMap.smul_apply] }
  apply FiniteDimensional.of_surjective orbit
  exact NonUnitalStateGNS.representation_vector_surjective_of_isPure
    phi.val phi.property.1 phi.property

end NonUnitalPureState

namespace PrimitiveSpectrum

/-- A finite set of the already selected primitive GNS actions separates
points of a finite-dimensional algebra. Empty selections are allowed. -/
theorem exists_finset_pureStateRepresentative_separates_points [FiniteDimensional ℂ A] :
    ∃ s : Finset (PrimitiveSpectrum A),
      ∀ a b : A,
        (∀ P ∈ s, P.pureStateRepresentative.gnsRepresentation a =
          P.pureStateRepresentative.gnsRepresentation b) → a = b := by
  let kernels : PrimitiveSpectrum A → Submodule ℂ A := fun P =>
    (LinearMapClass.linearMap P.pureStateRepresentative.gnsRepresentation).ker
  obtain ⟨s, hs⟩ := Submodule.exists_finset_iInf_eq_of_finiteDimensional kernels
  refine ⟨s, ?_⟩
  intro a b hab
  have hmem : a - b ∈ (⨅ P, kernels P) := by
    rw [hs]
    apply (Submodule.mem_iInf _).mpr
    intro P
    apply (Submodule.mem_iInf _).mpr
    intro hP
    change P.pureStateRepresentative.gnsRepresentation (a - b) = 0
    rw [map_sub, hab P hP, sub_self]
  have hall (P : PrimitiveSpectrum A) :
      P.pureStateRepresentative.gnsRepresentation a =
        P.pureStateRepresentative.gnsRepresentation b := by
    have h := (Submodule.mem_iInf _).mp hmem P
    change P.pureStateRepresentative.gnsRepresentation (a - b) = 0 at h
    exact sub_eq_zero.mp (by simpa only [map_sub] using h)
  apply reducedAtomicRepresentation_injective
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext P
  simp only [reducedAtomicRepresentation_apply, hall P]

/-- The genuine completed dependent Hilbert sum over a given finite selection
of primitive GNS spaces. This carrier is defined before any separation or
finite-dimensionality assumption on the algebra. -/
abbrev FiniteGNSHilbertSpace (A : Type u) [NonUnitalCStarAlgebra A]
    (s : Finset (PrimitiveSpectrum A)) :=
  HilbertSum (fun P : s => P.val.pureStateRepresentative.GNS)

/-- The selected finite GNS actions, obtained from the existing atomic action
of the unitization and then restricted to the original algebra. -/
def finiteGNSRepresentation (s : Finset (PrimitiveSpectrum A)) :
    NonUnitalCStarRepresentation A (FiniteGNSHilbertSpace A s) :=
  (atomicRepresentation (fun P : s =>
    P.val.pureStateRepresentative.gnsRepresentation.unitization)).toNonUnitalStarAlgHom.comp
    (Unitization.inrNonUnitalStarAlgHom ℂ A)

@[simp]
theorem finiteGNSRepresentation_apply (s : Finset (PrimitiveSpectrum A))
    (a : A) (x : FiniteGNSHilbertSpace A s) (P : s) :
    finiteGNSRepresentation s a x P =
      P.val.pureStateRepresentative.gnsRepresentation a (x P) := by
  simp [finiteGNSRepresentation, atomicRepresentation_apply,
    NonUnitalCStarRepresentation.unitization_inr]

/-- Compression to the selected coordinate is precisely the given GNS action. -/
theorem coordinateProjection_comp_finiteGNSRepresentation_comp_coordinateEmbedding
    (s : Finset (PrimitiveSpectrum A)) (a : A) (P : s) :
    (coordinateProjection P).comp
      ((finiteGNSRepresentation s a).comp (coordinateEmbedding P)) =
        P.val.pureStateRepresentative.gnsRepresentation a := by
  apply ContinuousLinearMap.ext
  intro x
  change (finiteGNSRepresentation s a (lp.single 2 P x)) P = _
  rw [finiteGNSRepresentation_apply, lp.coeFn_single, Pi.single_eq_same]

/-- Joint faithfulness of the chosen GNS actions implies faithfulness of
this very finite-sum representation; no summand is assumed faithful. -/
theorem finiteGNSRepresentation_injective (s : Finset (PrimitiveSpectrum A))
    (hsep : ∀ a b : A,
      (∀ P ∈ s, P.pureStateRepresentative.gnsRepresentation a =
        P.pureStateRepresentative.gnsRepresentation b) → a = b) :
    Function.Injective (finiteGNSRepresentation s) := by
  intro a b hab
  apply hsep a b
  intro P hP
  let Q : s := ⟨P, hP⟩
  have h := congrArg
    (fun T : FiniteGNSHilbertSpace A s →L[ℂ] FiniteGNSHilbertSpace A s =>
      (coordinateProjection Q).comp (T.comp (coordinateEmbedding Q))) hab
  simpa only [coordinateProjection_comp_finiteGNSRepresentation_comp_coordinateEmbedding]
    using h

/-- Norm preservation is a property of the same concrete finite GNS action. -/
@[simp]
theorem norm_finiteGNSRepresentation (s : Finset (PrimitiveSpectrum A))
    (hsep : ∀ a b : A,
      (∀ P ∈ s, P.pureStateRepresentative.gnsRepresentation a =
        P.pureStateRepresentative.gnsRepresentation b) → a = b) (a : A) :
    ‖finiteGNSRepresentation s a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (finiteGNSRepresentation s)
    (finiteGNSRepresentation_injective s hsep) a

theorem isometry_finiteGNSRepresentation (s : Finset (PrimitiveSpectrum A))
    (hsep : ∀ a b : A,
      (∀ P ∈ s, P.pureStateRepresentative.gnsRepresentation a =
        P.pureStateRepresentative.gnsRepresentation b) → a = b) :
    Isometry (finiteGNSRepresentation s) :=
  NonUnitalStarAlgHom.isometry (finiteGNSRepresentation s)
    (finiteGNSRepresentation_injective s hsep)

/-- The adjoint identity is inherited from the actual GNS star representations. -/
theorem adjoint_finiteGNSRepresentation (s : Finset (PrimitiveSpectrum A)) (a : A) :
    ContinuousLinearMap.adjoint (finiteGNSRepresentation s a) =
      finiteGNSRepresentation s (star a) := by
  simpa only [ContinuousLinearMap.star_eq_adjoint] using
    (map_star (finiteGNSRepresentation s) a).symm

/-- A finite dependent Hilbert sum of the finite-dimensional GNS fibers is
finite-dimensional. Injecting into the ordinary finite product is sufficient;
no equality between the product norm and the Hilbert norm is asserted. -/
theorem finiteDimensional_finiteGNSHilbertSpace [FiniteDimensional ℂ A]
    (s : Finset (PrimitiveSpectrum A)) :
    FiniteDimensional ℂ (FiniteGNSHilbertSpace A s) := by
  letI : ∀ P : s, FiniteDimensional ℂ P.val.pureStateRepresentative.GNS :=
    fun P => P.val.pureStateRepresentative.finiteDimensional_gns
  let coordinates : FiniteGNSHilbertSpace A s →ₗ[ℂ]
      (∀ P : s, P.val.pureStateRepresentative.GNS) :=
    { toFun := fun x P => x P
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply FiniteDimensional.of_injective coordinates
  intro x y hxy
  apply lp.ext
  exact hxy

/-- All values of the selected finite GNS action are compact because its
actual Hilbert space, not merely the source algebra, is finite-dimensional. -/
theorem isCompactOperator_finiteGNSRepresentation [FiniteDimensional ℂ A]
    (s : Finset (PrimitiveSpectrum A)) (a : A) :
    IsCompactOperator (finiteGNSRepresentation s a) := by
  letI : FiniteDimensional ℂ (FiniteGNSHilbertSpace A s) :=
    finiteDimensional_finiteGNSHilbertSpace s
  have hid : IsCompactOperator (id : FiniteGNSHilbertSpace A s →
      FiniteGNSHilbertSpace A s) :=
    (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℂ)).mpr inferInstance
  exact hid.comp_clm (finiteGNSRepresentation s a)

/-- A finite separating selection yields an actual faithful compact action. -/
theorem isCompactlyRepresented_finiteGNSRepresentation [FiniteDimensional ℂ A]
    (s : Finset (PrimitiveSpectrum A))
    (hsep : ∀ a b : A,
      (∀ P ∈ s, P.pureStateRepresentative.gnsRepresentation a =
        P.pureStateRepresentative.gnsRepresentation b) → a = b) :
    (finiteGNSRepresentation s).IsCompactlyRepresented :=
  ⟨finiteGNSRepresentation_injective s hsep,
    isCompactOperator_finiteGNSRepresentation s⟩

/-- The separating set is proved to exist, rather than supplied as a boundary
hypothesis of the finite-dimensional existence theorem. -/
theorem exists_finset_isCompactlyRepresented_finiteGNSRepresentation
    [FiniteDimensional ℂ A] :
    ∃ s : Finset (PrimitiveSpectrum A),
      (finiteGNSRepresentation s).IsCompactlyRepresented := by
  obtain ⟨s, hs⟩ := exists_finset_pureStateRepresentative_separates_points (A := A)
  exact ⟨s, isCompactlyRepresented_finiteGNSRepresentation s hs⟩

/-- Finite-dimensionality alone makes the same canonical reduced atomic map
faithfully compact. The supplied intermediate witness is the finite GNS sum,
not an arbitrary preassigned faithful representation. -/
theorem isCompactlyRepresented_reducedAtomicRepresentation_of_finiteDimensional
    [FiniteDimensional ℂ A] :
    (reducedAtomicRepresentation (A := A)).IsCompactlyRepresented := by
  obtain ⟨s, hs⟩ := exists_finset_isCompactlyRepresented_finiteGNSRepresentation (A := A)
  exact isCompactlyRepresented_reducedAtomicRepresentation_of_isCompactlyRepresented
    (finiteGNSRepresentation s) hs

end PrimitiveSpectrum

namespace NonUnitalCStarRepresentation

/-- A finite-dimensional C-star algebra has a faithful compact-valued
representation on an explicitly supplied finite-dimensional Hilbert space in
its own universe. The normed, inner-product and completeness structures are
all supplied by the genuine finite dependent GNS Hilbert sum. -/
theorem exists_finiteDimensional_isCompactlyRepresented [FiniteDimensional ℂ A] :
    ∃ (K : Type u) (normed : NormedAddCommGroup K),
      letI : NormedAddCommGroup K := normed
      ∃ inner : InnerProductSpace ℂ K,
        letI : InnerProductSpace ℂ K := inner
        ∃ complete : CompleteSpace K,
          letI : CompleteSpace K := complete
          FiniteDimensional ℂ K ∧
            ∃ pi : NonUnitalCStarRepresentation A K, pi.IsCompactlyRepresented := by
  obtain ⟨s, hs⟩ :=
    PrimitiveSpectrum.exists_finset_isCompactlyRepresented_finiteGNSRepresentation (A := A)
  refine ⟨PrimitiveSpectrum.FiniteGNSHilbertSpace A s, inferInstance, ?_⟩
  refine ⟨inferInstance, ?_⟩
  exact ⟨inferInstance, PrimitiveSpectrum.finiteDimensional_finiteGNSHilbertSpace s,
    PrimitiveSpectrum.finiteGNSRepresentation s, hs⟩

end NonUnitalCStarRepresentation

end MathlibAnnex.Analysis.CStarAlgebra

end
