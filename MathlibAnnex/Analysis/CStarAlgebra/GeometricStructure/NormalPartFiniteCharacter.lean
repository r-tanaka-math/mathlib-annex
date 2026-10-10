/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Topology.ClosureSpace.HullKernelFiniteDimensional
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartProjectiveDimension
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.CompactFiniteConjugation
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Finite character of normal parts and finite-dimensional compact targets

Only the actual coefficient kernels in the normal part are treated as linear
subspaces. The other points of the ambient geometric structure space remain
sets (unions of kernels). No finiteness of the set of normal points is claimed.

The finite-target branch uses finite dimension transferred by the GIVEN finite
homeomorphism in the reverse direction, not inverse full continuity. It includes
Hilbert dimensions one and two and does not use a semilinear realization.
The final two results combine this branch with the received infinite branch.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v uA uH uL
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The relative normal-part closure has finite character if the concrete
operator algebra itself is finite dimensional. No irreducibility is needed. -/
theorem normalPart_closure_eq_iUnion_finite
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (S : Set (H →L[ℂ] H))] [FiniteDimensional ℂ S] :
    ∀ s : Set (normalPart S),
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure s =
        ⋃ (t : Set (normalPart S)) (_ : t ⊆ s) (_ : t.Finite),
          ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure t := by
  classical
  have hker (I : normalPart S) :
      ∃ f : S →L[ℂ] ℂ, (f.ker : Set S) = I.val.val := by
    obtain ⟨x, y, _hx, _hy, hI⟩ := I.property
    exact ⟨NonUnitalCStarRepresentation.matrixCoefficient
      (NonUnitalStarSubalgebraClass.subtype S) x y, hI⟩
  choose f hf using hker
  exact ClosureSpace.HullKernel.subspace_closure_eq_iUnion_finite
    (NormedSpace.geometricStructureFamily ℂ S)
    (NormedSpace.univ_notMem_geometricStructureFamily ℂ S)
    (normalPart S) (fun I => (f I).ker) hf

/-- The SAME point equivalence is a full homeomorphism when the two concrete
algebras are finite dimensional, independently of Hilbert dimensions. -/
def normalPartHomeomorphOfFiniteDimensional
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (T : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K))
    [IsClosed (S : Set (H →L[ℂ] H))] [IsClosed (T : Set (K →L[ℂ] K))]
    [FiniteDimensional ℂ S] [FiniteDimensional ℂ T]
    (f : ClosureSpace.FiniteHomeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T))) :
    ClosureSpace.Homeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) :=
  f.toHomeomorphOfFiniteCharacter
    (normalPart_closure_eq_iUnion_finite S) (normalPart_closure_eq_iUnion_finite T)

@[simp]
theorem normalPartHomeomorphOfFiniteDimensional_toEquiv
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (T : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K))
    [IsClosed (S : Set (H →L[ℂ] H))] [IsClosed (T : Set (K →L[ℂ] K))]
    [FiniteDimensional ℂ S] [FiniteDimensional ℂ T]
    (f : ClosureSpace.FiniteHomeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T))) :
    (normalPartHomeomorphOfFiniteDimensional S T f).toEquiv = f.toEquiv := rfl

/-- A concrete operator subalgebra is a finite-dimensional vector space if its
Hilbert space is finite dimensional. The inclusion is the literal subtype map. -/
theorem finiteDimensional_operator_subalgebra [FiniteDimensional ℂ H]
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) : FiniteDimensional ℂ S := by
  let i : S →ₗ[ℂ] (H →L[ℂ] H) :=
    { toFun := Subtype.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective i Subtype.coe_injective

attribute [local instance] ContinuousLinearMap.isClosed_compactOperatorStarSubalgebra
local notation "𝒦K" => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K

/-- Finite-dimensional compact targets need no forward-continuity inputs at
all: the given finite maps and their inverses upgrade by finite character. -/
theorem exists_compact_conjugate_homeomorph_of_finiteDimensional
    [Nontrivial K] [FiniteDimensional ℂ K]
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (S : Set (H →L[ℂ] H))]
    (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
    (f : ClosureSpace.FiniteHomeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      ((NormedSpace.geometricStructureClosure ℂ 𝒦K).subspace (normalPart 𝒦K)))
    (g : ClosureSpace.FiniteHomeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))) :
    ∃ h : ClosureSpace.Homeomorph
      ((NormedSpace.geometricStructureClosure ℂ 𝒦K).subspace (normalPart 𝒦K))
      ((NormedSpace.geometricStructureClosure ℂ 𝒦K).subspace (normalPart 𝒦K)),
      h.toEquiv = (f.conjugate g).toEquiv := by
  have hdim := finite_and_finrank_eq_of_normalPart_finiteHomeomorph
    𝒦K S (isIrreducible_compactOperatorRepresentation K) hS f.symm
    (Or.inl (inferInstance : Module.Finite ℂ K))
  letI : FiniteDimensional ℂ H := hdim.2.1
  letI : FiniteDimensional ℂ S := finiteDimensional_operator_subalgebra S
  letI : FiniteDimensional ℂ 𝒦K := finiteDimensional_operator_subalgebra 𝒦K
  let F := normalPartHomeomorphOfFiniteDimensional S 𝒦K f
  let G := normalPartHomeomorphOfFiniteDimensional S S g
  exact ⟨F.symm.trans (G.trans F), rfl⟩

/-- The finite and infinite target cases together. Only forward full
continuity of the input finite homeomorphisms is assumed. -/
theorem exists_compact_conjugate_homeomorph_all_dimensions [Nontrivial K]
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (S : Set (H →L[ℂ] H))]
    (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
    (f : ClosureSpace.FiniteHomeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      ((NormedSpace.geometricStructureClosure ℂ 𝒦K).subspace (normalPart 𝒦K)))
    (hf : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ 𝒦K).subspace (normalPart 𝒦K)) f.toEquiv)
    (g : ClosureSpace.FiniteHomeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)))
    (hg : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)) g.toEquiv) :
    ∃ h : ClosureSpace.Homeomorph
      ((NormedSpace.geometricStructureClosure ℂ 𝒦K).subspace (normalPart 𝒦K))
      ((NormedSpace.geometricStructureClosure ℂ 𝒦K).subspace (normalPart 𝒦K)),
      h.toEquiv = (f.conjugate g).toEquiv := by
  classical
  by_cases hK : FiniteDimensional ℂ K
  · letI : FiniteDimensional ℂ K := hK
    exact exists_compact_conjugate_homeomorph_of_finiteDimensional S hS f g
  · exact exists_compact_conjugate_homeomorph S hS hK f hf g hg

/-- All actual irreducible image tests, with independent source algebra and
Hilbert universes, for every nonzero compact target. -/
theorem hasImageNormalPartFiniteConjugation_compact_operators_all_dimensions [Nontrivial K] :
    ClosureSpace.HasImageNormalPartFiniteConjugation.{uA, uH, v}
      ((NormedSpace.geometricStructureClosure ℂ 𝒦K).subspace (normalPart 𝒦K)) := by
  intro A instA hA L instN instI instC pi hpi
  dsimp only
  intro f hf g hg
  letI : PartialOrder A := _root_.CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := _root_.CStarAlgebra.spectralOrderedRing A
  letI : Nontrivial L := NonUnitalCStarRepresentation.nontrivial_of_isNonzero pi hpi.1
  letI : IsClosed ((NonUnitalStarAlgHom.range pi) : Set (L →L[ℂ] L)) := HomKernelQuotient.isClosed_image pi
  have hi : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype (NonUnitalStarAlgHom.range pi)) :=
    (NonUnitalCStarRepresentation.isIrreducible_imageRepresentation_iff pi).2 hpi
  obtain ⟨h, hh⟩ := exists_compact_conjugate_homeomorph_all_dimensions (NonUnitalStarAlgHom.range pi) hi f hf g hg
  rw [← hh]
  exact ⟨h.continuous_toFun, h.continuous_invFun⟩

/-- The all-realizable-source property, using the existing small-GNS direction.
This does not put all Hilbert universes into a single type. -/
theorem hasContinuousFiniteConjugation_compact_operators_all_dimensions [Nontrivial K] :
    ((NormedSpace.geometricStructureClosure ℂ 𝒦K).subspace (normalPart 𝒦K)).HasContinuousFiniteConjugation (ClosureCat.IsCStarRealizable.{uA, uL}) := by
  have h : ClosureSpace.HasImageNormalPartFiniteConjugation.{uA, uA, v}
      ((NormedSpace.geometricStructureClosure ℂ 𝒦K).subspace (normalPart 𝒦K)) :=
    hasImageNormalPartFiniteConjugation_compact_operators_all_dimensions
  exact h.hasContinuousFiniteConjugation

end MathlibAnnex.Analysis.CStarAlgebra
