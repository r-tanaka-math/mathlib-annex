/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartFiniteCharacter
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.ElementaryOfFiniteConjugation

/-!
# Compact-operator models characterized by singleton and finite conjugation

This is a small joint endpoint, not a new definition of `IsElementary`.
The model is the existing `IsCompactOperatorModel`; the iff uses a pure GNS
model in the source-algebra universe. Any given compact model on a separately
specified Hilbert universe also gives such a GNS model by the theorem below.

The source-class carrier is `max u w` for the converse. That converse needs
access to the actual small GNS and its full bounded-operator algebra. No large
witness is shrunk, and no collection of all universes is made into a type.

Theorem 7.7 in the supplied paper assumes nonseparability. Here the finite
character argument supplies its previously separate finite-target branch, so
the characterization is stated for every nontrivial complex C-star algebra.
The printed theorem is a specialization, not a change to the historical text.
- Only forward full continuity of the tested finite maps is assumed.
- A zero Hilbert space is not counted as a singleton spectrum.
- No isometry assertion about the selected bounded conjugation maps is made.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w uA uL
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] HomKernelQuotient.imageCStarAlgebra HomKernelQuotient.isClosed_image

/-- The forward property on the FULL geometric structure space of a given
nonzero compact model, in all Hilbert dimensions. The same pi and preimage
homeomorphism are used; the source-class universes are independent. -/
theorem hasContinuousFiniteConjugation_of_isCompactOperatorModel_all_dimensions
    [Nontrivial H] (pi : NonUnitalCStarRepresentation A H)
    (hpi : IsCompactOperatorModel pi) :
    (NormedSpace.geometricStructureClosure ℂ A).HasContinuousFiniteConjugation
      (ClosureCat.IsCStarRealizable.{uA, uL}) := by
  have hi := isIrreducible_of_isCompactOperatorModel pi hpi
  letI : Nontrivial A := NonUnitalCStarRepresentation.nontrivial_algebra_of_isNonzero pi hi.1
  have hs := exists_forall_eq_irreducibleSpectrum_of_isCompactOperatorModel pi hpi
  have hrange := range_eq_compactOperatorStarSubalgebra_of_isCompactOperatorModel pi hpi
  have hn : ((NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range pi)).subspace (normalPart (NonUnitalStarAlgHom.range pi))).HasContinuousFiniteConjugation
      (ClosureCat.IsCStarRealizable.{uA, uL}) := by
    dsimp +instances only [HomKernelQuotient.imageCStarAlgebra,
      NonUnitalStarSubalgebra.nonUnitalCStarAlgebra]
    rw [hrange]
    exact hasContinuousFiniteConjugation_compact_operators_all_dimensions
  exact (singletonImageNormalPartHomeomorph hs pi hi).hasContinuousFiniteConjugation hn

/-- The existence-including component condition follows from the SAME given
model, including Hilbert dimensions one and two. -/
theorem exists_component_hasContinuousFiniteConjugation_of_isCompactOperatorModel_all_dimensions
    [Nontrivial H] (pi : NonUnitalCStarRepresentation A H)
    (hpi : IsCompactOperatorModel pi) :
    ∃ I : NormedSpace.GeometricStructureSpace ℂ A,
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        ((NormedSpace.geometricStructureClosure ℂ A).component I)).HasContinuousFiniteConjugation
          (ClosureCat.IsCStarRealizable.{uA, uL}) := by
  have hi := isIrreducible_of_isCompactOperatorModel pi hpi
  letI : Nontrivial A := NonUnitalCStarRepresentation.nontrivial_algebra_of_isNonzero pi hi.1
  have hs := exists_forall_eq_irreducibleSpectrum_of_isCompactOperatorModel pi hpi
  obtain ⟨I, _⟩ := exists_forall_eq_irreducibleSpectrum_iff_exists_component_eq_univ.mp hs
  exact ⟨I, (singletonComponentHomeomorph hs I).symm.hasContinuousFiniteConjugation
    (hasContinuousFiniteConjugation_of_isCompactOperatorModel_all_dimensions pi hpi)⟩

/-- Minimal joint iff for Theorem 7.7, generalized to nontrivial A. Both the
singleton and the target-component quantifiers include existence. The strong
R23 endpoint still records the same faithful pi, star isomorphism and literal
preimage homeomorphism, rather than having those witnesses reselected here. -/
theorem exists_pureState_compactOperatorModel_iff_singleton_finiteConjugation
    [Nontrivial A] :
    (∃ phi : NonUnitalPureState A, IsCompactOperatorModel phi.gnsRepresentation) ↔
      (∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q) ∧
      ∃ I : NormedSpace.GeometricStructureSpace ℂ A,
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)).HasContinuousFiniteConjugation
            (ClosureCat.IsCStarRealizable.{u, max u w}) := by
  constructor
  · rintro ⟨phi, hmodel⟩
    letI : Nontrivial phi.GNS := NonUnitalCStarRepresentation.nontrivial_of_isNonzero
      phi.gnsRepresentation phi.isIrreducible_gnsRepresentation.1
    exact ⟨exists_forall_eq_irreducibleSpectrum_of_isCompactOperatorModel
        phi.gnsRepresentation hmodel,
      exists_component_hasContinuousFiniteConjugation_of_isCompactOperatorModel_all_dimensions
        phi.gnsRepresentation hmodel⟩
  · rintro ⟨hsingle, hproperty⟩
    obtain ⟨phi, _hfaith, _hnormal, _r, _hr, hmodel, _hrest⟩ :=
      exists_faithful_compactOperatorModel_of_singleton_finiteConjugation hsingle hproperty
    exact ⟨phi, hmodel⟩

/-- A model on ANY separately specified Hilbert universe gives a pure-GNS
compact model in the algebra's own universe. This is proved through the actual
forward property and the existing converse, not by an unproved Small instance. -/
theorem exists_pureState_compactOperatorModel_of_isCompactOperatorModel
    [Nontrivial H] (pi : NonUnitalCStarRepresentation A H)
    (hpi : IsCompactOperatorModel pi) :
    ∃ phi : NonUnitalPureState A, IsCompactOperatorModel phi.gnsRepresentation := by
  have hi := isIrreducible_of_isCompactOperatorModel pi hpi
  letI : Nontrivial A := NonUnitalCStarRepresentation.nontrivial_algebra_of_isNonzero pi hi.1
  have hp : ∃ I : NormedSpace.GeometricStructureSpace ℂ A,
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        ((NormedSpace.geometricStructureClosure ℂ A).component I)).HasContinuousFiniteConjugation
          (ClosureCat.IsCStarRealizable.{u, u}) :=
    exists_component_hasContinuousFiniteConjugation_of_isCompactOperatorModel_all_dimensions pi hpi
  exact (exists_pureState_compactOperatorModel_iff_singleton_finiteConjugation.{u, 0}).mpr
    ⟨exists_forall_eq_irreducibleSpectrum_of_isCompactOperatorModel pi hpi, hp⟩

/-- Remark 7.8: the component condition (ii) itself is invariant under a full
GSS homeomorphism. Neither singleton spectrum nor compactness is an input.
The SAME universally quantified source class is kept in both directions. -/
theorem exists_component_finiteConjugation_iff_of_geometricStructure_homeomorph
    {B : Type v} [NonUnitalCStarAlgebra B]
    (e : ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B)) :
    (∃ I : NormedSpace.GeometricStructureSpace ℂ A,
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        ((NormedSpace.geometricStructureClosure ℂ A).component I)).HasContinuousFiniteConjugation
          (ClosureCat.IsCStarRealizable.{uA, uL})) ↔
    (∃ J : NormedSpace.GeometricStructureSpace ℂ B,
      ((NormedSpace.geometricStructureClosure ℂ B).subspace
        ((NormedSpace.geometricStructureClosure ℂ B).component J)).HasContinuousFiniteConjugation
          (ClosureCat.IsCStarRealizable.{uA, uL})) :=
  e.exists_hasContinuousFiniteConjugation_component_iff

end MathlibAnnex.Analysis.CStarAlgebra
