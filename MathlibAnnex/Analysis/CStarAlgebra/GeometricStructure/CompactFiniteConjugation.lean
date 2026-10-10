/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.CompactOperatorSpectrum
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartClassificationConsequences
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartFiniteConjugation
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.SingletonFiniteConjugation
import MathlibAnnex.Analysis.InnerProductSpace.CompactSandwich
import MathlibAnnex.Analysis.Normed.Operator.SemilinearSandwich

/-!
# Finite conjugation with an infinite-dimensional compact-operator target

Only FORWARD full continuity of the two finite homeomorphisms is assumed.
The received normal-part classification supplies their actual bounded pairs.
The four global orientations are computed on every nonzero coefficient point.
The resulting bounded pair acts on the TARGET compact algebra, where the
proved compact sandwich equality gives a full homeomorphism. No equality of
the source operator algebra with its sandwich image is requested or used.

The irreducible-compact classification is dimension-free in the preceding file.
The forward test property here has an explicit infinite-dimensional target
hypothesis. Finite-dimensional finite-character exceptions remain separate.
Source-algebra, Hilbert and target universes are independently quantified.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v uA uH uL
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

attribute [local instance] ContinuousLinearMap.isClosed_compactOperatorStarSubalgebra

local notation "𝒦H" => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H
local notation "𝒦K" => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K

section CompactPair
variable [Nontrivial K]
variable {τ : ℂ →+* ℂ} [RingHomInvPair τ τ]

/-- A bounded pair of either scalar type gives a FULL homeomorphism of the
compact target. Both directions come from the compact sandwich equality. -/
theorem exists_compact_normalPart_homeomorph_of_scalar_type
    (hτ : ∀ c : ℂ, τ (star c) = star (τ c))
    (htype : τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ)
    (U V : K ≃SL[τ] K) :
    ∃ h : ClosureSpace.Homeomorph
        ((NormedSpace.geometricStructureClosure ℂ 𝒦K).subspace (normalPart 𝒦K))
        ((NormedSpace.geometricStructureClosure ℂ 𝒦K).subspace (normalPart 𝒦K)),
      h.toEquiv = normalPartSemilinearEquiv 𝒦K 𝒦K
        (isIrreducible_compactOperatorRepresentation K)
        (isIrreducible_compactOperatorRepresentation K)
        hτ U.toLinearEquiv V.toLinearEquiv := by
  rcases htype with rfl | rfl
  · exact ⟨normalPartLinearHomeomorph 𝒦K 𝒦K
      (isIrreducible_compactOperatorRepresentation K)
      (isIrreducible_compactOperatorRepresentation K) U V
      (InnerProductSpace.image_adjointSandwich_setOf_isCompactOperator U V), rfl⟩
  · exact ⟨normalPartConjugateLinearHomeomorph 𝒦K 𝒦K
      (isIrreducible_compactOperatorRepresentation K)
      (isIrreducible_compactOperatorRepresentation K) U V
      (InnerProductSpace.image_conjugateAdjointSandwich_setOf_isCompactOperator U V), rfl⟩

end CompactPair

section GivenPairs
variable [Nontrivial K]
variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable [IsClosed (S : Set (H →L[ℂ] H))]
variable (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
variable {σ τ : ℂ →+* ℂ} [RingHomInvPair σ σ] [RingHomInvPair τ τ]

/-- Compute all four GLOBAL direct/swap cases with actual bounded target pairs.
For direct/direct use `(UPU⁻¹,VQV⁻¹)`; direct/swap uses the swapped pair
`(VPU⁻¹,UQV⁻¹)`; swap/direct uses `(VQV⁻¹,UPU⁻¹)`; swap/swap uses
`(UQV⁻¹,VPU⁻¹)` and swaps. All representatives are nonzero and all inverse
laws come from the actual equivalences. Only the target compact sandwich
is used, never equality of a source-algebra sandwich. -/
theorem exists_compact_conjugate_homeomorph_of_bounded_pairs
    (hσ : ∀ c : ℂ, σ (star c) = star (σ c))
    (hτ : ∀ c : ℂ, τ (star c) = star (τ c))
    (hcomm : ∀ c : ℂ, σ (τ c) = τ (σ c))
    (htype : τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ)
    (U V : H ≃SL[σ] K) (P Q : H ≃SL[τ] H)
    (f : ClosureSpace.FiniteHomeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      ((NormedSpace.geometricStructureClosure ℂ 𝒦K).subspace (normalPart 𝒦K)))
    (g : ClosureSpace.FiniteHomeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)))
    (hf : f.toEquiv = normalPartSemilinearEquiv S 𝒦K hS
        (isIrreducible_compactOperatorRepresentation K) hσ U.toLinearEquiv V.toLinearEquiv ∨
      f.toEquiv = (normalPartSemilinearEquiv S 𝒦K hS
        (isIrreducible_compactOperatorRepresentation K) hσ U.toLinearEquiv V.toLinearEquiv).trans
          (normalPartStarHomeomorph 𝒦K (isIrreducible_compactOperatorRepresentation K)).toEquiv)
    (hg : g.toEquiv = normalPartSemilinearEquiv S S hS hS hτ
        P.toLinearEquiv Q.toLinearEquiv ∨
      g.toEquiv = (normalPartSemilinearEquiv S S hS hS hτ
        P.toLinearEquiv Q.toLinearEquiv).trans (normalPartStarHomeomorph S hS).toEquiv) :
    ∃ h : ClosureSpace.Homeomorph
        ((NormedSpace.geometricStructureClosure ℂ 𝒦K).subspace (normalPart 𝒦K))
        ((NormedSpace.geometricStructureClosure ℂ 𝒦K).subspace (normalPart 𝒦K)),
      h.toEquiv = (f.conjugate g).toEquiv := by
  let hK := isIrreducible_compactOperatorRepresentation K
  rcases normalPart_equiv_evaluation_of_semilinear_eq_or_star S 𝒦K hS hK f hσ
      U.toLinearEquiv V.toLinearEquiv hf with ⟨_, hff, hfi⟩ | ⟨_, hff, hfi⟩
  · rcases normalPart_equiv_evaluation_of_semilinear_eq_or_star S S hS hS g hτ
        P.toLinearEquiv Q.toLinearEquiv hg with ⟨_, hgg, _⟩ | ⟨_, hgg, _⟩
    · let A := ContinuousLinearEquiv.sandwichOfCommute hcomm U U P
      let B := ContinuousLinearEquiv.sandwichOfCommute hcomm V V Q
      obtain ⟨h, hh⟩ := exists_compact_normalPart_homeomorph_of_scalar_type hτ htype A B
      refine ⟨h, ?_⟩
      apply Equiv.ext
      intro I
      obtain ⟨z, w, hz, hw, rfl⟩ := exists_normalPartPoint_eq 𝒦K hK I
      rw [hh]
      change normalPartSemilinearMap 𝒦K 𝒦K hK A.toLinearEquiv B.toLinearEquiv
        (normalPartPoint 𝒦K hK z w hz hw) =
        f.toEquiv (g.toEquiv (f.toEquiv.symm (normalPartPoint 𝒦K hK z w hz hw)))
      rw [normalPartSemilinearMap_point 𝒦K 𝒦K hK hK hτ, hfi, hgg, hff]
      rfl
    · let A := ContinuousLinearEquiv.sandwichOfCommute hcomm V U P
      let B := ContinuousLinearEquiv.sandwichOfCommute hcomm U V Q
      obtain ⟨h, hh⟩ := exists_compact_normalPart_homeomorph_of_scalar_type hτ htype A B
      refine ⟨h.trans (normalPartStarHomeomorph 𝒦K hK), ?_⟩
      apply Equiv.ext
      intro I
      obtain ⟨z, w, hz, hw, rfl⟩ := exists_normalPartPoint_eq 𝒦K hK I
      change (normalPartStarHomeomorph 𝒦K hK).toEquiv
        (h.toEquiv (normalPartPoint 𝒦K hK z w hz hw)) =
        f.toEquiv (g.toEquiv (f.toEquiv.symm (normalPartPoint 𝒦K hK z w hz hw)))
      rw [hh]
      change (normalPartStarHomeomorph 𝒦K hK).toEquiv
        (normalPartSemilinearMap 𝒦K 𝒦K hK A.toLinearEquiv B.toLinearEquiv
          (normalPartPoint 𝒦K hK z w hz hw)) = _
      rw [normalPartSemilinearMap_point 𝒦K 𝒦K hK hK hτ, normalPartStarHomeomorph_point,
        hfi, hgg, hff]
      rfl
  · rcases normalPart_equiv_evaluation_of_semilinear_eq_or_star S S hS hS g hτ
        P.toLinearEquiv Q.toLinearEquiv hg with ⟨_, hgg, _⟩ | ⟨_, hgg, _⟩
    · let A := ContinuousLinearEquiv.sandwichOfCommute hcomm V V Q
      let B := ContinuousLinearEquiv.sandwichOfCommute hcomm U U P
      obtain ⟨h, hh⟩ := exists_compact_normalPart_homeomorph_of_scalar_type hτ htype A B
      refine ⟨h, ?_⟩
      apply Equiv.ext
      intro I
      obtain ⟨z, w, hz, hw, rfl⟩ := exists_normalPartPoint_eq 𝒦K hK I
      rw [hh]
      change normalPartSemilinearMap 𝒦K 𝒦K hK A.toLinearEquiv B.toLinearEquiv
        (normalPartPoint 𝒦K hK z w hz hw) =
        f.toEquiv (g.toEquiv (f.toEquiv.symm (normalPartPoint 𝒦K hK z w hz hw)))
      rw [normalPartSemilinearMap_point 𝒦K 𝒦K hK hK hτ, hfi, hgg, hff]
      rfl
    · let A := ContinuousLinearEquiv.sandwichOfCommute hcomm U V Q
      let B := ContinuousLinearEquiv.sandwichOfCommute hcomm V U P
      obtain ⟨h, hh⟩ := exists_compact_normalPart_homeomorph_of_scalar_type hτ htype A B
      refine ⟨h.trans (normalPartStarHomeomorph 𝒦K hK), ?_⟩
      apply Equiv.ext
      intro I
      obtain ⟨z, w, hz, hw, rfl⟩ := exists_normalPartPoint_eq 𝒦K hK I
      change (normalPartStarHomeomorph 𝒦K hK).toEquiv
        (h.toEquiv (normalPartPoint 𝒦K hK z w hz hw)) =
        f.toEquiv (g.toEquiv (f.toEquiv.symm (normalPartPoint 𝒦K hK z w hz hw)))
      rw [hh]
      change (normalPartStarHomeomorph 𝒦K hK).toEquiv
        (normalPartSemilinearMap 𝒦K 𝒦K hK A.toLinearEquiv B.toLinearEquiv
          (normalPartPoint 𝒦K hK z w hz hw)) = _
      rw [normalPartSemilinearMap_point 𝒦K 𝒦K hK hK hτ, normalPartStarHomeomorph_point,
        hfi, hgg, hff]
      rfl

include hS in
/-- The forward continuity inputs produce the needed bounded pairs. Infinite
dimensionality is required only of the compact target; that of the source
is deduced from the already proved finite-dimensional comparison. -/
theorem exists_compact_conjugate_homeomorph
    (hK : ¬ FiniteDimensional ℂ K)
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
  have hH : ¬ FiniteDimensional ℂ H :=
    not_finiteDimensional_of_normalPart_finiteHomeomorph 𝒦K S
      (isIrreducible_compactOperatorRepresentation K) hS f.symm hK
  have hfp := (exists_normalPart_selected_operator_inclusion S 𝒦K hS
    (isIrreducible_compactOperatorRepresentation K) f hH hf).2
  have hgp := (exists_normalPart_selected_operator_inclusion S S hS hS g hH hg).2
  rcases hfp with ⟨U, V, _, _, _, _, hfe, _, _⟩ | ⟨U, V, _, _, _, _, hfe, _, _⟩
  · rcases hgp with ⟨P, Q, _, _, _, _, hge, _, _⟩ | ⟨P, Q, _, _, _, _, hge, _, _⟩
    · exact exists_compact_conjugate_homeomorph_of_bounded_pairs
        (σ := RingHom.id ℂ) (τ := RingHom.id ℂ) S hS
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (Or.inl rfl) U V P Q f g hfe hge
    · exact exists_compact_conjugate_homeomorph_of_bounded_pairs
        (σ := RingHom.id ℂ) (τ := starRingEnd ℂ) S hS
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (Or.inr rfl) U V P Q f g hfe hge
  · rcases hgp with ⟨P, Q, _, _, _, _, hge, _, _⟩ | ⟨P, Q, _, _, _, _, hge, _, _⟩
    · exact exists_compact_conjugate_homeomorph_of_bounded_pairs
        (σ := starRingEnd ℂ) (τ := RingHom.id ℂ) S hS
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (Or.inl rfl) U V P Q f g hfe hge
    · exact exists_compact_conjugate_homeomorph_of_bounded_pairs
        (σ := starRingEnd ℂ) (τ := starRingEnd ℂ) S hS
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (Or.inr rfl) U V P Q f g hfe hge

end GivenPairs

/-- All actual nonzero irreducible images, on every separately specified
Hilbert universe, satisfy the compact-target test. No inverse continuity of
its input maps is added. -/
theorem hasImageNormalPartFiniteConjugation_compact_operators [Nontrivial K]
    (hK : ¬ FiniteDimensional ℂ K) :
    ClosureSpace.HasImageNormalPartFiniteConjugation.{uA, uH, v}
      ((NormedSpace.geometricStructureClosure ℂ 𝒦K).subspace (normalPart 𝒦K)) := by
  intro A instA hA L instN instI instC pi hpi
  dsimp only
  intro f hf g hg
  letI : PartialOrder A := _root_.CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := _root_.CStarAlgebra.spectralOrderedRing A
  letI : Nontrivial L := NonUnitalCStarRepresentation.nontrivial_of_isNonzero pi hpi.1
  letI : IsClosed ((NonUnitalStarAlgHom.range pi) : Set (L →L[ℂ] L)) := HomKernelQuotient.isClosed_image pi
  have hi : NonUnitalCStarRepresentation.IsIrreducible
    (NonUnitalStarSubalgebraClass.subtype (NonUnitalStarAlgHom.range pi)) :=
    (NonUnitalCStarRepresentation.isIrreducible_imageRepresentation_iff pi).2 hpi
  obtain ⟨h, hh⟩ := exists_compact_conjugate_homeomorph (NonUnitalStarAlgHom.range pi) hi hK f hf g hg
  rw [← hh]
  exact ⟨h.continuous_toFun, h.continuous_invFun⟩

/-- The all-realizable-source property follows from the actual small-GNS
reduction. The witness algebra universe and eligible source-carrier universe
are independent; the existing reduction supplies the correct direction. -/
theorem hasContinuousFiniteConjugation_compact_operators [Nontrivial K]
    (hK : ¬ FiniteDimensional ℂ K) :
    ((NormedSpace.geometricStructureClosure ℂ 𝒦K).subspace (normalPart 𝒦K)).HasContinuousFiniteConjugation
       (ClosureCat.IsCStarRealizable.{uA, uL}) := by
  have h : ClosureSpace.HasImageNormalPartFiniteConjugation.{uA, uA, v}
      ((NormedSpace.geometricStructureClosure ℂ 𝒦K).subspace (normalPart 𝒦K)) :=
    hasImageNormalPartFiniteConjugation_compact_operators hK
  exact h.hasContinuousFiniteConjugation

section GeneralModel
universe uModel
variable {A : Type uModel} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A] [Nontrivial K]

attribute [local instance] HomKernelQuotient.imageCStarAlgebra HomKernelQuotient.isClosed_image

/-- Transfer the infinite-Hilbert compact-target result to the FULL GSS of a
proved compact model, using the same representation and its literal preimage
homeomorphism. No new elementary-algebra definition is introduced. -/
theorem hasContinuousFiniteConjugation_of_isCompactOperatorModel
    (pi : NonUnitalCStarRepresentation A K) (hpi : IsCompactOperatorModel pi)
    (hK : ¬ FiniteDimensional ℂ K) :
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
    exact hasContinuousFiniteConjugation_compact_operators hK
  exact (singletonImageNormalPartHomeomorph hs pi hi).hasContinuousFiniteConjugation hn

/-- The existence-including component clause in the infinite-Hilbert forward
branch. Its singleton input is PROVED from the same compact model, not assumed. -/
theorem exists_component_hasContinuousFiniteConjugation_of_isCompactOperatorModel
    (pi : NonUnitalCStarRepresentation A K) (hpi : IsCompactOperatorModel pi)
    (hK : ¬ FiniteDimensional ℂ K) :
    ∃ I : NormedSpace.GeometricStructureSpace ℂ A,
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        ((NormedSpace.geometricStructureClosure ℂ A).component I)).HasContinuousFiniteConjugation
          (ClosureCat.IsCStarRealizable.{uA, uL}) := by
  have hi := isIrreducible_of_isCompactOperatorModel pi hpi
  letI : Nontrivial A := NonUnitalCStarRepresentation.nontrivial_algebra_of_isNonzero pi hi.1
  have hs := exists_forall_eq_irreducibleSpectrum_of_isCompactOperatorModel pi hpi
  obtain ⟨I, _⟩ := exists_forall_eq_irreducibleSpectrum_iff_exists_component_eq_univ.mp hs
  exact ⟨I, (singletonComponentHomeomorph hs I).symm.hasContinuousFiniteConjugation
    (hasContinuousFiniteConjugation_of_isCompactOperatorModel pi hpi hK)⟩

end GeneralModel

end MathlibAnnex.Analysis.CStarAlgebra
