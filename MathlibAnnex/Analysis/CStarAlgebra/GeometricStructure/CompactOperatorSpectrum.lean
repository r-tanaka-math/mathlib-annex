/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactOperators
import MathlibAnnex.Analysis.CStarAlgebra.CompactModelEquiv
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.Representatives
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.SurjectiveRepresentation
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.SpectrumSingleton

/-!
# The actual irreducible spectrum of a compact-operator model

The independently defined spectrum is the quotient of genuine pure-state GNS
representatives by actual unitary equivalence. The corner classification is
transported through the existing star equivalence of a compact model; neither
primitive-kernel equality nor faithfulness of an arbitrary irreducible action is
used as a substitute. The zero Hilbert space gives an EMPTY spectrum. Existence
is retained in the nonzero singleton statement.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : Type w} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
open NonUnitalCStarRepresentation

attribute [local instance] ContinuousLinearMap.isClosed_compactOperatorStarSubalgebra

/-- The actual inclusion is a compact model in the already fixed definition. -/
theorem isCompactOperatorModel_compactOperatorRepresentation :
    IsCompactOperatorModel (compactOperatorRepresentation H) :=
  ⟨compactOperatorRepresentation_injective H, fun a => a.property,
    fun T hT => ⟨⟨T, hT⟩, rfl⟩⟩

/-- The representation range is literally the compact star subalgebra. -/
theorem range_compactOperatorRepresentation :
    (NonUnitalStarAlgHom.range (compactOperatorRepresentation H)) =
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H := by
  ext T
  constructor
  · intro hT
    obtain ⟨a, rfl⟩ := (NonUnitalStarAlgHom.mem_range _).1 hT
    exact a.property
  · intro hT
    exact (NonUnitalStarAlgHom.mem_range _).2 ⟨⟨T, hT⟩, rfl⟩

/-- Any proved compact model has precisely the existing compact carrier as range. -/
theorem range_eq_compactOperatorStarSubalgebra_of_isCompactOperatorModel
    (pi : NonUnitalCStarRepresentation A H) (hpi : IsCompactOperatorModel pi) :
    (NonUnitalStarAlgHom.range pi) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H := by
  ext T
  constructor
  · intro hT
    obtain ⟨a, rfl⟩ := (NonUnitalStarAlgHom.mem_range pi).1 hT
    exact hpi.2.1 a
  · intro hT
    exact (NonUnitalStarAlgHom.mem_range pi).2 (hpi.2.2 T hT)

/-- A nonzero compact model is irreducible, by the actual star isomorphism. -/
theorem isIrreducible_of_isCompactOperatorModel [Nontrivial H]
    (pi : NonUnitalCStarRepresentation A H) (hpi : IsCompactOperatorModel pi) :
    pi.IsIrreducible := by
  let E := compactOperatorStarAlgEquiv pi hpi
  have hc : (compactOperatorRepresentation H).comp E.toNonUnitalStarAlgHom = pi := by
    ext a x
    rfl
  have hi := (isIrreducible_comp_iff_of_surjective (compactOperatorRepresentation H)
    E.toNonUnitalStarAlgHom E.surjective).2 (isIrreducible_compactOperatorRepresentation H)
  rwa [hc] at hi

/-- Transport the actual corner unitary through a proved compact model.
The unitary acts between the original Hilbert spaces and intertwines `pi` itself. -/
theorem unitaryEquivalent_of_isCompactOperatorModel [Nontrivial H]
    (pi : NonUnitalCStarRepresentation A H) (hpi : IsCompactOperatorModel pi)
    (rho : NonUnitalCStarRepresentation A L) (hrho : rho.IsIrreducible) :
    pi.UnitaryEquivalent rho := by
  let E := compactOperatorStarAlgEquiv pi hpi
  let sigma := rho.comp E.symm.toNonUnitalStarAlgHom
  have hsigma : NonUnitalCStarRepresentation.IsIrreducible sigma :=
    (isIrreducible_comp_iff_of_surjective rho E.symm.toNonUnitalStarAlgHom
      E.symm.surjective).2 hrho
  obtain ⟨U, hU⟩ := unitaryEquivalent_compactOperatorRepresentation sigma hsigma
  refine ⟨U, fun a x => ?_⟩
  have h := hU (E a) x
  change U ((E a).val x) = rho (E.symm (E a)) (U x) at h
  rw [E.symm_apply_apply] at h
  exact h

section Spectrum
variable [PartialOrder A] [StarOrderedRing A]

/-- Existence-including singleton of the independent pure-GNS spectrum. -/
theorem exists_forall_eq_irreducibleSpectrum_of_isCompactOperatorModel [Nontrivial H]
    (pi : NonUnitalCStarRepresentation A H) (hpi : IsCompactOperatorModel pi) :
    ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q := by
  have hi := isIrreducible_of_isCompactOperatorModel pi hpi
  refine ⟨IrreducibleSpectrum.ofRepresentation pi hi, ?_⟩
  intro r
  obtain ⟨phi, rfl⟩ := IrreducibleSpectrum.ofPureState_surjective r
  exact ((IrreducibleSpectrum.ofRepresentation_eq_ofPureState_iff pi hi phi).2
    (unitaryEquivalent_of_isCompactOperatorModel pi hpi phi.gnsRepresentation
      phi.isIrreducible_gnsRepresentation)).symm

end Spectrum

-- The concrete spectrum uses the canonical spectral order locally.
attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

private abbrev compactModelSpectrumOrder :
    PartialOrder (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) :=
  _root_.CStarAlgebra.spectralOrder _

attribute [local instance] compactModelSpectrumOrder

private abbrev compactModelSpectrumStarOrder :
    StarOrderedRing (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) :=
  _root_.CStarAlgebra.spectralOrderedRing _

attribute [local instance] compactModelSpectrumStarOrder

/-- Every nonzero Hilbert space has the genuine one-point compact spectrum. -/
theorem exists_forall_eq_irreducibleSpectrum_compact_operators [Nontrivial H] :
    ∃ q : IrreducibleSpectrum (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H),
      ∀ r : IrreducibleSpectrum (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H), r = q :=
  exists_forall_eq_irreducibleSpectrum_of_isCompactOperatorModel
    (compactOperatorRepresentation H) isCompactOperatorModel_compactOperatorRepresentation

/-- No pure-GNS representative exists when the Hilbert space is zero. -/
theorem isEmpty_irreducibleSpectrum_compact_operators_of_subsingleton [Subsingleton H] :
    IsEmpty (IrreducibleSpectrum (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H)) := by
  refine ⟨fun q => ?_⟩
  obtain ⟨phi, rfl⟩ := IrreducibleSpectrum.ofPureState_surjective q
  obtain ⟨a, ha⟩ := phi.isIrreducible_gnsRepresentation.1
  have hazero : a = 0 := Subtype.ext (Subsingleton.elim _ _)
  exact ha (by rw [hazero, map_zero])

/-- In particular, a subsingleton EMPTY spectrum is not called a singleton. -/
theorem exists_forall_eq_irreducibleSpectrum_compact_operators_iff :
    (∃ q : IrreducibleSpectrum (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H),
      ∀ r : IrreducibleSpectrum (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H), r = q) ↔
      Nontrivial H := by
  classical
  constructor
  · rintro ⟨q, _⟩
    apply not_subsingleton_iff_nontrivial.mp
    intro hH
    letI : Subsingleton H := hH
    letI := isEmpty_irreducibleSpectrum_compact_operators_of_subsingleton (H := H)
    exact isEmptyElim q
  · intro hH
    letI := hH
    exact exists_forall_eq_irreducibleSpectrum_compact_operators

/-- Full normality is derived from the actual singleton classification. -/
theorem normalPart_compactOperatorStarSubalgebra_eq_univ [Nontrivial H] :
    normalPart (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) = Set.univ := by
  let pi := compactOperatorRepresentation H
  have hi : pi.IsIrreducible := isIrreducible_compactOperatorRepresentation H
  letI : Nontrivial (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) :=
    nontrivial_algebra_of_isNonzero pi hi.1
  have h := (faithful_and_normalPart_eq_univ_of_singleton_irreducibleSpectrum
    exists_forall_eq_irreducibleSpectrum_compact_operators pi hi).2
  rwa [range_compactOperatorRepresentation] at h

end MathlibAnnex.Analysis.CStarAlgebra
