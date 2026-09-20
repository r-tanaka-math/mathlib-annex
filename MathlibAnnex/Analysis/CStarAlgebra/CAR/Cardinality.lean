import MathlibAnnex.Analysis.CStarAlgebra.CAR.SeparableFaithful
import MathlibAnnex.Analysis.CStarAlgebra.Representation.SeparableCardinality
import MathlibAnnex.Analysis.CStarAlgebra.Representation.DensityLowerBound
import MathlibAnnex.Analysis.CStarAlgebra.Representation.DensityCharacter

/-!
# Cardinality and norm density of the fixed atomic counterexample

The upper bound comes from the already constructed faithful separable model.
The lower bound applies to every norm-dense subset of this same algebra.
The whole-carrier cardinality and norm density are distinguished throughout.
-/
set_option autoImplicit false
open Set
open scoped Cardinal ComplexOrder
namespace MathlibAnnex.CStarAlgebra.CAR
open MathlibAnnex.Analysis.CStarAlgebra MathlibAnnex.Topology

/-- The existing faithful separable representation bounds the fixed carrier. -/
theorem cardinalMk_atomicCounterexampleAlgebra_le_continuum :
    #AtomicCounterexampleAlgebra ≤ Cardinal.continuum := by
  letI : TopologicalSpace.SeparableSpace SeparableCounterexampleHilbertSpace :=
    separableSpace_separableCounterexampleHilbertSpace
  exact Representation.cardinalMk_le_continuum_of_injective
    separableCounterexampleRepresentation separableCounterexampleRepresentation_injective

/-- No norm-dense subset of the fixed algebra is smaller than the continuum. -/
theorem continuum_le_cardinalMk_dense_atomicCounterexampleAlgebra
    (s : Set AtomicCounterexampleAlgebra) (hs : Dense s) :
    Cardinal.continuum ≤ #s :=
  Representation.continuum_le_cardinalMk_dense_algebra_of_singleton_of_not_finiteDimensional
    (shellFamilyInclusion homogeneityShellFamily)
    (isUniqueIrreducibleModel_shellFamilyInclusion.{0} homogeneityShellFamily).2
    (not_finiteDimensional_shellFamilyTarget homogeneityShellFamily) s hs

/-- The cardinality of the underlying set of the fixed algebra is continuum. -/
theorem cardinalMk_atomicCounterexampleAlgebra :
    #AtomicCounterexampleAlgebra = Cardinal.continuum := by
  apply le_antisymm cardinalMk_atomicCounterexampleAlgebra_le_continuum
  simpa using continuum_le_cardinalMk_dense_atomicCounterexampleAlgebra Set.univ dense_univ

/-- The exact norm density of the same fixed algebra is continuum. -/
theorem hasDensityCharacter_atomicCounterexampleAlgebra :
    HasDensityCharacter AtomicCounterexampleAlgebra Cardinal.continuum :=
  HasDensityCharacter.of_cardinalMk_le_of_forall_dense
    cardinalMk_atomicCounterexampleAlgebra_le_continuum
    continuum_le_cardinalMk_dense_atomicCounterexampleAlgebra

/-- Under CH, the fixed algebra has exact norm density aleph one. CH is an
explicit premise, not an added axiom and not a conclusion asserted in ZFC. -/
theorem hasDensityCharacter_atomicCounterexampleAlgebra_of_continuum_eq_aleph_one
    (hCH : (Cardinal.continuum : Cardinal.{0}) = Cardinal.aleph 1) :
    HasDensityCharacter AtomicCounterexampleAlgebra (Cardinal.aleph 1) := by
  rw [← hCH]
  exact hasDensityCharacter_atomicCounterexampleAlgebra

/-- Every dense subset of the fixed irreducible Hilbert model is at least
continuum-sized. This is norm density, not algebraic Hamel dimension. -/
theorem continuum_le_cardinalMk_dense_atomicCounterexampleHilbert
    (s : Set (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert
      completedRootPureState)) (hs : Dense s) : Cardinal.continuum ≤ #s :=
  Representation.continuum_le_cardinalMk_dense_space_of_singleton_of_not_finiteDimensional
    (shellFamilyInclusion homogeneityShellFamily)
    (isUniqueIrreducibleModel_shellFamilyInclusion.{0} homogeneityShellFamily).2
    (not_finiteDimensional_shellFamilyTarget homogeneityShellFamily) s hs

/-- The cyclic orbit bounds the exact norm density of the fixed irreducible
Hilbert model from above; the general Rosenberg bound gives the reverse. -/
theorem hasDensityCharacter_atomicCounterexampleHilbert :
    HasDensityCharacter
      (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState)
      Cardinal.continuum := by
  let H := MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState
  let pi : Representation AtomicCounterexampleAlgebra H :=
    shellFamilyInclusion homogeneityShellFamily
  have hirr : Representation.IsIrreducible pi :=
    isIrreducible_shellFamilyInclusion homogeneityShellFamily
  letI : Nontrivial H := Representation.nontrivial_of_isNonzero pi hirr.1
  obtain ⟨x, hx⟩ : ∃ x : H, x ≠ 0 := exists_ne 0
  let s : Set H := Set.range (fun a : AtomicCounterexampleAlgebra => pi a x)
  have hs : Dense s := Representation.denseRange_orbitMap_of_isIrreducible pi hirr hx
  have hupper' : Cardinal.lift.{0} (#s) ≤
      Cardinal.lift.{0} (#AtomicCounterexampleAlgebra) := Cardinal.mk_range_le_lift
  have hupper : #s ≤ Cardinal.continuum := by
    simpa [cardinalMk_atomicCounterexampleAlgebra] using hupper'
  refine ⟨⟨s, hs, le_antisymm hupper
    (continuum_le_cardinalMk_dense_atomicCounterexampleHilbert s hs)⟩,
    continuum_le_cardinalMk_dense_atomicCounterexampleHilbert⟩

/-- The faithful separable model is infinite-dimensional: otherwise its
operator algebra, and hence the faithfully represented source, would be finite-dimensional. -/
theorem not_finiteDimensional_separableCounterexampleHilbertSpace :
    ¬ FiniteDimensional ℂ SeparableCounterexampleHilbertSpace := by
  intro hfinite
  letI : FiniteDimensional ℂ SeparableCounterexampleHilbertSpace := hfinite
  letI : FiniteDimensional ℂ
      (SeparableCounterexampleHilbertSpace →L[ℂ] SeparableCounterexampleHilbertSpace) :=
    ContinuousLinearMap.finiteDimensional
  exact (not_finiteDimensional_shellFamilyTarget homogeneityShellFamily)
    (FiniteDimensional.of_injective
      (LinearMapClass.linearMap separableCounterexampleRepresentation)
      separableCounterexampleRepresentation_injective)

end MathlibAnnex.CStarAlgebra.CAR
