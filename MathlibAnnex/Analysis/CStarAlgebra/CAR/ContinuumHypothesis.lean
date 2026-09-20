import MathlibAnnex.Analysis.CStarAlgebra.CAR.Cardinality

/-!
# CH and a Naimark counterexample of norm density aleph one

The forward direction uses the same concrete algebra and faithful separable
representation as the existing endpoint. The reverse direction is the general
(possibly nonunital) density obstruction, without a separable-representation
assumption. This is a mathematical biconditional, not a metatheoretic forcing
or independence certificate.
-/
set_option autoImplicit false
open scoped Cardinal ComplexOrder
namespace MathlibAnnex.CStarAlgebra.CAR
universe v
open MathlibAnnex.Analysis.CStarAlgebra MathlibAnnex.Topology

/-- The fixed construction supplies an ordinary counterexample of exact
norm density continuum. This existence assertion has no CH premise. -/
theorem existsNaimarkCounterexampleOfDensity_continuum :
    ExistsNaimarkCounterexampleOfDensity (Cardinal.continuum : Cardinal.{0}) := by
  refine ⟨AtomicCounterexampleAlgebra, inferInstance, inferInstance, inferInstance,
    inferInstance,
    MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState,
    inferInstance, inferInstance, inferInstance,
    (shellFamilyInclusion homogeneityShellFamily).toNonUnitalStarAlgHom, ?_, ?_,
    hasDensityCharacter_atomicCounterexampleAlgebra⟩
  · exact
      Representation.IsSingletonIrreducibleModelAmongNonUnital.isSingletonIrreducibleModel_toNonUnitalStarAlgHom
        (isUniqueIrreducibleModelAmongNonUnital_shellFamilyInclusion.{0}
          homogeneityShellFamily).2
  · exact not_isCompactOperatorModel_shellFamilyTarget homogeneityShellFamily _

/-- CH is equivalent to the existence of an ordinary possibly nonunital
Naimark counterexample of exact norm density aleph one. Carriers in this closed
existence statement lie in Type; the reverse obstruction is universe-polymorphic. -/
theorem continuum_eq_aleph_one_iff_existsNaimarkCounterexampleOfDensity :
    (Cardinal.continuum : Cardinal.{0}) = Cardinal.aleph 1 ↔
      ExistsNaimarkCounterexampleOfDensity (Cardinal.aleph 1 : Cardinal.{0}) := by
  constructor
  · intro hCH
    rw [← hCH]
    exact existsNaimarkCounterexampleOfDensity_continuum
  · exact continuum_eq_aleph_one_of_existsNaimarkCounterexampleOfDensity

/-- Under not-CH no such aleph-one-density counterexample exists.
This is the contrapositive, not an independence claim. -/
theorem not_existsNaimarkCounterexampleOfDensity_aleph_one_of_continuum_ne_aleph_one
    (hCH : (Cardinal.continuum : Cardinal.{0}) ≠ Cardinal.aleph 1) :
    ¬ ExistsNaimarkCounterexampleOfDensity (Cardinal.aleph 1 : Cardinal.{0}) := by
  intro h
  exact hCH (continuum_eq_aleph_one_iff_existsNaimarkCounterexampleOfDensity.mpr h)

/-- Cardinality and exact density augment the unchanged ordinary endpoint,
which still ranges over an arbitrary comparison universe. -/
theorem atomicCounterexampleEndpoint_and_cardinality_and_density :
    AtomicCounterexampleEndpoint.{v} ∧
    #AtomicCounterexampleAlgebra = Cardinal.continuum ∧
    HasDensityCharacter AtomicCounterexampleAlgebra Cardinal.continuum :=
  ⟨atomicCounterexampleEndpoint, cardinalMk_atomicCounterexampleAlgebra,
    hasDensityCharacter_atomicCounterexampleAlgebra⟩

end MathlibAnnex.CStarAlgebra.CAR
