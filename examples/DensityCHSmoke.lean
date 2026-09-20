import MathlibAnnex.Projects.Naimark
import MathlibAnnex.Projects.Rosenberg

set_option autoImplicit false
open Function Set
open scoped Cardinal ComplexOrder
open MathlibAnnex.Topology MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.CStarAlgebra.CAR
universe u v

-- Both the witness and the lower bound are present in exact density.
example {X : Type u} [TopologicalSpace X] {κ : Cardinal.{u}}
    (h : HasDensityCharacter X κ) :
    (∃ s : Set X, Dense s ∧ #s = κ) ∧ ∀ s : Set X, Dense s → κ ≤ #s := h

-- The upper bound is about operators as a SET, not norm separability of B(H).
example {A : Type u} [NonUnitalCStarAlgebra A] {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (pi : NonUnitalCStarRepresentation A H) (hpi : Injective pi) :
    #A ≤ Cardinal.continuum :=
  NonUnitalCStarRepresentation.cardinalMk_le_continuum_of_injective pi hpi

-- This direction is arbitrary and genuinely nonunital, with independent universes.
-- In particular no faithful separable model, simplicity or CH is assumed here.
example {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Nontrivial A] {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (pi : NonUnitalCStarRepresentation A H)
    (hpi : NonUnitalCStarRepresentation.IsSingletonIrreducibleModel.{u,v,u} pi)
    (hnot : ¬ IsCompactOperatorModel pi)
    (hd : HasDensityCharacter A (Cardinal.aleph 1)) :
    (Cardinal.continuum : Cardinal.{u}) = Cardinal.aleph 1 :=
  NonUnitalCStarRepresentation.continuum_eq_aleph_one_of_singleton_of_not_isCompactOperatorModel_of_hasDensityCharacter
    pi hpi hnot hd

example : #MathlibAnnex.CStarAlgebra.CAR.AtomicCounterexampleAlgebra = Cardinal.continuum :=
  cardinalMk_atomicCounterexampleAlgebra
example : HasDensityCharacter MathlibAnnex.CStarAlgebra.CAR.AtomicCounterexampleAlgebra
    Cardinal.continuum :=
  hasDensityCharacter_atomicCounterexampleAlgebra
example : HasDensityCharacter
    (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState)
    Cardinal.continuum := hasDensityCharacter_atomicCounterexampleHilbert
example : ¬ FiniteDimensional ℂ SeparableCounterexampleHilbertSpace :=
  not_finiteDimensional_separableCounterexampleHilbertSpace
example : ExistsNaimarkCounterexampleOfDensity (Cardinal.continuum : Cardinal.{0}) :=
  existsNaimarkCounterexampleOfDensity_continuum
example : (Cardinal.continuum : Cardinal.{0}) = Cardinal.aleph 1 ↔
    ExistsNaimarkCounterexampleOfDensity (Cardinal.aleph 1 : Cardinal.{0}) :=
  continuum_eq_aleph_one_iff_existsNaimarkCounterexampleOfDensity
example : AtomicCounterexampleEndpoint.{v} ∧
    #MathlibAnnex.CStarAlgebra.CAR.AtomicCounterexampleAlgebra = Cardinal.continuum ∧
    HasDensityCharacter MathlibAnnex.CStarAlgebra.CAR.AtomicCounterexampleAlgebra
      Cardinal.continuum :=
  atomicCounterexampleEndpoint_and_cardinality_and_density

#print axioms MathlibAnnex.CStarAlgebra.CAR.continuum_eq_aleph_one_iff_existsNaimarkCounterexampleOfDensity
