import MathlibAnnex.Topology.CompactCardinality
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.DensityLowerBound
import MathlibAnnex.Analysis.CStarAlgebra.Representation.DensityLowerBound
import Mathlib.Topology.Bases

/-!
Signature tests for the downstream build lane.  These tests have not been
executed in this integration preparation.  They deliberately expose the full
compact-range conclusion and keep the algebra and Hilbert universes distinct.
-/

set_option autoImplicit false

open Set Function
open scoped Cardinal ComplexOrder

universe u v

section Topology

variable {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X]
  [T2Space X] [Nonempty X]

-- No metrizability, zero-dimensionality, countability, or CH hypothesis.
example (hX : #X < Cardinal.continuum) : ∃ x : X, IsOpen ({x} : Set X) :=
  MathlibAnnex.Topology.exists_isOpen_singleton_of_cardinalMk_lt_continuum hX

example (hX : ∀ x : X, ¬ IsOpen ({x} : Set X)) : Cardinal.continuum ≤ #X :=
  MathlibAnnex.Topology.continuum_le_cardinalMk_of_not_isOpen_singleton hX

end Topology

section Nonunital

open MathlibAnnex.Analysis.CStarAlgebra

variable {A : Type u} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- No unitality, faithfulness, simplicity, or separability premise.
example (pi : NonUnitalCStarRepresentation A H)
    (hpi : NonUnitalCStarRepresentation.IsSingletonIrreducibleModel.{u, v, u} pi)
    (s : Set H) (hs : Dense s) (hcard : #s < Cardinal.continuum) :
    Injective pi ∧ (∀ a : A, IsCompactOperator (pi a)) ∧
      ∀ T : H →L[ℂ] H, IsCompactOperator T → ∃ a : A, pi a = T :=
  NonUnitalCStarRepresentation.isCompactOperatorModel_of_singleton_of_dense pi hpi s hs hcard

example (pi : NonUnitalCStarRepresentation A H)
    (hpi : NonUnitalCStarRepresentation.IsSingletonIrreducibleModel.{u, v, u} pi)
    (hnot : ¬ IsCompactOperatorModel pi) :
    ∀ s : Set A, Dense s → Cardinal.continuum ≤ #s := by
  intro s hs
  exact NonUnitalCStarRepresentation.continuum_le_cardinalMk_dense_algebra_of_singleton_of_not_isCompactOperatorModel
      pi hpi hnot s hs

example (pi : NonUnitalCStarRepresentation A H)
    (hpi : NonUnitalCStarRepresentation.IsSingletonIrreducibleModel.{u, v, u} pi)
    (hnot : ¬ IsCompactOperatorModel pi) :
    ∀ s : Set H, Dense s → Cardinal.continuum ≤ #s := by
  intro s hs
  exact NonUnitalCStarRepresentation.continuum_le_cardinalMk_dense_space_of_singleton_of_not_isCompactOperatorModel
      pi hpi hnot s hs

-- The old separable-Hilbert hypothesis is a genuine specialization.
example [TopologicalSpace.SeparableSpace H]
    (pi : NonUnitalCStarRepresentation A H)
    (hpi : NonUnitalCStarRepresentation.IsSingletonIrreducibleModel.{u, v, u} pi) :
    IsCompactOperatorModel pi := by
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense H
  exact NonUnitalCStarRepresentation.isCompactOperatorModel_of_singleton_of_dense
    pi hpi s hsd (hsc.le_aleph0.trans_lt Cardinal.aleph0_lt_continuum)

end Nonunital

section Unital

open MathlibAnnex.Analysis.CStarAlgebra

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (pi : Representation A H)
    (hpi : Representation.IsSingletonIrreducibleModel.{u, v, u} pi)
    (s : Set H) (hs : Dense s) (hcard : #s < Cardinal.continuum) :
    FiniteDimensional ℂ A :=
  Representation.finiteDimensional_algebra_of_singleton_of_dense pi hpi s hs hcard

example (pi : Representation A H)
    (hpi : Representation.IsSingletonIrreducibleModelAmongNonUnital.{u, v, u} pi)
    (hA : ¬ FiniteDimensional ℂ A) (s : Set A) (hs : Dense s) :
    Cardinal.continuum ≤ #s :=
  Representation.continuum_le_cardinalMk_dense_algebra_of_singleton_amongNonUnital_of_not_finiteDimensional
      pi hpi hA s hs

end Unital
