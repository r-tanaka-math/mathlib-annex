import MathlibAnnex.Analysis.CStarAlgebra.CyclicTransport
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Adapters
import MathlibAnnex.Analysis.CStarAlgebra.Representation.VectorFunctional
import Mathlib.Analysis.Normed.Module.Normalize
import MathlibAnnex.Analysis.CStarAlgebra.PureStateGNS.State

/-!
# Vector states and their pointed GNS model

The construction works for an arbitrary target Hilbert space and arbitrary
universe.  A unit cyclic vector identifies its representation, by a genuine
unitary intertwiner, with the canonical GNS representation of its vector
state.
-/

set_option autoImplicit false

open Set
open scoped ComplexOrder InnerProduct

namespace MathlibAnnex.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open MathlibAnnex.Analysis.CStarAlgebra

/-- A unit vector in a unital star representation defines a state. -/
theorem vectorFunctional_mem_stateSpace
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (hξ : ‖ξ‖ = 1) :
    Representation.vectorFunctional pi ξ ∈ stateSpace A := by
  refine ⟨?_, Representation.vectorFunctional_one pi hξ⟩
  intro a ha
  exact Representation.vectorFunctional_nonnegative pi ξ ha

/-- The canonical positive functional associated to a unit vector state. -/
noncomputable def vectorPositiveFunctional
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (hξ : ‖ξ‖ = 1) : A →ₚ[ℂ] ℂ :=
  positiveLinearMapOfMemStateSpace (Representation.vectorFunctional pi ξ)
    (vectorFunctional_mem_stateSpace pi ξ hξ)

@[simp]
theorem vectorPositiveFunctional_apply
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (hξ : ‖ξ‖ = 1) (a : A) :
    vectorPositiveFunctional pi ξ hξ a = inner ℂ ξ (pi a ξ) :=
  rfl

/-- A unit cyclic representation is uniquely equivalent, as a pointed
representation, to the GNS model of its vector state. -/
theorem existsUnique_vectorStateGNSUnitary
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (hξ : ‖ξ‖ = 1)
    (hcyclic : DenseRange (StarAlgHom.orbitMap pi ξ)) :
    ∃! W : H ≃ₗᵢ[ℂ] (vectorPositiveFunctional pi ξ hξ).GNS,
      (∀ a, W (pi a ξ) =
        (vectorPositiveFunctional pi ξ hξ).gnsStarAlgHom a
          (_root_.PositiveLinearMap.gnsCyclicVector
            (vectorPositiveFunctional pi ξ hξ))) ∧
      W ξ = _root_.PositiveLinearMap.gnsCyclicVector
        (vectorPositiveFunctional pi ξ hξ) ∧
      ∀ a, (W : H →L[ℂ] (vectorPositiveFunctional pi ξ hξ).GNS).comp (pi a) =
        ((vectorPositiveFunctional pi ξ hξ).gnsStarAlgHom a).comp
          (W : H →L[ℂ] (vectorPositiveFunctional pi ξ hξ).GNS) := by
  apply StarAlgHom.existsUnique_pointedCyclicTransport
  · exact hcyclic
  · exact _root_.PositiveLinearMap.denseRange_gnsStarAlgHom_apply_gnsCyclicVector _
  · intro a
    calc
      inner ℂ ξ (pi a ξ) = vectorPositiveFunctional pi ξ hξ a :=
        (vectorPositiveFunctional_apply pi ξ hξ a).symm
      _ = inner ℂ (_root_.PositiveLinearMap.gnsCyclicVector _)
          ((vectorPositiveFunctional pi ξ hξ).gnsStarAlgHom a
            (_root_.PositiveLinearMap.gnsCyclicVector _)) :=
        (_root_.PositiveLinearMap.inner_gnsCyclicVector_gnsStarAlgHom _ a).symm

/-- The unpointed unitary equivalence extracted from the pointed theorem. -/
theorem vectorState_unitaryEquivalent_gns
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (hξ : ‖ξ‖ = 1)
    (hcyclic : DenseRange (StarAlgHom.orbitMap pi ξ)) :
    Representation.UnitaryEquivalent pi
      (vectorPositiveFunctional pi ξ hξ).gnsStarAlgHom := by
  obtain ⟨W, hW, -⟩ := existsUnique_vectorStateGNSUnitary pi ξ hξ hcyclic
  refine ⟨W, fun a x ↦ ?_⟩
  simpa using congrArg (fun T ↦ T x) (hW.2.2 a)

/-- Arbitrary-target coverage before the purity step: every explicitly
nonzero irreducible representation has a unit cyclic vector and is unitarily
equivalent to the genuine GNS representation of its vector state. -/
theorem irreducible_exists_vectorStateGNS
    (pi : Representation A H) (hirr : pi.IsIrreducible) :
    ∃ (ξ : H) (hξ : ‖ξ‖ = 1), DenseRange (StarAlgHom.orbitMap pi ξ) ∧
      Representation.vectorFunctional pi ξ ∈ stateSpace A ∧
      Representation.UnitaryEquivalent pi
        (vectorPositiveFunctional pi ξ hξ).gnsStarAlgHom := by
  letI : Nontrivial H := Representation.nontrivial_of_isNonzero pi hirr.1
  obtain ⟨eta, heta⟩ := exists_ne (0 : H)
  let ξ : H := NormedSpace.normalize eta
  have hξ_ne : ξ ≠ 0 := by
    simpa [ξ] using heta
  have hξ_norm : ‖ξ‖ = 1 := by
    exact NormedSpace.norm_normalize heta
  have hcyclic : DenseRange (StarAlgHom.orbitMap pi ξ) :=
    Representation.denseRange_orbitMap_of_isIrreducible pi hirr hξ_ne
  refine ⟨ξ, hξ_norm, hcyclic, vectorFunctional_mem_stateSpace pi ξ hξ_norm, ?_⟩
  exact vectorState_unitaryEquivalent_gns pi ξ hξ_norm hcyclic

end MathlibAnnex.CStarAlgebra
