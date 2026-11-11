import MathlibAnnex.Analysis.CStarAlgebra.TypeI.PureStateExtension

set_option autoImplicit false
open Set
open scoped ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A]
variable (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
variable [PartialOrder D] [StarOrderedRing D]

-- The prescribed functional is arbitrary and is not assumed multiplicative.
example (phi : D →L[ℂ] ℂ) (hphi : IsPureState D phi) :
    ∃ psi : A →L[ℂ] ℂ,
      (∀ a : A, 0 ≤ a → 0 ≤ psi a) ∧ psi 1 = 1 ∧
      psi ∈ (stateSpace A).extremePoints ℝ ∧ ∀ d : D, psi d = phi d := by
  obtain ⟨psi, hstate, hpure, hext⟩ := exists_pure_state_extension D phi hphi
  exact ⟨psi, hstate.1, hstate.2, hpure, hext⟩

example (phi : D →L[ℂ] ℂ) (hphi : phi ∈ stateSpace D) :
    ∃ psi : A →L[ℂ] ℂ, psi 1 = 1 ∧
      (∀ a : A, 0 ≤ a → 0 ≤ psi a) ∧ ∀ d : D, psi d = phi d := by
  obtain ⟨psi, hstate, hext⟩ := exists_state_extension_of_mem_stateSpace D phi hphi
  exact ⟨psi, hstate.2, hstate.1, hext⟩

-- The actual pure extension includes the isometry of the concrete GNS spaces.
example (phi : D →L[ℂ] ℂ) (hphi : IsPureState D phi) :
    ∃ (psi : A →L[ℂ] ℂ) (hpsi : psi ∈ stateSpace A),
      psi ∈ (stateSpace A).extremePoints ℝ ∧ (∀ d : D, psi d = phi d) ∧
      ∃ U : (positiveLinearMapOfMemStateSpace phi hphi.1).GNS →ₗᵢ[ℂ]
          (positiveLinearMapOfMemStateSpace psi hpsi).GNS,
        U (stateGNSVector phi hphi.1) = stateGNSVector psi hpsi ∧
        ∀ (d : D) x,
          U ((positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom d x) =
            (positiveLinearMapOfMemStateSpace psi hpsi).gnsStarAlgHom (d : A) (U x) := by
  exact exists_pure_state_extension_with_gns_isometry D phi hphi

end MathlibAnnex.Analysis.CStarAlgebra
