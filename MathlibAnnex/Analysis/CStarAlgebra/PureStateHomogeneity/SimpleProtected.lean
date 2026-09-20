import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.SimpleRepresentation
import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.ProtectedState

/-!
# Protected local transport for an infinite-dimensional simple algebra

Simplicity removes the representation-kernel and compact-image hypotheses.
An actual protected finite row is still required; no general row supplier
is asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.CStarAlgebra

open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem exists_protected_state_transport_of_simple_row
    (hsimple : IsSimpleCStarAlgebra A)
    (hinfinite : ¬ FiniteDimensional ℂ A)
    (pi : Representation A H) (hpi : pi.IsIrreducible)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hpure : IsPureState A phi)
    (xi : H) (hxi : ‖xi‖ = 1)
    (hcoeff : ∀ a : A, phi a = inner ℂ xi (pi a xi))
    (F : Finset A) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {n : ℕ} (x : Fin n → A)
    (hq : ‖MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x‖ ≤ 1)
    (hqxi : pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x) xi = xi)
    (hprotect : ∀ a ∈ F, ∀ h : A,
      ‖a * MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h -
        MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h * a‖ ≤
        ((epsilon / 2) / (8 * Real.pi)) * ‖h‖) :
    ∃ G : Finset A, ∃ delta : ℝ, 0 < delta ∧
      ∀ psi : A →L[ℂ] ℂ, psi ∈ stateSpace A → IsPureState A psi →
        (∀ a ∈ G, ‖phi a - psi a‖ < delta) →
        ∀ T : Finset A, ∀ eta : ℝ, 0 < eta →
          ∃ u : unitary A, ∃ p : Path 1 u,
            PathCentralOn p F epsilon ∧
              ∀ a ∈ T, ‖pull phi u a - psi a‖ < eta := by
  letI : Nontrivial H := pi.nontrivial_of_isNonzero hpi.1
  have hinj : Function.Injective pi :=
    representation_injective_of_simple hsimple pi hpi
  have hker (theta : A →L[ℂ] ℂ) :
      ∀ a : A, pi a = 0 → theta a = 0 := by
    intro a ha
    have ha0 : a = 0 := hinj (by simpa using ha)
    simp [ha0]
  have hno : pi.HasNoNonzeroCompactImage :=
    hasNoNonzeroCompactImage_representation_of_simple_infinite
      hsimple hinfinite pi hpi
  obtain ⟨G, delta, hdelta, htransport⟩ :=
    pi.exists_protected_state_transport_of_row
      (Representation.isIrreducible_starAlgHom pi hpi) hno
      phi hphi hpure (hker phi) xi hxi hcoeff F hepsilon x hq hqxi hprotect
  refine ⟨G, delta, hdelta, ?_⟩
  intro psi hpsi hpurepsi hclose T eta heta
  exact htransport psi hpsi hpurepsi (hker psi) hclose T eta heta

end MathlibAnnex.CStarAlgebra
