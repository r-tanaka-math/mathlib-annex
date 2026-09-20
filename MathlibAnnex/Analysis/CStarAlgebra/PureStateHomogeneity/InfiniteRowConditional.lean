import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.PureInfiniteApprox
import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.SimpleProtected
import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.PureFamily

/-! Explicit missing row interface in the infinite-dimensional simple case.
This file only consumes a row supplier; it does not assert one exists. -/

set_option autoImplicit false
noncomputable section
namespace MathlibAnnex.CStarAlgebra
open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.CStarAlgebra
open MathlibAnnex.CStarAlgebra.TensorAveraging

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The exact GNS row supplier still missing from the general proof. -/
def PureGNSProtectedRowSupplier (A : Type*) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] : Prop :=
  ∀ (phi : A →L[ℂ] ℂ) (hpure : IsPureState A phi)
    (F : Finset A) (epsilon : ℝ), 0 < epsilon →
    let f := positiveLinearMapOfMemStateSpace phi hpure.1
    let xi := stateGNSVector phi hpure.1
    ∃ (n : ℕ) (x : Fin n → A),
      ‖rowSquare A x‖ ≤ 1 ∧
      f.gnsStarAlgHom (rowSquare A x) xi = xi ∧
      ∀ a ∈ F, ∀ h : A,
        ‖a * rowMap A x h - rowMap A x h * a‖ ≤
          ((epsilon / 2) / (8 * Real.pi)) * ‖h‖

theorem pure_gns_protected_of_rowSupplier
    (hsimple : IsSimpleCStarAlgebra A)
    (hinfinite : ¬ FiniteDimensional ℂ A)
    (hrow : PureGNSProtectedRowSupplier A)
    (phi : A →L[ℂ] ℂ) (hpure : IsPureState A phi)
    (F : Finset A) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ G : Finset A, ∃ delta : ℝ, 0 < delta ∧
      ∀ psi : A →L[ℂ] ℂ, IsPureState A psi →
        (∀ a ∈ G, ‖phi a - psi a‖ < delta) →
        ∀ T : Finset A, ∀ eta : ℝ, 0 < eta →
          ∃ u : unitary A, ∃ p : Path 1 u,
            PathCentralOn p F epsilon ∧
              ∀ a ∈ T, ‖pull phi u a - psi a‖ < eta := by
  let hstate : phi ∈ stateSpace A := hpure.1
  let f := positiveLinearMapOfMemStateSpace phi hstate
  let pi : Representation A f.GNS := f.gnsStarAlgHom
  let xi : f.GNS := stateGNSVector phi hstate
  have hxi : ‖xi‖ = 1 := norm_stateGNSVector phi hstate
  have hxi0 : xi ≠ 0 := by
    intro hzero
    simp [hzero] at hxi
  letI : Nontrivial f.GNS := nontrivial_of_ne xi 0 hxi0
  have hirr : pi.IsIrreducible :=
    (Representation.isIrreducible_iff_starAlgHom pi).mpr
      (isIrreducible_pureState_gnsStarAlgHom phi hstate hpure)
  have hcoeff : ∀ a : A, phi a = inner ℂ xi (pi a xi) := by
    intro a
    exact (inner_gnsStarAlgHom_stateGNSVector phi hstate a).symm
  obtain ⟨n, x, hq, hqxi, hprotect⟩ := hrow phi hpure F epsilon hepsilon
  obtain ⟨G, delta, hdelta, hmain⟩ :=
    CStarAlgebra.exists_protected_state_transport_of_simple_row
      hsimple hinfinite pi hirr phi hstate hpure xi hxi hcoeff
      F hepsilon x hq hqxi hprotect
  refine ⟨G, delta, hdelta, ?_⟩
  intro psi hpurepsi hclose T eta heta
  exact hmain psi hpurepsi.1 hpurepsi hclose T eta heta

theorem finitePathTransport_pure_infinite_of_rowSupplier
    (hsimple : IsSimpleCStarAlgebra A)
    (hinfinite : ¬ FiniteDimensional ℂ A)
    (hrow : PureGNSProtectedRowSupplier A) :
    FinitePathTransport (IsPureState A) where
  toInnerInvariantFamily := innerInvariantFamily_pure
  approximate := by
    intro phi hphi psi hpsi F epsilon hepsilon
    exact pure_gns_path_approx_of_simple_infinite hsimple hinfinite
      phi psi hphi hpsi F hepsilon
  protected_approximate := by
    intro phi hphi F epsilon hepsilon
    obtain ⟨G, delta, hdelta, hmain⟩ :=
      pure_gns_protected_of_rowSupplier
        hsimple hinfinite hrow phi hphi F hepsilon
    exact ⟨G, delta, hdelta, fun psi hpsi hclose T eta heta =>
      hmain psi hpsi hclose T eta heta⟩
end MathlibAnnex.CStarAlgebra
