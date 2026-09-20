import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.PureFamily
import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.PureCompact

/-! All four pure-state finite path fields in the finite-dimensional simple case. -/

set_option autoImplicit false
noncomputable section
namespace MathlibAnnex.CStarAlgebra
open MathlibAnnex.CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem finitePathTransport_pure_of_simple_finite
    (hsimple : IsSimpleCStarAlgebra A) [FiniteDimensional ℂ A] :
    FinitePathTransport (IsPureState A) where
  toInnerInvariantFamily := innerInvariantFamily_pure
  approximate := by
    intro phi hphi psi hpsi F epsilon hepsilon
    obtain ⟨u, p, heq⟩ :=
      pure_gns_path_pull_eq_of_simple_finite hsimple phi psi hphi hpsi
    refine ⟨u, p, ?_⟩
    intro a _
    rw [heq, sub_self, norm_zero]
    exact hepsilon
  protected_approximate := by
    intro phi hphi F epsilon hepsilon
    obtain ⟨G, delta, hdelta, hmain⟩ :=
      pure_gns_protected_transport_of_simple_finite
        hsimple phi hphi F hepsilon
    refine ⟨G, delta, hdelta, ?_⟩
    intro psi hpsi hclose H eta heta
    exact hmain psi hpsi.1 hpsi hclose H eta heta
end MathlibAnnex.CStarAlgebra
