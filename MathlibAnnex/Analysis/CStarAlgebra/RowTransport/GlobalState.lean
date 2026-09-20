import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.GlobalPath
import MathlibAnnex.Analysis.CStarAlgebra.State.VectorApproximation
import MathlibAnnex.Analysis.CStarAlgebra.LocalPathTransport
import MathlibAnnex.Analysis.CStarAlgebra.Representation.VectorFunctional

set_option autoImplicit false
noncomputable section
open scoped CStarAlgebra ComplexOrder ComplexStarModule InnerProduct
namespace MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.CStarAlgebra
variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

theorem Representation.exists_path_state_approx_of_essential
    (pi : Representation A H) (hpi : StarAlgHom.IsIrreducible pi)
    (hno : pi.HasNoNonzeroCompactImage)
    (phi : A →L[ℂ] ℂ) (xi : H) (hxi : ‖xi‖ = 1)
    (hcoeff : ∀ a : A, phi a = inner ℂ xi (pi a xi))
    (psi : A →L[ℂ] ℂ) (hpsi : psi ∈ stateSpace A)
    (hpure : IsPureState A psi)
    (hker : ∀ a : A, pi a = 0 → psi a = 0)
    (F : Finset A) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ u : unitary A, ∃ p : Path 1 u,
      ∀ a ∈ F, ‖pull phi u a - psi a‖ < epsilon := by
  letI : FiniteDimensional ℂ (⊥ : Submodule ℂ H) := inferInstance
  obtain ⟨v, hv, _hvorth, happ⟩ :=
    pi.exists_unit_mem_orthogonal_approx hno psi hpsi hpure hker
      (⊥ : Submodule ℂ H) F hepsilon
  obtain ⟨zeta, hzeta, hsame, hnear⟩ := phase_align_lt_two xi v hxi hv
  obtain ⟨u, p, hu⟩ :=
    StarAlgHom.exists_unitary_path_apply_eq_of_norm_sub_lt_two pi hpi
      xi zeta hxi hzeta hnear
  refine ⟨u, p, ?_⟩
  intro a ha
  have hphiVec : phi = Representation.vectorFunctional pi xi := by
    ext b
    exact hcoeff b
  have hpull : pull phi u a = inner ℂ zeta (pi a zeta) := by
    rw [hphiVec]
    calc
      pull (Representation.vectorFunctional pi xi) u a =
          Representation.vectorFunctional pi xi
            (star (u : A) * a * (u : A)) := by simp [pull_apply, innerAt]
      _ = Representation.vectorFunctional pi (pi (u : A) xi) a :=
          (Representation.vectorFunctional_map_apply pi xi (u : A) a).symm
      _ = inner ℂ zeta (pi a zeta) := by rw [hu]; rfl
  rw [hpull, hsame (pi a), norm_sub_rev]
  exact happ a ha
end MathlibAnnex.Analysis.CStarAlgebra
