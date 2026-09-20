import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.CompactPath
import MathlibAnnex.Analysis.InnerProductSpace.TwoVectorUnitary
import MathlibAnnex.Analysis.CStarAlgebra.Representation.FullImage

set_option autoImplicit false
noncomputable section
open scoped ComplexOrder ComplexStarModule InnerProduct
namespace MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.CStarAlgebra
variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [FiniteDimensional ℂ H]

theorem Representation.exists_path_pull_eq_of_full_finite
    (pi : Representation A H) (hinj : Function.Injective pi)
    (hsurj : Function.Surjective pi)
    (phi psi : A →L[ℂ] ℂ) (hpsi : psi ∈ stateSpace A)
    (hpure : IsPureState A psi)
    (xi : H) (hxi : ‖xi‖ = 1)
    (hcoeff : ∀ a : A, phi a = inner ℂ xi (pi a xi)) :
    ∃ u : unitary A, ∃ p : Path 1 u, pull phi u = psi := by
  obtain ⟨eta, heta, hetaCoeff⟩ :=
    representation_exists_exact_unit_vector_of_full_finite pi hinj hsurj
      psi hpsi hpure
  obtain ⟨zeta, hzeta, hzetaCoeff, hnear⟩ :=
    phase_align_lt_two xi eta hxi heta
  obtain ⟨U, hU, hUnorm⟩ :=
    MathlibAnnex.Analysis.InnerProductSpace.exists_unitary_apply_eq_and_norm_sub_one_eq
      xi zeta hxi hzeta
  let e : A ≃⋆ₐ[ℂ] (H →L[ℂ] H) :=
    StarAlgEquiv.ofBijective pi ⟨hinj, hsurj⟩
  let gammaStar : (H →L[ℂ] H) →⋆* A :=
    { e.symm.toMonoidHom with map_star' := fun T => map_star e.symm T }
  let u : unitary A := Unitary.map gammaStar U
  have hmap : pi (u : A) = (U : H →L[ℂ] H) := by
    change e (e.symm (U : H →L[ℂ] H)) = _
    exact e.apply_symm_apply _
  have hunorm : ‖(u : A) - 1‖ < 2 := by
    have heq : ‖(u : A) - 1‖ = ‖(U : H →L[ℂ] H) - 1‖ := by
      change ‖e.symm (U : H →L[ℂ] H) - 1‖ = _
      rw [← map_one e.symm, ← map_sub, StarAlgEquiv.norm_map]
    rw [heq, hUnorm]
    exact hnear
  let p : Path 1 u := Unitary.path 1 u (by simpa using hunorm)
  refine ⟨u, p, ?_⟩
  ext a
  have hphiVec : phi = Representation.vectorFunctional pi xi := by
    ext b
    exact hcoeff b
  rw [hphiVec]
  calc
    pull (Representation.vectorFunctional pi xi) u a =
        Representation.vectorFunctional pi xi
          (star (u : A) * a * (u : A)) := by simp [pull_apply, innerAt]
    _ = Representation.vectorFunctional pi (pi (u : A) xi) a :=
        (Representation.vectorFunctional_map_apply pi xi (u : A) a).symm
    _ = inner ℂ zeta (pi a zeta) := by rw [hmap, hU]; rfl
    _ = inner ℂ eta (pi a eta) := hzetaCoeff (pi a)
    _ = psi a := (hetaCoeff a).symm
end MathlibAnnex.Analysis.CStarAlgebra
