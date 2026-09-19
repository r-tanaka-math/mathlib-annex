import MathlibAnnex.Analysis.CStarAlgebra.Representation.Singleton
import MathlibAnnex.Analysis.CStarAlgebra.State.Extension

/-!
# Characters realized as joint eigenvectors

A character of a closed unital star subalgebra extends to a pure state.  Its
irreducible GNS representation is therefore equivalent to a singleton model,
and the transported cyclic vector realizes the original character.
-/

set_option autoImplicit false

open Set
open scoped ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Representation

/-- Every character of a closed unital star subalgebra occurs as a joint
unit eigenvector in a singleton irreducible model. -/
theorem exists_unit_eigenvector_of_character [Nontrivial A]
    (pi : Representation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (chi : WeakDual.characterSpace ℂ D) :
    ∃ eta : H, ‖eta‖ = 1 ∧
      ∀ d : D, pi (d : A) eta = chi d • eta := by
  obtain ⟨phi, hphi, hpure, hext⟩ := exists_pureState_extension D chi
  let f : A →ₚ[ℂ] ℂ := positiveLinearMapOfMemStateSpace phi hphi
  let xi : f.GNS := f.gnsCyclicVector
  have hxi : ‖xi‖ = 1 :=
    PositiveLinearMap.norm_gnsCyclicVector f
      (positiveLinearMapOfMemStateSpace_one phi hphi)
  have hxi_ne : xi ≠ 0 := by
    intro hzero
    simp [hzero] at hxi
  letI : Nontrivial f.GNS := nontrivial_of_ne xi 0 hxi_ne
  have hirr : Representation.IsIrreducible f.gnsStarAlgHom :=
    (Representation.isIrreducible_iff_starAlgHom f.gnsStarAlgHom).2
      (pureState_gnsStarAlgHom_isIrreducible phi hphi hpure)
  obtain ⟨U, hU⟩ := hsingle.2 f.GNS f.gnsStarAlgHom hirr
  have heigen (d : D) :
      f.gnsStarAlgHom (d : A) xi = chi d • xi := by
    let q : D := d - algebraMap ℂ D (chi d)
    have hchiq : chi q = 0 := by
      dsimp [q]
      rw [map_sub, AlgHomClass.commutes]
      simp
    have hchiqq : chi (star q * q) = 0 := by
      rw [map_mul, map_star, hchiq]
      simp
    have hphiqq : phi (star (q : A) * (q : A)) = 0 := by
      have hvalue := hext (star q * q)
      change phi (star (q : A) * (q : A)) = chi (star q * q) at hvalue
      exact hvalue.trans hchiqq
    have hinner :
        inner ℂ (f.gnsStarAlgHom (q : A) xi)
          (f.gnsStarAlgHom (q : A) xi) = 0 := by
      calc
        inner ℂ (f.gnsStarAlgHom (q : A) xi)
            (f.gnsStarAlgHom (q : A) xi) =
            Representation.vectorFunctional f.gnsStarAlgHom xi
              (star (q : A) * (q : A)) := by
          simpa using
            (Representation.vectorFunctional_star_mul
              f.gnsStarAlgHom xi (q : A) (q : A)).symm
        _ = f (star (q : A) * (q : A)) :=
          PositiveLinearMap.inner_gnsCyclicVector_gnsStarAlgHom f _
        _ = phi (star (q : A) * (q : A)) := rfl
        _ = 0 := hphiqq
    have hqzero : f.gnsStarAlgHom (q : A) xi = 0 :=
      inner_self_eq_zero.mp hinner
    have hsub : f.gnsStarAlgHom (d : A) xi - chi d • xi = 0 := by
      calc
        f.gnsStarAlgHom (d : A) xi - chi d • xi =
            f.gnsStarAlgHom (q : A) xi := by
          simp [q, Algebra.algebraMap_eq_smul_one]
        _ = 0 := hqzero
    exact sub_eq_zero.mp hsub
  refine ⟨U.symm xi, (U.symm.norm_map xi).trans hxi, ?_⟩
  intro d
  apply U.injective
  calc
    U (pi (d : A) (U.symm xi)) =
        f.gnsStarAlgHom (d : A) xi := by simpa using hU (d : A) (U.symm xi)
    _ = chi d • xi := heigen d
    _ = U (chi d • U.symm xi) := by simp

end Representation

end MathlibAnnex.Analysis.CStarAlgebra
