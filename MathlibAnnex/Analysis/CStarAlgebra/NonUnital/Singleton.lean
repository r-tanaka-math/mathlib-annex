import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.Representation
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Faithful

/-!
# Singleton irreducible models of genuinely nonunital C-star algebras
-/

set_option autoImplicit false

open scoped ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w

variable {A : Type u} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace NonUnitalCStarRepresentation

/-- A displayed nonzero irreducible representation representing every
nonzero irreducible representation of a genuinely nonunital C-star algebra.
Faithfulness is deliberately not part of this predicate. -/
def IsSingletonIrreducibleModel
    (pi : NonUnitalCStarRepresentation A H) : Prop :=
  pi.IsIrreducible ∧
    ∀ (K : Type w) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K] (rho : NonUnitalCStarRepresentation A K),
      rho.IsIrreducible → pi.UnitaryEquivalent rho

/-- Pure-state separation in the minimal unitization proves faithfulness of a
singleton irreducible model without assuming that the original algebra has a
unit. -/
theorem injective_of_singleton [Nontrivial A]
    (pi : NonUnitalCStarRepresentation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi) :
    Function.Injective pi := by
  intro x y hxy
  let a : A := x - y
  have hpia : pi a = 0 := by
    simp only [a, map_sub, hxy, sub_self]
  have hazero : a = 0 := by
    by_contra hane
    let ainr : Unitization ℂ A := Unitization.inr a
    have hainr : ainr ≠ 0 := by
      intro hzero
      apply hane
      apply Unitization.inr_injective (R := ℂ)
      simpa [ainr] using hzero
    obtain ⟨phi, hphi, hpure, hdetect⟩ :=
      exists_pureState_nonzero_on_star_mul_self (A := Unitization ℂ A) hainr
    let f : Unitization ℂ A →ₚ[ℂ] ℂ :=
      positiveLinearMapOfMemStateSpace phi hphi
    let rhoU : Representation (Unitization ℂ A) f.GNS := f.gnsStarAlgHom
    let rho : NonUnitalCStarRepresentation A f.GNS :=
      rhoU.toNonUnitalStarAlgHom.comp
        (Unitization.inrNonUnitalStarAlgHom ℂ A)
    have hrhoa : rho a ≠ 0 := by
      intro hzero
      have hrhoUa : rhoU ainr = 0 := by
        simpa [rho, rhoU, ainr] using hzero
      apply hdetect
      calc
        phi (star ainr * ainr) = f (star ainr * ainr) := rfl
        _ = inner ℂ f.gnsCyclicVector
            (rhoU (star ainr * ainr) f.gnsCyclicVector) :=
          (PositiveLinearMap.inner_gnsCyclicVector_gnsStarAlgHom f _).symm
        _ = 0 := by rw [map_mul, map_star, hrhoUa]; simp
    have hxi : ‖f.gnsCyclicVector‖ = 1 :=
      PositiveLinearMap.norm_gnsCyclicVector f
        (positiveLinearMapOfMemStateSpace_one phi hphi)
    have hxi_ne : f.gnsCyclicVector ≠ 0 := by
      intro hzero
      simp [hzero] at hxi
    letI : Nontrivial f.GNS :=
      nontrivial_of_ne f.gnsCyclicVector 0 hxi_ne
    have hirrU : rhoU.IsIrreducible :=
      (Representation.isIrreducible_iff_starAlgHom rhoU).2
        (isIrreducible_pureState_gnsStarAlgHom phi hphi hpure)
    have hirr : rho.IsIrreducible :=
      isIrreducible_restriction_of_isIrreducible_unitization rhoU hirrU
        ⟨a, hrhoa⟩
    obtain ⟨U, hU⟩ := hsingle.2 f.GNS rho hirr
    have hrhozero : rho a = 0 := by
      apply ContinuousLinearMap.ext
      intro z
      obtain ⟨q, rfl⟩ := U.surjective z
      calc
        rho a (U q) = U (pi a q) := (hU a q).symm
        _ = 0 := by rw [hpia]; simp
    exact hrhoa hrhozero
  exact sub_eq_zero.mp hazero

end NonUnitalCStarRepresentation

end MathlibAnnex.Analysis.CStarAlgebra
