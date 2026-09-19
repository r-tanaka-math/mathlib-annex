import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Algebraic models of the compact operators

The fixed Mathlib version exposes compact operators as a predicate/submodule,
not as a bundled star algebra.  `IsCompactOperatorModel` is the exact range
characterization of an ordinary nonunital star-algebra isomorphism onto all
compact operators.
-/

set_option autoImplicit false

open scoped InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u}
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A nonunital star representation that is injective and has precisely the
compact operators as its range.  This is the unbundled form of a star
isomorphism with `K(H)`. -/
def IsCompactOperatorModel [NonUnitalCStarAlgebra A]
    (e : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  Function.Injective e ∧
    (∀ a : A, IsCompactOperator (e a)) ∧
    ∀ T : H →L[ℂ] H, IsCompactOperator T → ∃ a : A, e a = T

omit [CompleteSpace H] in
/-- Rank-one operators are compact, proved by factoring through the
one-dimensional scalar field. -/
theorem isCompactOperator_rankOne (x y : H) :
    IsCompactOperator (InnerProductSpace.rankOne ℂ x y) := by
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_dom
    (innerSL ℂ y)).clm_comp
      (ContinuousLinearMap.toSpanSingleton ℂ x)

theorem map_one_eq_one_of_isCompactOperatorModel [Nontrivial H]
    [CStarAlgebra A]
    (e : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (he : IsCompactOperatorModel e) : e 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change e 1 x = x
  obtain ⟨y, hy⟩ := exists_norm_ne_zero H
  let z : H := ‖y‖⁻¹ • y
  have hz : ‖z‖ = 1 := by
    dsimp [z]
    simp [norm_smul, inv_mul_cancel₀ hy]
  let T : H →L[ℂ] H := InnerProductSpace.rankOne ℂ x z
  obtain ⟨a, ha⟩ := he.2.2 T (isCompactOperator_rankOne x z)
  have hleft : e 1 * T = T := by
    rw [← ha, ← map_mul, one_mul]
  have hTz : T z = x := by
    simp [T, InnerProductSpace.rankOne_apply,
      inner_self_eq_norm_sq_to_K, hz]
  calc
    e 1 x = e 1 (T z) := congrArg (e 1) hTz.symm
    _ = (e 1 * T) z := rfl
    _ = T z := congrArg (fun S : H →L[ℂ] H => S z) hleft
    _ = x := hTz

/-- A nonzero unital infinite-dimensional C-star algebra cannot be
star-isomorphic to the compact operators on any Hilbert space, including the
zero Hilbert space. -/
theorem not_isCompactOperatorModel_of_infiniteDimensional
    [CStarAlgebra A] [Nontrivial A] (hA : ¬ FiniteDimensional ℂ A)
    (e : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : ¬ IsCompactOperatorModel e := by
  intro he
  have hH : ¬ Subsingleton H := by
    intro hsub
    letI : Subsingleton H := hsub
    have hmap : e (1 : A) = e 0 := Subsingleton.elim _ _
    exact one_ne_zero (he.1 hmap)
  letI : Nontrivial H := not_subsingleton_iff_nontrivial.mp hH
  have hone := map_one_eq_one_of_isCompactOperatorModel e he
  have hcompact_one : IsCompactOperator ((1 : H →L[ℂ] H) : H → H) := by
    rw [← hone]
    exact he.2.1 1
  haveI : FiniteDimensional ℂ H := by
    apply FiniteDimensional.of_isCompactOperator_id
    change IsCompactOperator (fun x : H => x)
    exact hcompact_one
  haveI : FiniteDimensional ℂ (H →L[ℂ] H) :=
    ContinuousLinearMap.finiteDimensional
  exact hA
    (FiniteDimensional.of_injective (LinearMapClass.linearMap e) he.1)

end MathlibAnnex.Analysis.CStarAlgebra
