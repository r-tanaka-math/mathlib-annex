import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The ideal pulled back from the compact operators

For a star representation on a Hilbert space, the elements represented by
compact operators form a norm-closed two-sided ideal.  Consequently an
injective representation of an infinite-dimensional simple unital C-star
algebra contains no nonzero compact operator.
-/

set_option autoImplicit false

open scoped CStarAlgebra

namespace MathlibAnnex.CStarAlgebra

universe u v

variable {A : Type u}
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The inverse image of the compact operators under a star representation,
as an algebraic two-sided ideal. -/
def compactPreimageIdeal [NonUnitalCStarAlgebra A]
    (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' {a | rho a ∈ compactOperator (RingHom.id ℂ) H H}
    (by
      change rho 0 ∈ compactOperator (RingHom.id ℂ) H H
      rw [map_zero]
      exact Submodule.zero_mem _)
    (fun {x y} hx hy => by
      change rho x ∈ compactOperator (RingHom.id ℂ) H H at hx
      change rho y ∈ compactOperator (RingHom.id ℂ) H H at hy
      change rho (x + y) ∈ compactOperator (RingHom.id ℂ) H H
      rw [map_add]
      exact Submodule.add_mem _ hx hy)
    (fun {x} hx => by
      change rho x ∈ compactOperator (RingHom.id ℂ) H H at hx
      change rho (-x) ∈ compactOperator (RingHom.id ℂ) H H
      rw [map_neg]
      exact Submodule.neg_mem _ hx)
    (fun {x y} hy => by
      change rho y ∈ compactOperator (RingHom.id ℂ) H H at hy
      change rho (x * y) ∈ compactOperator (RingHom.id ℂ) H H
      rw [map_mul]
      have hxy : (rho x).comp (rho y) ∈ compactOperator (RingHom.id ℂ) H H := by
        change IsCompactOperator ⇑((rho x).comp (rho y))
        exact hy.clm_comp (rho x)
      exact hxy)
    (fun {x y} hx => by
      change rho x ∈ compactOperator (RingHom.id ℂ) H H at hx
      change rho (x * y) ∈ compactOperator (RingHom.id ℂ) H H
      rw [map_mul]
      have hxy : (rho x).comp (rho y) ∈ compactOperator (RingHom.id ℂ) H H := by
        change IsCompactOperator ⇑((rho x).comp (rho y))
        exact hx.comp_clm (rho y)
      exact hxy)

@[simp] theorem mem_compactPreimageIdeal [NonUnitalCStarAlgebra A]
    (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    a ∈ compactPreimageIdeal rho ↔ IsCompactOperator (rho a) := by
  unfold compactPreimageIdeal
  rw [TwoSidedIdeal.mem_mk']
  rfl

/-- The compact-operator preimage is norm closed. -/
theorem isClosed_compactPreimageIdeal [NonUnitalCStarAlgebra A]
    (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    IsClosed (compactPreimageIdeal rho : Set A) := by
  let rhoL : A →L[ℂ] (H →L[ℂ] H) :=
    (LinearMapClass.linearMap rho).mkContinuous 1 fun a => by
      change ‖rho a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le rho a
  have hcarrier : (compactPreimageIdeal rho : Set A) =
      rhoL ⁻¹' (compactOperator (RingHom.id ℂ) H H : Set (H →L[ℂ] H)) := by
    ext a
    rw [Set.mem_preimage, SetLike.mem_coe, mem_compactPreimageIdeal]
    change IsCompactOperator ⇑(rho a) ↔ IsCompactOperator ⇑(rhoL a)
    rfl
  have hclosed : IsClosed
      (compactOperator (RingHom.id ℂ) H H : Set (H →L[ℂ] H)) := by
    change IsClosed {T : H →L[ℂ] H | IsCompactOperator T}
    exact isClosed_setOf_isCompactOperator
  rw [hcarrier]
  exact hclosed.preimage rhoL.continuous

/-- In an injective representation of an infinite-dimensional algebra with
no nontrivial closed two-sided ideals, every compact image is zero.  The
finite-dimensional target contradiction is proved here rather than hidden in
a `no-compacts` premise. -/
theorem eq_zero_of_isCompactOperator_of_injective
    [CStarAlgebra A] [Nontrivial A] (hA : ¬ FiniteDimensional ℂ A)
    (hsimple : ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤)
    (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hrho : Function.Injective rho)
    {a : A} (ha : IsCompactOperator (rho a)) : a = 0 := by
  let rhoNU := rho.toNonUnitalStarAlgHom
  let I := compactPreimageIdeal rhoNU
  have haI : a ∈ I := (mem_compactPreimageIdeal rhoNU a).2 ha
  rcases hsimple I (isClosed_compactPreimageIdeal rhoNU) with hI | hI
  · rw [hI] at haI
    simpa using haI
  · have hH : ¬ Subsingleton H := by
      intro hsub
      letI : Subsingleton H := hsub
      have : (1 : A) = 0 := hrho (Subsingleton.elim _ _)
      exact one_ne_zero this
    letI : Nontrivial H := not_subsingleton_iff_nontrivial.mp hH
    have honeI : (1 : A) ∈ I := by rw [hI]; exact Set.mem_univ 1
    have hcompactOne : IsCompactOperator ((1 : H →L[ℂ] H) : H → H) := by
      have : IsCompactOperator (rho (1 : A)) :=
        (mem_compactPreimageIdeal rhoNU 1).1 honeI
      simpa only [map_one, one_apply_eq_self] using this
    letI : FiniteDimensional ℂ H := by
      apply FiniteDimensional.of_isCompactOperator_id
      change IsCompactOperator (fun x : H => x)
      exact hcompactOne
    letI : FiniteDimensional ℂ (H →L[ℂ] H) :=
      ContinuousLinearMap.finiteDimensional
    exact (hA (FiniteDimensional.of_injective
      (LinearMapClass.linearMap rho) hrho)).elim

end MathlibAnnex.CStarAlgebra
