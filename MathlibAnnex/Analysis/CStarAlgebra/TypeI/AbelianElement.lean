/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.Basic
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.ComplexExactInterpolation
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.Image
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.SurjectiveRepresentation
import MathlibAnnex.Analysis.InnerProductSpace.CompactOperatorIdeal

/-!
# Abelian positive elements in irreducible representations

Commutativity of the genuine closed sandwich algebra forces the image of its
positive generator in every irreducible representation to have rank at most
one. The proof uses exact interpolation on two vectors twice, then evaluates
a commutator of rank-one operators. No separability, unit, faithful action,
classification theorem, or assumed finite-rank conclusion is used.

The nonzero conclusion is an explicit scalar multiple of an actual rank-one
operator. Compactness is then an application of the existing compactness
theorem for rank-one operators.
-/

set_option autoImplicit false
noncomputable section

open Set InnerProductSpace
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Interpolation

variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable (hclosed : IsClosed (S : Set (H →L[ℂ] H)))
variable (hS : letI : NonUnitalCStarAlgebra S :=
    NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S (h_closed := hclosed)
  NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))

include hclosed hS

/-- Exact interpolation at two arbitrary vectors, including dependent or zero
vectors, by an element of the original closed irreducible algebra. -/
theorem exists_eq_on_pair_of_isIrreducible (T : H →L[ℂ] H) (x y : H) :
    ∃ s : S, s.val x = T x ∧ s.val y = T y := by
  classical
  let K : Submodule ℂ H := Submodule.span ℂ (↑({x, y} : Finset H) : Set H)
  letI : FiniteDimensional ℂ K := by
    change FiniteDimensional ℂ (Submodule.span ℂ (↑({x, y} : Finset H) : Set H))
    infer_instance
  letI : CompleteSpace K := FiniteDimensional.complete ℂ K
  let F : H →L[ℂ] H := K.starProjection
  have hFK : LinearMap.range F.toLinearMap ≤ K := by
    rintro z ⟨w, rfl⟩
    exact (K.orthogonalProjectionOnto w).property
  letI : FiniteDimensional ℂ (LinearMap.range F.toLinearMap) :=
    Submodule.finiteDimensional_of_le hFK
  obtain ⟨s, _hsnorm, hs⟩ := exists_norm_le_two_mul_eq_on_range S hclosed hS F T
  have hxK : x ∈ K := Submodule.subset_span (by simp)
  have hyK : y ∈ K := Submodule.subset_span (by simp)
  have hxF : x ∈ LinearMap.range F.toLinearMap := by
    refine ⟨x, ?_⟩
    exact (Submodule.starProjection_eq_self_iff (K := K)).2 hxK
  have hyF : y ∈ LinearMap.range F.toLinearMap := by
    refine ⟨y, ?_⟩
    exact (Submodule.starProjection_eq_self_iff (K := K)).2 hyK
  exact ⟨s, hs x hxF, hs y hyF⟩

/-- Commuting sandwiches with middle coefficients in an irreducible algebra
force commuting sandwiches with arbitrary bounded-operator coefficients. -/
theorem sandwiches_commute_of_commute_on_irreducible (a : H →L[ℂ] H)
    (hcomm : ∀ s ∈ S, ∀ t ∈ S,
      (a * s * a) * (a * t * a) = (a * t * a) * (a * s * a))
    (T U : H →L[ℂ] H) :
    (a * T * a) * (a * U * a) = (a * U * a) * (a * T * a) := by
  ext z
  obtain ⟨s, hs₁, hs₂⟩ := exists_eq_on_pair_of_isIrreducible S hclosed hS T
    (a z) (a (a (U (a z))))
  obtain ⟨t, ht₁, ht₂⟩ := exists_eq_on_pair_of_isIrreducible S hclosed hS U
    (a z) (a (a (T (a z))))
  have h := congrArg (fun R : H →L[ℂ] H => R z)
    (hcomm s.val s.property t.val t.property)
  change a (s.val (a (a (t.val (a z))))) = a (t.val (a (a (s.val (a z))))) at h
  rw [ht₁, hs₁, hs₂, ht₂] at h
  exact h

end Interpolation

/-- If every operator sandwich by a self-adjoint operator commutes, then a
nonzero value gives an explicit rank-one formula for the operator. -/
theorem eq_smul_rankOne_of_sandwiches_commute {a : H →L[ℂ] H}
    (ha : IsSelfAdjoint a)
    (hcomm : ∀ T U : H →L[ℂ] H,
      (a * T * a) * (a * U * a) = (a * U * a) * (a * T * a))
    {x : H} (hx : a x ≠ 0) :
    a = (inner ℂ (a x) (a x))⁻¹ • rankOne ℂ (a x) (a (a x)) := by
  have hsandwich (y z : H) :
      a * rankOne ℂ y z * a = rankOne ℂ (a y) (a z) := by
    change (a.comp (rankOne ℂ y z)).comp a = rankOne ℂ (a y) (a z)
    rw [comp_rankOne, rankOne_comp, ha.adjoint_eq]
  let v : H := a x
  let c : ℂ := inner ℂ v v
  have hc : c ≠ 0 := by
    simpa only [c, v, ne_eq, inner_self_eq_zero] using hx
  ext y
  let w : H := a y
  let d : ℂ := inner ℂ v w
  have h := hcomm (rankOne ℂ x x) (rankOne ℂ y x)
  simp only [hsandwich] at h
  have heval := congrArg (fun R : H →L[ℂ] H => R v) h
  change rankOne ℂ v v (rankOne ℂ w v v) =
    rankOne ℂ w v (rankOne ℂ v v v) at heval
  simp only [rankOne_apply, inner_smul_right, smul_smul] at heval
  change (c * d) • v = (c * c) • w at heval
  have hcancel := congrArg (fun z : H => c⁻¹ • z) heval
  have hlinear : d • v = c • w := by
    simpa only [smul_smul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul] using hcancel
  have hcancel' := congrArg (fun z : H => c⁻¹ • z) hlinear
  have hw : w = c⁻¹ • (d • v) := by
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hcancel'.symm
  have hinner : inner ℂ (a v) y = d := by
    simpa only [ha.adjoint_eq] using a.adjoint_inner_left y v
  change w = c⁻¹ • (inner ℂ (a v) y • v)
  rw [hinner]
  exact hw

/-- Compactness follows from the proved rank-one formula, with the zero
operator branch retained. -/
theorem isCompactOperator_of_sandwiches_commute {a : H →L[ℂ] H}
    (ha : IsSelfAdjoint a)
    (hcomm : ∀ T U : H →L[ℂ] H,
      (a * T * a) * (a * U * a) = (a * U * a) * (a * T * a)) :
    IsCompactOperator a := by
  classical
  by_cases ha0 : a = 0
  · rw [ha0]
    exact isCompactOperator_zero
  · obtain ⟨x, hx⟩ : ∃ x : H, a x ≠ 0 := by
      by_contra hn
      apply ha0
      ext x
      by_contra hx
      exact hn ⟨x, hx⟩
    rw [eq_smul_rankOne_of_sandwiches_commute ha hcomm hx]
    exact (isCompactOperator_rankOne (a x) (a (a x))).smul _

section Representation

variable {A : Type u} [NonUnitalCStarAlgebra A]
attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- An abelian positive element gives commuting sandwiches by every bounded
operator after passage to any irreducible representation. -/
theorem IsAbelianPositiveElement.sandwiches_commute {a : A}
    (ha : IsAbelianPositiveElement a) (pi : NonUnitalCStarRepresentation A H)
    (hpi : pi.IsIrreducible) (T U : H →L[ℂ] H) :
    (pi a * T * pi a) * (pi a * U * pi a) =
      (pi a * U * pi a) * (pi a * T * pi a) := by
  let S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H) := NonUnitalStarAlgHom.range pi
  have hclosed : IsClosed (S : Set (H →L[ℂ] H)) := HomKernelQuotient.isClosed_image pi
  have hS : letI : NonUnitalCStarAlgebra S :=
      NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S (h_closed := hclosed)
    NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S) := by
    letI : NonUnitalCStarAlgebra S :=
      NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S (h_closed := hclosed)
    let q : A →⋆ₙₐ[ℂ] S := NonUnitalStarAlgHom.rangeRestrict pi
    have hq : Function.Surjective q := by
      intro s
      obtain ⟨b, hb⟩ := (NonUnitalStarAlgHom.mem_range pi).1 s.property
      exact ⟨b, Subtype.ext hb⟩
    have hcomp : (NonUnitalStarSubalgebraClass.subtype S).comp q = pi := by
      ext b
      rfl
    apply (NonUnitalCStarRepresentation.isIrreducible_comp_iff_of_surjective
      (NonUnitalStarSubalgebraClass.subtype S) q hq).1
    rwa [hcomp]
  apply sandwiches_commute_of_commute_on_irreducible S hclosed hS (pi a) ?_ T U
  intro s hs t ht
  obtain ⟨b, rfl⟩ := (NonUnitalStarAlgHom.mem_range pi).1 hs
  obtain ⟨c, rfl⟩ := (NonUnitalStarAlgHom.mem_range pi).1 ht
  have hb : a * b * a ∈ hereditarySubalgebra a := by
    simpa only [ha.nonneg.star_eq] using sandwich_mem_hereditarySubalgebra a b
  have hc : a * c * a ∈ hereditarySubalgebra a := by
    simpa only [ha.nonneg.star_eq] using sandwich_mem_hereditarySubalgebra a c
  simpa only [map_mul] using congrArg pi (ha.mul_comm hb hc)

/-- In the nonzero branch, the image is a displayed scalar multiple of a
rank-one operator on the original Hilbert space. -/
theorem IsAbelianPositiveElement.exists_eq_smul_rankOne {a : A}
    (ha : IsAbelianPositiveElement a) (pi : NonUnitalCStarRepresentation A H)
    (hpi : pi.IsIrreducible) (hne : pi a ≠ 0) :
    ∃ x : H, pi a x ≠ 0 ∧
      pi a = (inner ℂ (pi a x) (pi a x))⁻¹ • rankOne ℂ (pi a x) (pi a (pi a x)) := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : H, pi a x ≠ 0 := by
    by_contra hn
    apply hne
    ext x
    by_contra hx
    exact hn ⟨x, hx⟩
  exact ⟨x, hx, eq_smul_rankOne_of_sandwiches_commute
    (ha.nonneg.isSelfAdjoint.map pi) (ha.sandwiches_commute pi hpi) hx⟩

/-- An abelian positive element has compact image in every irreducible
representation, without a faithful-action or separability hypothesis. -/
theorem IsAbelianPositiveElement.isCompactOperator {a : A}
    (ha : IsAbelianPositiveElement a) (pi : NonUnitalCStarRepresentation A H)
    (hpi : pi.IsIrreducible) : IsCompactOperator (pi a) :=
  isCompactOperator_of_sandwiches_commute
    (ha.nonneg.isSelfAdjoint.map pi) (ha.sandwiches_commute pi hpi)

end Representation

end MathlibAnnex.Analysis.CStarAlgebra
