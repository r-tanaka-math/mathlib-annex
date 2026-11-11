/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.Basic
import MathlibAnnex.Analysis.CStarAlgebra.Hereditary.Representation

/-!
# Abelian positive elements and internal type I under quotient maps

Surjective maps transport the entire hereditary algebra, including arbitrary
middle coefficients. An injective map into a larger ambient algebra is not
claimed to preserve abelian positive elements.

The internal predicate is proved invariant under actual C-star isomorphisms
and preserved by surjective homomorphisms, using the universal property of
the genuine closed-ideal quotient. No representation-side GCR result is used.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} {B : Type v}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- Positivity and abelianness pass through a surjective homomorphism. -/
theorem IsAbelianPositiveElement.map_of_surjective {a : A}
    (ha : IsAbelianPositiveElement a) (q : A →⋆ₙₐ[ℂ] B)
    (hq : Function.Surjective q) : IsAbelianPositiveElement (q a) := by
  refine ⟨?_, ?_⟩
  · simpa only [map_zero] using (OrderHomClass.mono q ha.nonneg)
  · intro x hx y hy
    obtain ⟨b, hb, rfl⟩ := (mem_hereditarySubalgebra_image_iff q hq a x).1 hx
    obtain ⟨c, hc, rfl⟩ := (mem_hereditarySubalgebra_image_iff q hq a y).1 hy
    simpa only [map_mul] using congrArg q (ha.mul_comm hb hc)

theorem isAbelianPositiveElement_iff_of_starAlgEquiv
    (e : A ≃⋆ₐ[ℂ] B) (a : A) :
    IsAbelianPositiveElement a ↔ IsAbelianPositiveElement (e a) := by
  constructor
  · intro ha
    exact ha.map_of_surjective e.toNonUnitalStarAlgHom e.surjective
  · intro ha
    have h : IsAbelianPositiveElement (e.symm (e a)) :=
      ha.map_of_surjective e.symm.toNonUnitalStarAlgHom e.symm.surjective
    rwa [e.symm_apply_apply] at h

/-- The definition on the fixed quotient model implies the same witness in
any nonzero C-star quotient presentation, in any codomain universe. -/
theorem IsInternalTypeI.exists_of_surjective (hA : IsInternalTypeI A)
    [Nontrivial B] (q : A →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q) :
    ∃ b : B, b ≠ 0 ∧ IsAbelianPositiveElement b := by
  let J : TwoSidedIdeal A := TwoSidedIdeal.ker q
  have hJ : IsClosed (J : Set A) := by
    have hset : (J : Set A) = {a : A | q a = 0} := by
      ext a
      exact TwoSidedIdeal.mem_ker q
    rw [hset]
    exact isClosed_eq (map_continuous q) continuous_const
  have hproper : J ≠ ⊤ := by
    intro htop
    obtain ⟨b, hb⟩ := exists_ne (0 : B)
    obtain ⟨a, rfl⟩ := hq b
    apply hb
    have ha : a ∈ J := by rw [htop]; trivial
    exact (TwoSidedIdeal.mem_ker q).1 ha
  obtain ⟨a, ha, hab⟩ := hA J hJ hproper
  let e := ClosedIdealQuotient.equivOfSurjective J hJ q hq
    (fun _ => (TwoSidedIdeal.mem_ker q).symm)
  refine ⟨e a, ?_, hab.map_of_surjective e.toNonUnitalStarAlgHom e.surjective⟩
  intro hz
  apply ha
  exact e.injective (hz.trans (map_zero e).symm)

/-- In particular the original nonzero algebra contains an abelian positive
element; it is not obtained by choosing an arbitrary positive lift from a quotient. -/
theorem IsInternalTypeI.exists_nonzero_abelian_positive_element
    (hA : IsInternalTypeI A) [Nontrivial A] :
    ∃ a : A, a ≠ 0 ∧ IsAbelianPositiveElement a :=
  hA.exists_of_surjective (NonUnitalStarAlgHom.id ℂ A) Function.surjective_id

/-- Quotient permanence of the internal predicate, independently of GCR. -/
theorem IsInternalTypeI.of_surjective (hA : IsInternalTypeI A)
    (q : A →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q) : IsInternalTypeI B := by
  intro J hJ hproper
  letI : Nontrivial (ClosedIdealQuotient.Quotient J hJ) :=
    ClosedIdealQuotient.nontrivial_quotient J hJ hproper
  exact hA.exists_of_surjective ((ClosedIdealQuotient.mkHom J hJ).comp q)
    ((ClosedIdealQuotient.mkHom_surjective J hJ).comp hq)

theorem isInternalTypeI_iff_of_starAlgEquiv (e : A ≃⋆ₐ[ℂ] B) :
    IsInternalTypeI A ↔ IsInternalTypeI B :=
  ⟨fun h => h.of_surjective e.toNonUnitalStarAlgHom e.surjective,
    fun h => h.of_surjective e.symm.toNonUnitalStarAlgHom e.symm.surjective⟩

/-- A nonzero commutative C-star algebra has an explicit nonzero positive
witness `x⋆x`; its hereditary algebra is commutative in the original ambient algebra. -/
theorem exists_nonzero_abelian_positive_element_of_commutative [Nontrivial A]
    (hcomm : ∀ x y : A, x * y = y * x) :
    ∃ a : A, a ≠ 0 ∧ IsAbelianPositiveElement a := by
  obtain ⟨x, hx⟩ := exists_ne (0 : A)
  refine ⟨star x * x, ?_,
    isAbelianPositiveElement_of_nonneg_of_commutative hcomm (star_mul_self_nonneg x)⟩
  exact fun hz => hx (star_mul_self_eq_zero.mp hz)

/-- Every commutative C-star algebra is internally type I, with nonunital and
zero algebras included. The quotient witness is constructed inside each quotient. -/
theorem isInternalTypeI_of_commutative (hcomm : ∀ x y : A, x * y = y * x) :
    IsInternalTypeI A := by
  intro J hJ hproper
  letI : Nontrivial (ClosedIdealQuotient.Quotient J hJ) :=
    ClosedIdealQuotient.nontrivial_quotient J hJ hproper
  apply exists_nonzero_abelian_positive_element_of_commutative
  intro x y
  obtain ⟨a, rfl⟩ := ClosedIdealQuotient.mkHom_surjective J hJ x
  obtain ⟨b, rfl⟩ := ClosedIdealQuotient.mkHom_surjective J hJ y
  simpa only [map_mul] using congrArg (ClosedIdealQuotient.mkHom J hJ) (hcomm a b)

section Unital

variable {D : Type u} [CStarAlgebra D]

/-- A direct regression boundary: the unit is abelian exactly when the whole
algebra is commutative, because its hereditary algebra is all of `D`. -/
theorem isAbelianPositiveElement_one_iff :
    IsAbelianPositiveElement (1 : D) ↔ ∀ x y : D, x * y = y * x := by
  constructor
  · intro h x y
    exact h.mul_comm (by simp) (by simp)
  · intro h
    apply isAbelianPositiveElement_of_nonneg_of_commutative h
    simpa only [star_one, one_mul] using (star_mul_self_nonneg (1 : D))

end Unital

end MathlibAnnex.Analysis.CStarAlgebra
