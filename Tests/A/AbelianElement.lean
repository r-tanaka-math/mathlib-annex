/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.AbelianElement

/-! Typed consumers of the original abelian-element hypothesis. The compact
conclusion and the rank-one formula are derived, not consumer assumptions. -/

set_option autoImplicit false
noncomputable section

open Set InnerProductSpace
open MathlibAnnex.Analysis.CStarAlgebra
open scoped CStarAlgebra

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example {a : A} (ha : IsAbelianPositiveElement a)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    IsCompactOperator (pi a) :=
  ha.isCompactOperator pi hpi

example {a : A} (ha : IsAbelianPositiveElement a)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (hne : pi a ≠ 0) :
    ∃ x : H, pi a x ≠ 0 ∧
      pi a = (inner ℂ (pi a x) (pi a x))⁻¹ •
        rankOne ℂ (pi a x) (pi a (pi a x)) :=
  ha.exists_eq_smul_rankOne pi hpi hne

example {a : A} (ha : IsAbelianPositiveElement a) (ha0 : a ≠ 0)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (hfaithful : Function.Injective pi) :
    ∃ T : H →L[ℂ] H,
      T ∈ NonUnitalStarAlgHom.range pi ∧ IsCompactOperator T ∧ T ≠ 0 := by
  refine ⟨pi a, (NonUnitalStarAlgHom.mem_range pi).2 ⟨a, rfl⟩,
    ha.isCompactOperator pi hpi, ?_⟩
  intro hz
  apply ha0
  apply hfaithful
  simpa only [map_zero] using hz

example {a : A} (ha : IsAbelianPositiveElement a)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (T U : H →L[ℂ] H) :
    (pi a * T * pi a) * (pi a * U * pi a) =
      (pi a * U * pi a) * (pi a * T * pi a) :=
  ha.sandwiches_commute pi hpi T U
