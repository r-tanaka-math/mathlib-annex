/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartLinked
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Projective coordinates on the existing normal part

The factors are Mathlib's actual `Projectivization ℂ H`. The codomain remains
the original normal-part subtype, not a second definition by coordinate labels.
The equivalence does not replace or transport its inherited closure structure.
The representative and inverse formulas explicitly remove dependence on choices.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped LinearAlgebra.Projectivization

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable [IsClosed (S : Set (H →L[ℂ] H))]
variable (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))

/-- Kernel equality in literal Mathlib projective coordinates. -/
theorem normalPartPoint_eq_iff_projectivization_eq_and_eq
    (x₁ x₂ y₁ y₂ : H) (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) :
    normalPartPoint S hS x₁ y₁ hx₁ hy₁ = normalPartPoint S hS x₂ y₂ hx₂ hy₂ ↔
      Projectivization.mk ℂ x₁ hx₁ = Projectivization.mk ℂ x₂ hx₂ ∧
      Projectivization.mk ℂ y₁ hy₁ = Projectivization.mk ℂ y₂ hy₂ := by
  rw [normalPartPoint_eq_iff_span_eq_and_span_eq]
  constructor
  · rintro ⟨hX, hY⟩
    exact ⟨Projectivization.submodule_injective hX, Projectivization.submodule_injective hY⟩
  · rintro ⟨hX, hY⟩
    exact ⟨congrArg Projectivization.submodule hX, congrArg Projectivization.submodule hY⟩

/-- A choice of projective representatives gives an actual normal kernel point. -/
def normalPartProjectivizationMap (p : (ℙ ℂ H) × (ℙ ℂ H)) : normalPart S :=
  normalPartPoint S hS p.1.rep p.2.rep p.1.rep_nonzero p.2.rep_nonzero

/-- Evaluation on any nonzero representatives, not merely the chosen ones. -/
@[simp]
theorem normalPartProjectivizationMap_mk (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    normalPartProjectivizationMap S hS
      (Projectivization.mk ℂ x hx, Projectivization.mk ℂ y hy) =
        normalPartPoint S hS x y hx hy := by
  apply (normalPartPoint_eq_iff_projectivization_eq_and_eq S hS _ _ _ _ _ _ _ _).2
  exact ⟨Projectivization.mk_rep _, Projectivization.mk_rep _⟩

/-- Both projective coordinates are recoverable from the kernel. -/
theorem normalPartProjectivizationMap_injective :
    Function.Injective (normalPartProjectivizationMap S hS) := by
  intro p q hpq
  have hh := (normalPartPoint_eq_iff_projectivization_eq_and_eq S hS
    p.1.rep q.1.rep p.2.rep q.2.rep
    p.1.rep_nonzero q.1.rep_nonzero p.2.rep_nonzero q.2.rep_nonzero).1 hpq
  exact Prod.ext (by simpa using hh.1) (by simpa using hh.2)

/-- The existing normal-part membership supplies all projective coordinates. -/
theorem normalPartProjectivizationMap_surjective :
    Function.Surjective (normalPartProjectivizationMap S hS) := by
  intro I
  obtain ⟨x, y, hx, hy, rfl⟩ := exists_normalPartPoint_eq S hS I
  exact ⟨(Projectivization.mk ℂ x hx, Projectivization.mk ℂ y hy),
    normalPartProjectivizationMap_mk S hS x y hx hy⟩

/-- The projective product is in bijection with the ACTUAL normal part. -/
def normalPartProjectivizationEquiv : (ℙ ℂ H) × (ℙ ℂ H) ≃ normalPart S :=
  Equiv.ofBijective (normalPartProjectivizationMap S hS)
    ⟨normalPartProjectivizationMap_injective S hS,
      normalPartProjectivizationMap_surjective S hS⟩

/-- Literal kernel evaluation, with the prescribed source/target convention. -/
@[simp]
theorem normalPartProjectivizationEquiv_val_val (p : (ℙ ℂ H) × (ℙ ℂ H)) :
    (normalPartProjectivizationEquiv S hS p).val.val =
      {a : S | inner ℂ p.2.rep ((a : H →L[ℂ] H) p.1.rep) = 0} := rfl

@[simp]
theorem normalPartProjectivizationEquiv_mk (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    normalPartProjectivizationEquiv S hS
      (Projectivization.mk ℂ x hx, Projectivization.mk ℂ y hy) =
        normalPartPoint S hS x y hx hy :=
  normalPartProjectivizationMap_mk S hS x y hx hy

/-- The inverse formula holds for EVERY nonzero coefficient representative. -/
@[simp]
theorem normalPartProjectivizationEquiv_symm_point (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    (normalPartProjectivizationEquiv S hS).symm (normalPartPoint S hS x y hx hy) =
      (Projectivization.mk ℂ x hx, Projectivization.mk ℂ y hy) := by
  apply (normalPartProjectivizationEquiv S hS).injective
  rw [Equiv.apply_symm_apply, normalPartProjectivizationEquiv_mk]

/-- Scalar rescaling in each slot preserves the point; the target coefficient
itself is conjugate-linear, although the zero set forgets the nonzero factor. -/
theorem normalPartPoint_smul_smul (x y : H) (hx : x ≠ 0) (hy : y ≠ 0)
    (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    normalPartPoint S hS (a • x) (b • y) (smul_ne_zero ha hx) (smul_ne_zero hb hy) =
      normalPartPoint S hS x y hx hy := by
  apply (normalPartPoint_eq_iff_projectivization_eq_and_eq S hS _ _ _ _ _ _ _ _).2
  exact ⟨(Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨a, rfl⟩,
    (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨b, rfl⟩⟩

/-- The coordinate product records the normal-part link relation, without
putting a new closure on the product. -/
theorem linked_normalPartProjectivizationEquiv_iff (p q : (ℙ ℂ H) × (ℙ ℂ H)) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Linked
      (normalPartProjectivizationEquiv S hS p) (normalPartProjectivizationEquiv S hS q) ↔
        p.1 = q.1 ∨ p.2 = q.2 := by
  change ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Linked
    (normalPartPoint S hS p.1.rep p.2.rep p.1.rep_nonzero p.2.rep_nonzero)
    (normalPartPoint S hS q.1.rep q.2.rep q.1.rep_nonzero q.2.rep_nonzero) ↔ _
  rw [linked_normalPartPoint_iff_span_eq_or_span_eq]
  constructor
  · rintro (h | h)
    · left
      apply Projectivization.submodule_injective
      simpa only [Projectivization.submodule_eq] using h
    · right
      apply Projectivization.submodule_injective
      simpa only [Projectivization.submodule_eq] using h
  · rintro (h | h)
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])

/-- Kernel equality is dependence in BOTH slots; the family formulation
continues to distinguish repeated vectors from a singleton set. -/
theorem normalPartPoint_eq_iff_not_linearIndependent_and_not_linearIndependent
    (x₁ x₂ y₁ y₂ : H) (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) :
    normalPartPoint S hS x₁ y₁ hx₁ hy₁ = normalPartPoint S hS x₂ y₂ hx₂ hy₂ ↔
      ¬ LinearIndependent ℂ ![x₁, x₂] ∧ ¬ LinearIndependent ℂ ![y₁, y₂] := by
  rw [normalPartPoint_eq_iff_projectivization_eq_and_eq]
  have dep (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
      Projectivization.mk ℂ x hx = Projectivization.mk ℂ y hy ↔
        ¬ LinearIndependent ℂ ![x, y] := by
    rw [eq_comm, Projectivization.mk_eq_mk_iff', LinearIndependent.pair_iff' hx]
    simp only [not_forall, not_not]
  exact and_congr (dep x₁ x₂ hx₁ hx₂) (dep y₁ y₂ hy₁ hy₂)

/-- The literal disjunction-of-dependence form of Lemma 6.10. -/
theorem linked_normalPartPoint_iff_not_linearIndependent_or_not_linearIndependent
    (x₁ x₂ y₁ y₂ : H) (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Linked
      (normalPartPoint S hS x₁ y₁ hx₁ hy₁) (normalPartPoint S hS x₂ y₂ hx₂ hy₂) ↔
        ¬ LinearIndependent ℂ ![x₁, x₂] ∨ ¬ LinearIndependent ℂ ![y₁, y₂] := by
  rw [← normalPartProjectivizationEquiv_mk S hS x₁ y₁ hx₁ hy₁,
    ← normalPartProjectivizationEquiv_mk S hS x₂ y₂ hx₂ hy₂,
    linked_normalPartProjectivizationEquiv_iff]
  have dep (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
      Projectivization.mk ℂ x hx = Projectivization.mk ℂ y hy ↔
        ¬ LinearIndependent ℂ ![x, y] := by
    rw [eq_comm, Projectivization.mk_eq_mk_iff', LinearIndependent.pair_iff' hx]
    simp only [not_forall, not_not]
  exact or_congr (dep x₁ x₂ hx₁ hx₂) (dep y₁ y₂ hy₁ hy₂)

end MathlibAnnex.Analysis.CStarAlgebra
