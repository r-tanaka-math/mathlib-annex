/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import Mathlib.Analysis.CStarAlgebra.Hom
import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.Corner
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Splitting an algebra at a central projection

Multiplication by a central projection gives a star homomorphism onto its
corner.  The two complementary maps assemble to an actual star-algebra
equivalence, with inverse addition.  The corner identities are their
projections, including when one component is zero.
-/

set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra

namespace VonNeumannAlgebra

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Multiplication by a central projection, with values in its corner. -/
def centralCornerHom (M : VonNeumannAlgebra H)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p)
    (hc : ∀ a : M.toStarSubalgebra, a * p = p * a) :
    M.toStarSubalgebra →⋆ₙₐ[ℂ] corner M p hp := by
  have hmem (a : M.toStarSubalgebra) : p * a ∈ corner M p hp := by
    constructor
    · rw [← mul_assoc, hp.isIdempotentElem.eq]
    · rw [mul_assoc, hc a, ← mul_assoc, hp.isIdempotentElem.eq]
  exact
    { toFun := fun a ↦ ⟨p * a, hmem a⟩
      map_zero' := Subtype.ext (mul_zero p)
      map_add' := fun a b ↦ Subtype.ext (mul_add p a b)
      map_smul' := fun c a ↦ Subtype.ext (by
        change p * (c • a) = c • (p * a)
        simp only [mul_smul_comm])
      map_mul' := fun a b ↦ Subtype.ext (by
        change p * (a * b) = (p * a) * (p * b)
        calc
          p * (a * b) = (p * a) * b := (mul_assoc _ _ _).symm
          _ = ((p * a) * p) * b := by rw [(hmem a).2]
          _ = (p * a) * (p * b) := mul_assoc _ _ _)
      map_star' := fun a ↦ Subtype.ext (by
        change p * star a = star (p * a)
        rw [star_mul, hp.isSelfAdjoint.star_eq]
        exact (hc (star a)).symm) }

@[simp]
theorem coe_centralCornerHom (M : VonNeumannAlgebra H)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p)
    (hc : ∀ a : M.toStarSubalgebra, a * p = p * a) (a : M.toStarSubalgebra) :
    (centralCornerHom M p hp hc a : M.toStarSubalgebra) = p * a := rfl

/-- The complementary projection is central in the same algebra. -/
theorem one_sub_commutes (M : VonNeumannAlgebra H)
    (p : M.toStarSubalgebra)
    (hc : ∀ a : M.toStarSubalgebra, a * p = p * a) (a : M.toStarSubalgebra) :
    a * (1 - p) = (1 - p) * a := by
  rw [mul_sub, sub_mul, mul_one, one_mul, hc a]

/-- An actual product decomposition at a specified central projection.
This construction does not assume or select the projection's type. -/
def centralCornerProdEquiv (M : VonNeumannAlgebra H)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p)
    (hc : ∀ a : M.toStarSubalgebra, a * p = p * a) :
    M.toStarSubalgebra ≃⋆ₐ[ℂ] (corner M p hp × corner M (1 - p) hp.one_sub) := by
  let f := centralCornerHom M p hp hc
  let g := centralCornerHom M (1 - p) hp.one_sub (one_sub_commutes M p hc)
  exact
    { toFun := fun a ↦ (f a, g a)
      invFun := fun a ↦ (a.1 : M.toStarSubalgebra) + (a.2 : M.toStarSubalgebra)
      left_inv := fun a ↦ by
        change p * a + (1 - p) * a = a
        rw [sub_mul, one_mul, add_comm, sub_add_cancel]
      right_inv := fun a ↦ by
        have hpy : p * (a.2 : M.toStarSubalgebra) = 0 := by
          calc
            p * (a.2 : M.toStarSubalgebra) =
                p * ((1 - p) * (a.2 : M.toStarSubalgebra)) := by rw [a.2.property.1]
            _ = (p * (1 - p)) * (a.2 : M.toStarSubalgebra) := (mul_assoc _ _ _).symm
            _ = 0 := by rw [hp.mul_one_sub_self, zero_mul]
        have hqx : (1 - p) * (a.1 : M.toStarSubalgebra) = 0 := by
          calc
            (1 - p) * (a.1 : M.toStarSubalgebra) =
                (1 - p) * (p * (a.1 : M.toStarSubalgebra)) := by rw [a.1.property.1]
            _ = ((1 - p) * p) * (a.1 : M.toStarSubalgebra) := (mul_assoc _ _ _).symm
            _ = 0 := by rw [hp.one_sub_mul_self, zero_mul]
        apply Prod.ext
        · apply Subtype.ext
          change p * ((a.1 : M.toStarSubalgebra) + (a.2 : M.toStarSubalgebra)) = _
          rw [mul_add, a.1.property.1, hpy, add_zero]
        · apply Subtype.ext
          change (1 - p) * ((a.1 : M.toStarSubalgebra) + (a.2 : M.toStarSubalgebra)) = _
          rw [mul_add, hqx, a.2.property.1, zero_add]
      map_mul' := fun a b ↦ Prod.ext (map_mul f a b) (map_mul g a b)
      map_add' := fun a b ↦ Prod.ext (map_add f a b) (map_add g a b)
      map_star' := fun a ↦ Prod.ext (map_star f a) (map_star g a)
      map_smul' := fun c a ↦ Prod.ext (map_smul f c a) (map_smul g c a) }

@[simp]
theorem centralCornerProdEquiv_apply_fst (M : VonNeumannAlgebra H)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p)
    (hc : ∀ a : M.toStarSubalgebra, a * p = p * a) (a : M.toStarSubalgebra) :
    ((centralCornerProdEquiv M p hp hc a).1 : M.toStarSubalgebra) = p * a := rfl

@[simp]
theorem centralCornerProdEquiv_apply_snd (M : VonNeumannAlgebra H)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p)
    (hc : ∀ a : M.toStarSubalgebra, a * p = p * a) (a : M.toStarSubalgebra) :
    ((centralCornerProdEquiv M p hp hc a).2 : M.toStarSubalgebra) = (1 - p) * a := rfl

@[simp]
theorem centralCornerProdEquiv_symm_apply (M : VonNeumannAlgebra H)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p)
    (hc : ∀ a : M.toStarSubalgebra, a * p = p * a)
    (a : corner M p hp × corner M (1 - p) hp.one_sub) :
    (centralCornerProdEquiv M p hp hc).symm a =
      (a.1 : M.toStarSubalgebra) + (a.2 : M.toStarSubalgebra) := rfl

/-- The ambient unit goes to the two genuine corner units. -/
theorem centralCornerProdEquiv_one (M : VonNeumannAlgebra H)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p)
    (hc : ∀ a : M.toStarSubalgebra, a * p = p * a) :
    centralCornerProdEquiv M p hp hc 1 =
      (cornerUnit M p hp, cornerUnit M (1 - p) hp.one_sub) := by
  apply Prod.ext <;> apply Subtype.ext <;> exact mul_one _

/-- The concrete product decomposition preserves the C-star norm.
The proved corner closedness supplies the existing Mathlib instances. -/
theorem isometry_centralCornerProdEquiv (M : VonNeumannAlgebra H)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p)
    (hc : ∀ a : M.toStarSubalgebra, a * p = p * a) :
    Isometry (centralCornerProdEquiv M p hp hc) := by
  let e := centralCornerProdEquiv M p hp hc
  exact NonUnitalStarAlgHom.isometry e.toNonUnitalStarAlgHom e.toEquiv.injective

/-- Three pairwise orthogonal central projections summing to the unit give
an actual product of their three corners. The inverse is addition. -/
def centralCornerTripleEquiv (M : VonNeumannAlgebra H)
    (p q r : M.toStarSubalgebra)
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hr : IsStarProjection r)
    (hcp : ∀ a : M.toStarSubalgebra, a * p = p * a)
    (hcq : ∀ a : M.toStarSubalgebra, a * q = q * a)
    (hcr : ∀ a : M.toStarSubalgebra, a * r = r * a)
    (hpq : p * q = 0) (hpr : p * r = 0) (hqr : q * r = 0)
    (hsum : p + q + r = 1) :
    M.toStarSubalgebra ≃⋆ₐ[ℂ] (corner M p hp × corner M q hq × corner M r hr) := by
  let f := centralCornerHom M p hp hcp
  let g := centralCornerHom M q hq hcq
  let h := centralCornerHom M r hr hcr
  have hqp : q * p = 0 := by rw [hcp q, hpq]
  have hrp : r * p = 0 := by rw [hcp r, hpr]
  have hrq : r * q = 0 := by rw [hcq r, hqr]
  have cross (e t : M.toStarSubalgebra) (ht : IsStarProjection t)
      (het : e * t = 0) (x : corner M t ht) : e * (x : M.toStarSubalgebra) = 0 := by
    calc
      e * (x : M.toStarSubalgebra) = e * (t * (x : M.toStarSubalgebra)) :=
        by rw [x.property.1]
      _ = (e * t) * (x : M.toStarSubalgebra) := (mul_assoc _ _ _).symm
      _ = 0 := by rw [het, zero_mul]
  exact
    { toFun := fun a ↦ (f a, g a, h a)
      invFun := fun a ↦ (a.1 : M.toStarSubalgebra) +
        (a.2.1 : M.toStarSubalgebra) + (a.2.2 : M.toStarSubalgebra)
      left_inv := fun a ↦ by
        change p * a + q * a + r * a = a
        rw [← add_mul, ← add_mul, hsum, one_mul]
      right_inv := fun a ↦ by
        apply Prod.ext
        · apply Subtype.ext
          change p * ((a.1 : M.toStarSubalgebra) + (a.2.1 : M.toStarSubalgebra) +
            (a.2.2 : M.toStarSubalgebra)) = _
          simp only [mul_add, a.1.property.1,
            cross p q hq hpq a.2.1, cross p r hr hpr a.2.2, add_zero]
        · apply Prod.ext
          · apply Subtype.ext
            change q * ((a.1 : M.toStarSubalgebra) + (a.2.1 : M.toStarSubalgebra) +
              (a.2.2 : M.toStarSubalgebra)) = _
            simp only [mul_add, cross q p hp hqp a.1,
              a.2.1.property.1, cross q r hr hqr a.2.2, zero_add, add_zero]
          · apply Subtype.ext
            change r * ((a.1 : M.toStarSubalgebra) + (a.2.1 : M.toStarSubalgebra) +
              (a.2.2 : M.toStarSubalgebra)) = _
            simp only [mul_add, cross r p hp hrp a.1,
              cross r q hq hrq a.2.1, a.2.2.property.1, zero_add]
      map_mul' := fun a b ↦ Prod.ext (map_mul f a b)
        (Prod.ext (map_mul g a b) (map_mul h a b))
      map_add' := fun a b ↦ Prod.ext (map_add f a b)
        (Prod.ext (map_add g a b) (map_add h a b))
      map_star' := fun a ↦ Prod.ext (map_star f a)
        (Prod.ext (map_star g a) (map_star h a))
      map_smul' := fun c a ↦ Prod.ext (map_smul f c a)
        (Prod.ext (map_smul g c a) (map_smul h c a)) }

/-- The three-factor equivalence maps one to the three actual corner units. -/
theorem centralCornerTripleEquiv_one (M : VonNeumannAlgebra H)
    (p q r : M.toStarSubalgebra)
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hr : IsStarProjection r)
    (hcp : ∀ a : M.toStarSubalgebra, a * p = p * a)
    (hcq : ∀ a : M.toStarSubalgebra, a * q = q * a)
    (hcr : ∀ a : M.toStarSubalgebra, a * r = r * a)
    (hpq : p * q = 0) (hpr : p * r = 0) (hqr : q * r = 0)
    (hsum : p + q + r = 1) :
    centralCornerTripleEquiv M p q r hp hq hr hcp hcq hcr hpq hpr hqr hsum 1 =
      (cornerUnit M p hp, cornerUnit M q hq, cornerUnit M r hr) := by
  apply Prod.ext
  · apply Subtype.ext
    exact mul_one _
  · apply Prod.ext <;> apply Subtype.ext <;> exact mul_one _

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 900000 in
/-- The genuine C-star norm of the three-corner product is preserved. -/
theorem isometry_centralCornerTripleEquiv (M : VonNeumannAlgebra H)
    (p q r : M.toStarSubalgebra)
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hr : IsStarProjection r)
    (hcp : ∀ a : M.toStarSubalgebra, a * p = p * a)
    (hcq : ∀ a : M.toStarSubalgebra, a * q = q * a)
    (hcr : ∀ a : M.toStarSubalgebra, a * r = r * a)
    (hpq : p * q = 0) (hpr : p * r = 0) (hqr : q * r = 0)
    (hsum : p + q + r = 1) :
    Isometry (centralCornerTripleEquiv M p q r hp hq hr hcp hcq hcr hpq hpr hqr hsum) := by
  let e := centralCornerTripleEquiv M p q r hp hq hr hcp hcq hcr hpq hpr hqr hsum
  exact NonUnitalStarAlgHom.isometry e.toNonUnitalStarAlgHom e.toEquiv.injective

end VonNeumannAlgebra
