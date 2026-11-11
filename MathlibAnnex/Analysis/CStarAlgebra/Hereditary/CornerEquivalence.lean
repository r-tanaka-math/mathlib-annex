/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.Hereditary.Generated
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Conjugation between genuine hereditary corners

If `c` is self-adjoint and `v⋆ v c = c`, conjugation by `v` is an actual
nonunital star-algebra equivalence from `Her(c)` onto `Her(v c v⋆)`.
The multiplier `v⋆ v` need not be a projection. Its action on the entire
closed sandwich algebra is proved by taking a closed equalizer.

Both maps are given by ambient multiplication, and the inherited C-star norms
agree by the existing isometry theorem for injective nonunital star homomorphisms.
No unit, separability, nonzero projection, or ambient polar decomposition is used.
-/

set_option autoImplicit false
noncomputable section

open Set

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- Fixing the left generator fixes every element of its closed sandwich algebra. -/
theorem mul_eq_self_of_mem_hereditarySubalgebra {a e z : A}
    (he : e * a = a) (hz : z ∈ hereditarySubalgebra a) : e * z = z := by
  apply closure_minimal
    (s := (sandwichSubalgebra a : Set A))
    (t := {z : A | e * z = z}) _ _ hz
  · rintro _ ⟨b, rfl⟩
    calc
      e * (a * b * star a) = (e * a) * b * star a := by simp only [mul_assoc]
      _ = a * b * star a := by rw [he]
  · exact isClosed_eq (continuous_const.mul continuous_id) continuous_id

/-- Fixing the right generator fixes every element of its closed sandwich algebra. -/
theorem mul_eq_self_of_mem_hereditarySubalgebra_right {a e z : A}
    (he : star a * e = star a) (hz : z ∈ hereditarySubalgebra a) : z * e = z := by
  apply closure_minimal
    (s := (sandwichSubalgebra a : Set A))
    (t := {z : A | z * e = z}) _ _ hz
  · rintro _ ⟨b, rfl⟩
    calc
      (a * b * star a) * e = (a * b) * (star a * e) := mul_assoc _ _ _
      _ = a * b * star a := by rw [he]
  · exact isClosed_eq (continuous_id.mul continuous_const) continuous_id

/-- Left annihilation passes from the generator to its full norm-closed sandwich algebra. -/
theorem mul_eq_zero_of_mem_hereditarySubalgebra_left {a e z : A}
    (he : e * a = 0) (hz : z ∈ hereditarySubalgebra a) : e * z = 0 := by
  apply closure_minimal
    (s := (sandwichSubalgebra a : Set A))
    (t := {z : A | e * z = 0}) _ _ hz
  · rintro _ ⟨b, rfl⟩
    calc
      e * (a * b * star a) = (e * a) * b * star a := by simp only [mul_assoc]
      _ = 0 := by rw [he, zero_mul, zero_mul]
  · exact isClosed_eq (continuous_const.mul continuous_id) continuous_const

/-- Right annihilation passes from the adjoint generator to the full closed sandwich algebra. -/
theorem mul_eq_zero_of_mem_hereditarySubalgebra_right {a e z : A}
    (he : star a * e = 0) (hz : z ∈ hereditarySubalgebra a) : z * e = 0 := by
  apply closure_minimal
    (s := (sandwichSubalgebra a : Set A))
    (t := {z : A | z * e = 0}) _ _ hz
  · rintro _ ⟨b, rfl⟩
    calc
      (a * b * star a) * e = (a * b) * (star a * e) := mul_assoc _ _ _
      _ = 0 := by rw [he, mul_zero]
  · exact isClosed_eq (continuous_id.mul continuous_const) continuous_const

private theorem conjugate_right_fixed {c v : A} (hc : IsSelfAdjoint c)
    (hv : star v * v * c = c) : c * (star v * v) = c := by
  have h := congrArg star hv
  simpa only [star_mul, star_star, hc.star_eq, mul_assoc] using h

/-- The two conjugated factors multiply using the original corner product.
Only the right input has to lie in the corner for this identity. -/
theorem conjugate_mul_conjugate_of_mem_hereditarySubalgebra {c v z w : A}
    (hv : star v * v * c = c) (hw : w ∈ hereditarySubalgebra c) :
    (v * z * star v) * (v * w * star v) = v * (z * w) * star v := by
  calc
    (v * z * star v) * (v * w * star v) =
        v * z * ((star v * v) * w) * star v := by simp only [mul_assoc]
    _ = v * z * w * star v := by
      rw [mul_eq_self_of_mem_hereditarySubalgebra hv hw]
    _ = v * (z * w) * star v := by simp only [mul_assoc]

/-- Conjugation maps into the genuine hereditary algebra of the conjugated
generator, with all ambient middle coefficients accounted for before closure. -/
theorem mul_conjugate_mem_hereditarySubalgebra {c v z : A}
    (hc : IsSelfAdjoint c) (hv : star v * v * c = c)
    (hz : z ∈ hereditarySubalgebra c) :
    v * z * star v ∈ hereditarySubalgebra (v * c * star v) := by
  have hright := conjugate_right_fixed hc hv
  apply closure_minimal
    (s := (sandwichSubalgebra c : Set A))
    (t := {z : A | v * z * star v ∈ hereditarySubalgebra (v * c * star v)}) _ _ hz
  · rintro _ ⟨b, rfl⟩
    have heq :
        v * (c * b * star c) * star v =
          (v * c * star v) * (v * b * star v) * star (v * c * star v) := by
      simp only [star_mul, star_star, hc.star_eq]
      calc
        v * (c * b * c) * star v =
            v * ((c * (star v * v)) * b * ((star v * v) * c)) * star v := by
              rw [hright, hv]
        _ = _ := by simp only [mul_assoc]
    change v * (c * b * star c) * star v ∈ hereditarySubalgebra (v * c * star v)
    rw [heq]
    exact sandwich_mem_hereditarySubalgebra (v * c * star v) (v * b * star v)
  · exact (isClosed_hereditarySubalgebra (v * c * star v)).preimage
      ((continuous_const.mul continuous_id).mul continuous_const)

/-- Conjugation is a concrete nonunital star homomorphism between the two
closed hereditary subalgebras. -/
def hereditaryConjugateHom {c v : A} (hc : IsSelfAdjoint c)
    (hv : star v * v * c = c) :
    hereditarySubalgebra c →⋆ₙₐ[ℂ] hereditarySubalgebra (v * c * star v) where
  toFun z := ⟨v * (z : A) * star v, mul_conjugate_mem_hereditarySubalgebra hc hv z.property⟩
  map_zero' := Subtype.ext (by simp)
  map_add' z w := Subtype.ext (by
    change v * ((z : A) + w) * star v = v * z * star v + v * w * star v
    rw [mul_add, add_mul])
  map_mul' z w := Subtype.ext
    (conjugate_mul_conjugate_of_mem_hereditarySubalgebra hv w.property).symm
  map_smul' r z := Subtype.ext (by
    change v * (r • (z : A)) * star v = r • (v * z * star v)
    rw [mul_smul_comm, smul_mul_assoc])
  map_star' z := Subtype.ext (by
    change v * star (z : A) * star v = star (v * z * star v)
    simp only [star_mul, star_star, mul_assoc])

@[simp]
theorem coe_hereditaryConjugateHom {c v : A} (hc : IsSelfAdjoint c)
    (hv : star v * v * c = c) (z : hereditarySubalgebra c) :
    (hereditaryConjugateHom hc hv z : A) = v * (z : A) * star v := rfl

private theorem conjugate_generator_selfAdjoint {c v : A} (hc : IsSelfAdjoint c) :
    IsSelfAdjoint (v * c * star v) := by
  show star (v * c * star v) = v * c * star v
  simp only [star_mul, star_star, hc.star_eq, mul_assoc]

private theorem conjugate_generator_fixed {c v : A}
    (hv : star v * v * c = c) :
    v * star v * (v * c * star v) = v * c * star v := by
  calc
    v * star v * (v * c * star v) = v * (star v * v * c) * star v := by
      simp only [mul_assoc]
    _ = v * c * star v := by rw [hv]

/-- The proposed inverse sends the conjugated generator back to the original one. -/
theorem star_mul_conjugate_mul_eq {c v : A} (hc : IsSelfAdjoint c)
    (hv : star v * v * c = c) :
    star v * (v * c * star v) * v = c := by
  calc
    star v * (v * c * star v) * v = (star v * v * c) * (star v * v) := by
      simp only [mul_assoc]
    _ = c * (star v * v) := by rw [hv]
    _ = c := conjugate_right_fixed hc hv

/-- The inverse conjugation really maps the full target hereditary algebra back. -/
theorem star_mul_mem_hereditarySubalgebra_mul {c v w : A}
    (hc : IsSelfAdjoint c) (hv : star v * v * c = c)
    (hw : w ∈ hereditarySubalgebra (v * c * star v)) :
    star v * w * v ∈ hereditarySubalgebra c := by
  have hq := conjugate_generator_selfAdjoint (v := v) hc
  have hfix : star (star v) * star v * (v * c * star v) = v * c * star v := by
    simpa only [star_star] using conjugate_generator_fixed hv
  have hmem := mul_conjugate_mem_hereditarySubalgebra hq hfix hw
  simpa only [star_star, star_mul_conjugate_mul_eq hc hv] using hmem

/-- The two explicit ambient conjugation maps give an actual star-algebra
equivalence. No ambient inverse for `v` is claimed or used. -/
def hereditaryConjugateEquiv {c v : A} (hc : IsSelfAdjoint c)
    (hv : star v * v * c = c) :
    hereditarySubalgebra c ≃⋆ₐ[ℂ] hereditarySubalgebra (v * c * star v) where
  toFun := hereditaryConjugateHom hc hv
  invFun w := ⟨star v * (w : A) * v, star_mul_mem_hereditarySubalgebra_mul hc hv w.property⟩
  left_inv z := by
    apply Subtype.ext
    change star v * (v * (z : A) * star v) * v = (z : A)
    have hright : star c * (star v * v) = star c := by
      simpa only [hc.star_eq] using conjugate_right_fixed hc hv
    calc
      star v * (v * (z : A) * star v) * v =
          ((star v * v) * (z : A)) * (star v * v) := by simp only [mul_assoc]
      _ = (z : A) * (star v * v) := by
        rw [mul_eq_self_of_mem_hereditarySubalgebra hv z.property]
      _ = (z : A) := mul_eq_self_of_mem_hereditarySubalgebra_right hright z.property
  right_inv w := by
    apply Subtype.ext
    change v * (star v * (w : A) * v) * star v = (w : A)
    have hfix := conjugate_generator_fixed hv
    have hright : star (v * c * star v) * (v * star v) = star (v * c * star v) := by
      have h := congrArg star hfix
      simpa only [star_mul, star_star, hc.star_eq, mul_assoc] using h
    calc
      v * (star v * (w : A) * v) * star v =
          ((v * star v) * (w : A)) * (v * star v) := by simp only [mul_assoc]
      _ = (w : A) * (v * star v) := by
        rw [mul_eq_self_of_mem_hereditarySubalgebra hfix w.property]
      _ = (w : A) := mul_eq_self_of_mem_hereditarySubalgebra_right hright w.property
  map_mul' := map_mul (hereditaryConjugateHom hc hv)
  map_add' := map_add (hereditaryConjugateHom hc hv)
  map_smul' := map_smul (hereditaryConjugateHom hc hv)
  map_star' := map_star (hereditaryConjugateHom hc hv)

@[simp]
theorem coe_hereditaryConjugateEquiv {c v : A} (hc : IsSelfAdjoint c)
    (hv : star v * v * c = c) (z : hereditarySubalgebra c) :
    (hereditaryConjugateEquiv hc hv z : A) = v * (z : A) * star v := rfl

@[simp]
theorem coe_hereditaryConjugateEquiv_symm {c v : A} (hc : IsSelfAdjoint c)
    (hv : star v * v * c = c) (w : hereditarySubalgebra (v * c * star v)) :
    ((hereditaryConjugateEquiv hc hv).symm w : A) = star v * (w : A) * v := rfl

/-- The inherited C-star norms of the two actual hereditary algebras agree. -/
theorem norm_conjugate_of_mem_hereditarySubalgebra {c v z : A}
    (hc : IsSelfAdjoint c) (hv : star v * v * c = c)
    (hz : z ∈ hereditarySubalgebra c) : ‖v * z * star v‖ = ‖z‖ :=
  NonUnitalStarAlgHom.norm_map (hereditaryConjugateEquiv hc hv)
    (hereditaryConjugateEquiv hc hv).injective ⟨z, hz⟩

theorem isometry_hereditaryConjugateEquiv {c v : A} (hc : IsSelfAdjoint c)
    (hv : star v * v * c = c) : Isometry (hereditaryConjugateEquiv hc hv) :=
  NonUnitalStarAlgHom.isometry (hereditaryConjugateEquiv hc hv)
    (hereditaryConjugateEquiv hc hv).injective

end MathlibAnnex.Analysis.CStarAlgebra
