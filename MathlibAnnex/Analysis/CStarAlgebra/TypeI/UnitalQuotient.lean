/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.ClosedIdealQuotient

/-!
# The unit of a closed-ideal quotient

The nonunital quotient already carries its actual Banach quotient norm.
For a unital source, its image of `1` acts as a two-sided identity. We reuse
Mathlib's `IsUnital.toCStarAlgebra` locally to add the unit and algebra map.
No norm, multiplication, or quotient equivalence relation is replaced.
The construction also permits the quotient by the whole algebra.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra.ClosedIdealQuotient

universe u
variable {A : Type u} [CStarAlgebra A]

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- Surjectivity makes the image of the old unit a unit of the actual quotient. -/
theorem isUnital_quotient (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) :
    IsUnital (Quotient J hJ) := by
  refine ⟨⟨mkHom J hJ 1, ?_⟩⟩
  intro x
  obtain ⟨a, rfl⟩ := mkHom_surjective J hJ x
  constructor
  · rw [← map_mul, one_mul]
  · rw [← map_mul, mul_one]

/-- Add only the unital structure to the existing C-star quotient. This is
an explicit local constructor, as recommended by Mathlib for `IsUnital`. -/
def quotientCStarAlgebra (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) :
    CStarAlgebra (Quotient J hJ) := by
  letI := isUnital_quotient J hJ
  exact IsUnital.toCStarAlgebra

/-- The newly chosen unit is the class of the source unit, by uniqueness of
a two-sided multiplicative identity. -/
theorem mkHom_one (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) :
    letI := quotientCStarAlgebra J hJ
    mkHom J hJ (1 : A) = 1 := by
  letI := quotientCStarAlgebra J hJ
  obtain ⟨a, ha⟩ := mkHom_surjective J hJ (1 : Quotient J hJ)
  calc
    mkHom J hJ 1 = mkHom J hJ 1 * 1 := (mul_one _).symm
    _ = mkHom J hJ 1 * mkHom J hJ a := by rw [ha]
    _ = mkHom J hJ a := by rw [← map_mul, one_mul]
    _ = 1 := ha

/-- The same quotient function, bundled as a unital complex star homomorphism. -/
def mkStarAlgHom (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) :
    letI := quotientCStarAlgebra J hJ
    A →⋆ₐ[ℂ] Quotient J hJ := by
  letI := quotientCStarAlgebra J hJ
  exact
    { toFun := mkHom J hJ
      map_one' := mkHom_one J hJ
      map_mul' := map_mul (mkHom J hJ)
      map_zero' := map_zero (mkHom J hJ)
      map_add' := map_add (mkHom J hJ)
      commutes' := fun c => by
        calc
          mkHom J hJ (algebraMap ℂ A c) = mkHom J hJ (c • (1 : A)) := by
            rw [Algebra.smul_def, mul_one]
          _ = c • mkHom J hJ 1 := map_smul (mkHom J hJ) c 1
          _ = algebraMap ℂ (Quotient J hJ) c := by
            rw [mkHom_one, Algebra.smul_def, mul_one]
      map_star' := map_star (mkHom J hJ) }

@[simp]
theorem mkStarAlgHom_apply (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (a : A) :
    letI := quotientCStarAlgebra J hJ
    mkStarAlgHom J hJ a = mkHom J hJ a := rfl

theorem mkStarAlgHom_surjective (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) :
    letI := quotientCStarAlgebra J hJ
    Function.Surjective (mkStarAlgHom J hJ) :=
  mkHom_surjective J hJ

@[simp]
theorem mkStarAlgHom_eq_zero_iff (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (a : A) :
    letI := quotientCStarAlgebra J hJ
    mkStarAlgHom J hJ a = 0 ↔ a ∈ J :=
  mkHom_eq_zero_iff J hJ a

end MathlibAnnex.Analysis.CStarAlgebra.ClosedIdealQuotient
