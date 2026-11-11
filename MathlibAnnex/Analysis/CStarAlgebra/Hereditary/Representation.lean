/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.Hereditary.Generated
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.Image

/-!
# Closed sandwich subalgebras under C⋆-homomorphisms

A homomorphism sends the closed sandwich algebra into the corresponding ambient
sandwich algebra. Equality requires surjectivity onto the ambient codomain.
Closedness of the image is obtained by restricting the homomorphism to the complete
subalgebra and applying the existing C⋆ first-isomorphism theorem.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} {B : Type v}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

theorem sandwichSubalgebra_map_le (φ : A →⋆ₙₐ[ℂ] B) (a : A) :
    (sandwichSubalgebra a).map φ ≤ sandwichSubalgebra (φ a) := by
  rintro _ ⟨x, ⟨y, rfl⟩, rfl⟩
  refine ⟨φ y, ?_⟩
  change φ a * φ y * star (φ a) = φ (a * y * star a)
  rw [map_mul, map_mul, map_star]

/-- Arbitrary C⋆-homomorphisms give containment. No assertion is made about
ambient coefficients outside the image of the homomorphism. -/
theorem hereditarySubalgebra_map_le (φ : A →⋆ₙₐ[ℂ] B) (a : A) :
    (hereditarySubalgebra a).map φ ≤ hereditarySubalgebra (φ a) := by
  calc
    (hereditarySubalgebra a).map φ ≤
        ((sandwichSubalgebra a).map φ).topologicalClosure :=
      NonUnitalStarSubalgebra.map_topologicalClosure_le _ (map_continuous φ)
    _ ≤ (sandwichSubalgebra (φ a)).topologicalClosure :=
      NonUnitalStarSubalgebra.topologicalClosure_mono (sandwichSubalgebra_map_le φ a)

/-- The image of a norm-closed non-unital star subalgebra under a C⋆-homomorphism
is norm closed. This is a restricted-homomorphism application of the existing
closed-image theorem, not a claim that the homomorphism is a closed map on sets. -/
theorem isClosed_map_nonUnitalStarSubalgebra (φ : A →⋆ₙₐ[ℂ] B)
    (S : NonUnitalStarSubalgebra ℂ A) (hS : IsClosed (S : Set A)) :
    IsClosed (S.map φ : Set B) := by
  letI : IsClosed (S : Set A) := hS
  letI : PartialOrder S := _root_.CStarAlgebra.spectralOrder S
  letI : StarOrderedRing S := _root_.CStarAlgebra.spectralOrderedRing S
  letI : PartialOrder B := _root_.CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := _root_.CStarAlgebra.spectralOrderedRing B
  let ψ : S →⋆ₙₐ[ℂ] B := φ.comp (NonUnitalStarSubalgebraClass.subtype S)
  have hc := HomKernelQuotient.isClosed_image ψ
  have hr : (NonUnitalStarAlgHom.range ψ : Set B) = (S.map φ : Set B) := by
    ext b
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s.1, s.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  rwa [hr] at hc

/-- Under a surjective C⋆-homomorphism the image of `Her(a)` is exactly
`Her(φ a)`. This applies in particular to actual C⋆ quotient maps. -/
theorem hereditarySubalgebra_map_of_surjective (φ : A →⋆ₙₐ[ℂ] B)
    (hφ : Function.Surjective φ) (a : A) :
    (hereditarySubalgebra a).map φ = hereditarySubalgebra (φ a) := by
  apply le_antisymm (hereditarySubalgebra_map_le φ a)
  apply hereditarySubalgebra_le (φ a)
    (isClosed_map_nonUnitalStarSubalgebra φ _ (isClosed_hereditarySubalgebra a))
  intro b
  obtain ⟨x, rfl⟩ := hφ b
  refine ⟨a * x * star a, sandwich_mem_hereditarySubalgebra a x, ?_⟩
  change φ (a * x * star a) = φ a * φ x * star (φ a)
  rw [map_mul, map_mul, map_star]

/-- A concrete preimage witness for membership in the hereditary algebra of a
quotient element. The witness stays in the source hereditary algebra. -/
theorem mem_hereditarySubalgebra_image_iff (φ : A →⋆ₙₐ[ℂ] B)
    (hφ : Function.Surjective φ) (a : A) (b : B) :
    b ∈ hereditarySubalgebra (φ a) ↔
      ∃ x ∈ hereditarySubalgebra a, φ x = b := by
  rw [← hereditarySubalgebra_map_of_surjective φ hφ a]
  exact NonUnitalStarSubalgebra.mem_map

end MathlibAnnex.Analysis.CStarAlgebra
