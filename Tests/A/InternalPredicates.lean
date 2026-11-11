import MathlibAnnex.Analysis.CStarAlgebra.TypeI.ElementTransport

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

-- Positivity is explicit, and the carrier is the closure of aAa.
example (a : A) (ha : IsAbelianPositiveElement a) :
    0 ≤ a ∧ (hereditarySubalgebra a : Set A) =
      closure (Set.range (fun x : A => a * x * a)) :=
  ⟨ha.nonneg, coe_hereditarySubalgebra_of_isSelfAdjoint ha.nonneg.isSelfAdjoint⟩

-- The full quotient witness is consumed, not just the name of a wrapper.
example (hA : IsInternalTypeI A) (J : TwoSidedIdeal A)
    (hJ : IsClosed (J : Set A)) (hproper : J ≠ ⊤) :
    ∃ a : ClosedIdealQuotient.Quotient J hJ, a ≠ 0 ∧ 0 ≤ a ∧
      ∀ x ∈ hereditarySubalgebra a, ∀ y ∈ hereditarySubalgebra a, x * y = y * x := by
  obtain ⟨a, ha, hab⟩ := hA J hJ hproper
  exact ⟨a, ha, hab.1, hab.2⟩

example [Subsingleton A] : IsInternalTypeI A ∧ IsGCR A ∧ IsAntiliminal A :=
  ⟨isInternalTypeI_of_subsingleton, isGCR_of_subsingleton,
    isAntiliminal_of_subsingleton⟩

example (hcomm : ∀ x y : A, x * y = y * x) : IsInternalTypeI A :=
  isInternalTypeI_of_commutative hcomm

example (hA : IsInternalTypeI A) [Nontrivial B]
    (q : A →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q) :
    ∃ b : B, b ≠ 0 ∧ IsAbelianPositiveElement b := hA.exists_of_surjective q hq

example (q : A →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q)
    (a : A) (ha : IsAbelianPositiveElement a) :
    IsAbelianPositiveElement (q a) := ha.map_of_surjective q hq

example {D : Type u} [CStarAlgebra D] (x y : D) (hxy : x * y ≠ y * x) :
    ¬ IsAbelianPositiveElement (1 : D) := by
  intro h
  exact hxy (isAbelianPositiveElement_one_iff.mp h x y)

end MathlibAnnex.Analysis.CStarAlgebra
