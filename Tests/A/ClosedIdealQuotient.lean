import MathlibAnnex.Analysis.CStarAlgebra.TypeI.ClosedIdealQuotient

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

example (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) :
    NonUnitalCStarAlgebra (ClosedIdealQuotient.Quotient J hJ) := inferInstance

example (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) (a b : A) :
    ClosedIdealQuotient.mkHom J hJ a = ClosedIdealQuotient.mkHom J hJ b ↔
      a - b ∈ J := ClosedIdealQuotient.mkHom_eq_mkHom_iff J hJ a b

example (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) (hproper : J ≠ ⊤) :
    Nontrivial (ClosedIdealQuotient.Quotient J hJ) :=
  ClosedIdealQuotient.nontrivial_quotient J hJ hproper

example (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) (htop : J = ⊤) :
    Subsingleton (ClosedIdealQuotient.Quotient J hJ) :=
  ClosedIdealQuotient.subsingleton_quotient_of_eq_top J hJ htop

example (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (q : A →⋆ₙₐ[ℂ] B) (hq : ∀ a : A, a ∈ J → q a = 0) (a : A) :
    ClosedIdealQuotient.liftHom J hJ q hq (ClosedIdealQuotient.mkHom J hJ a) = q a :=
  ClosedIdealQuotient.liftHom_mkHom J hJ q hq a

example (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (q : A →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q)
    (hker : ∀ a : A, q a = 0 ↔ a ∈ J) (a b : A) :
    ClosedIdealQuotient.equivOfSurjective J hJ q hq hker
      (ClosedIdealQuotient.mkHom J hJ a * ClosedIdealQuotient.mkHom J hJ b) =
        q a * q b := by
  rw [map_mul, ClosedIdealQuotient.equivOfSurjective_mkHom,
    ClosedIdealQuotient.equivOfSurjective_mkHom]

end MathlibAnnex.Analysis.CStarAlgebra
