/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.UnitalQuotient

set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [CStarAlgebra A]
attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

example (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) :
    letI := ClosedIdealQuotient.quotientCStarAlgebra J hJ
    ClosedIdealQuotient.mkStarAlgHom J hJ (1 : A) = 1 := by
  letI := ClosedIdealQuotient.quotientCStarAlgebra J hJ
  exact map_one (ClosedIdealQuotient.mkStarAlgHom J hJ)

example (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) (a : A) :
    letI := ClosedIdealQuotient.quotientCStarAlgebra J hJ
    ClosedIdealQuotient.mkStarAlgHom J hJ a = 0 ↔ a ∈ J :=
  ClosedIdealQuotient.mkStarAlgHom_eq_zero_iff J hJ a

example (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) (a : A) :
    letI := ClosedIdealQuotient.quotientCStarAlgebra J hJ
    ‖ClosedIdealQuotient.mkStarAlgHom J hJ a‖ ≤ ‖a‖ :=
  ClosedIdealQuotient.norm_mkHom_le J hJ a

example (hJ : IsClosed ((⊤ : TwoSidedIdeal A) : Set A)) :
    Subsingleton (ClosedIdealQuotient.Quotient (⊤ : TwoSidedIdeal A) hJ) :=
  ClosedIdealQuotient.subsingleton_quotient_of_eq_top ⊤ hJ rfl

end MathlibAnnex.Analysis.CStarAlgebra
