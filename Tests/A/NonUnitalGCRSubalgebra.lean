/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.NonUnitalGCRSubalgebra

set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

example (hA : IsGCR A) (D : NonUnitalStarSubalgebra ℂ A)
    (hD : IsClosed (D : Set A)) :
    letI := hD
    IsGCR D := by
  letI := hD
  exact hA.nonUnitalStarSubalgebra D

example (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)] :
    Function.Injective (Unitization.starMap (NonUnitalStarSubalgebraClass.subtype D)) :=
  Unitization.starMap_injective Subtype.val_injective

example (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)] (d : D) :
    Unitization.starMap (NonUnitalStarSubalgebraClass.subtype D)
      (Unitization.inr d) = (Unitization.inr (d : A) : Unitization ℂ A) :=
  Unitization.starMap_inr _ d

example (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)] :
    IsClosed (Set.range (Unitization.starMap (NonUnitalStarSubalgebraClass.subtype D))) :=
  HomKernelQuotient.isClosed_range
    (Unitization.starMap (NonUnitalStarSubalgebraClass.subtype D)).toNonUnitalStarAlgHom

end MathlibAnnex.Analysis.CStarAlgebra
