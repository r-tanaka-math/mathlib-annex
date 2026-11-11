/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.GCRSubalgebra

/-!
# GCR permanence for arbitrary closed nonunital subalgebras

The actual functorial inclusion of minimal unitizations is injective. Its
closed range is a same-unit subalgebra of the ambient unitization. Applying
the same-unit theorem there and transporting back along Mathlib's existing
range equivalence proves the result for the original nonunital subalgebra.
The zero subalgebra and algebras which already have a unit need no exception.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- Every norm-closed complex star subalgebra of a GCR C-star algebra is GCR.
Neither algebra is required to have a unit or a countable dense subset. -/
theorem IsGCR.nonUnitalStarSubalgebra (hA : IsGCR A)
    (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)] : IsGCR D := by
  let i : Unitization ℂ D →⋆ₐ[ℂ] Unitization ℂ A :=
    Unitization.starMap (NonUnitalStarSubalgebraClass.subtype D)
  have hi : Function.Injective i :=
    Unitization.starMap_injective Subtype.val_injective
  let E : StarSubalgebra ℂ (Unitization ℂ A) := i.range
  letI : IsClosed (E : Set (Unitization ℂ A)) := by
    change IsClosed (Set.range i)
    exact HomKernelQuotient.isClosed_range i.toNonUnitalStarAlgHom
  have hE : IsGCR E := hA.unitization.starSubalgebra E
  let e : Unitization ℂ D ≃⋆ₐ[ℂ] E := StarAlgEquiv.ofInjective i hi
  have hD : IsGCR (Unitization ℂ D) :=
    (isGCR_iff_of_starAlgEquiv e).mpr hE
  exact isGCR_of_unitization hD

end MathlibAnnex.Analysis.CStarAlgebra
