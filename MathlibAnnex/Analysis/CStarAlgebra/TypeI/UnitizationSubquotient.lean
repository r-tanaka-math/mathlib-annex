/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.

The range construction adapts the local unitization argument in the supplied
TypeI/NonUnitalGCRSubalgebra.lean. Mathlib's starMap, injectivity theorem and
range equivalence are reused. The published actual-kernel-quotient theorem
supplies closed range; none of these providers is redeclared or edited.
-/

import Mathlib.Analysis.CStarAlgebra.Unitization
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.KernelNorm

/-!
# Unitizing an actual closed nonunital subquotient diagram

A closed nonunital subalgebra `D` of `A` has an actual closed same-unit
image inside `Unitization ℂ A`: the range of Mathlib's functorial `starMap`
of the subtype inclusion. The existing range equivalence identifies it
with `Unitization ℂ D` and retains the full inclusion diagram.

An actual surjection from `D` onto any unital C-star algebra extends to a
surjection from this same-unit image. Both homomorphism diagrams and the
formula on original elements are proved. The target may live in an
independent universe. No unit, separability, or nonzeroness of the original
ambient algebra or of `D` is assumed.

The construction uses existing carriers and maps and returns their proved
properties. It introduces no alternative unitization or quotient definition.
-/

set_option autoImplicit false
noncomputable section

open Set
open MathlibAnnex.Analysis.CStarAlgebra
open scoped CStarAlgebra

namespace NonUnitalStarSubalgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- The formal/functorial unitization of a closed nonunital subalgebra is identified
with its actual closed, same-unit range in the ambient unitization. -/
theorem exists_unitization_range_equiv
    (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)] :
    ∃ (E : StarSubalgebra ℂ (Unitization ℂ A))
        (_hE : IsClosed (E : Set (Unitization ℂ A)))
        (e : Unitization ℂ D ≃⋆ₐ[ℂ] E),
      E.subtype.comp e.toStarAlgHom =
        Unitization.starMap (NonUnitalStarSubalgebraClass.subtype D) := by
  let i : Unitization ℂ D →⋆ₐ[ℂ] Unitization ℂ A :=
    Unitization.starMap (NonUnitalStarSubalgebraClass.subtype D)
  have hi : Function.Injective i :=
    Unitization.starMap_injective Subtype.val_injective
  let E : StarSubalgebra ℂ (Unitization ℂ A) := i.range
  have hE : IsClosed (E : Set (Unitization ℂ A)) := by
    change IsClosed (Set.range i)
    exact HomKernelQuotient.isClosed_range i.toNonUnitalStarAlgHom
  let e : Unitization ℂ D ≃⋆ₐ[ℂ] E := StarAlgEquiv.ofInjective i hi
  refine ⟨E, hE, e, ?_⟩
  apply StarAlgHom.ext
  intro z
  rfl

/-- A genuine surjection from a closed nonunital subalgebra to a unital
C-star algebra extends to the actual closed same-unit subalgebra of the
ambient unitization. The original inclusion and quotient diagrams commute. -/
theorem exists_unitization_subquotient
    (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)]
    {B : Type v} [CStarAlgebra B]
    (q : D →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q) :
    ∃ (E : StarSubalgebra ℂ (Unitization ℂ A))
        (_hE : IsClosed (E : Set (Unitization ℂ A)))
        (e : Unitization ℂ D ≃⋆ₐ[ℂ] E) (r : E →⋆ₐ[ℂ] B),
      Function.Surjective r ∧
      E.subtype.comp e.toStarAlgHom =
        Unitization.starMap (NonUnitalStarSubalgebraClass.subtype D) ∧
      r.comp e.toStarAlgHom = Unitization.starLift q ∧
      ∀ d : D, r (e (Unitization.inr d)) = q d := by
  obtain ⟨E, hE, e, he⟩ := D.exists_unitization_range_equiv
  let r : E →⋆ₐ[ℂ] B := (Unitization.starLift q).comp e.symm.toStarAlgHom
  have hinr (d : D) : Unitization.starLift q (Unitization.inr d) = q d := by
    simpa only [Unitization.starLift_symm_apply_apply] using
      congrArg (fun f : D →⋆ₙₐ[ℂ] B => f d)
        (Unitization.starLift.symm_apply_apply q)
  have hcomp : r.comp e.toStarAlgHom = Unitization.starLift q := by
    apply StarAlgHom.ext
    intro z
    change Unitization.starLift q (e.symm (e z)) = Unitization.starLift q z
    rw [e.symm_apply_apply]
  have hdiag (d : D) : r (e (Unitization.inr d)) = q d := by
    change Unitization.starLift q (e.symm (e (Unitization.inr d))) = q d
    rw [e.symm_apply_apply, hinr]
  have hr : Function.Surjective r := by
    intro b
    obtain ⟨d, hd⟩ := hq b
    exact ⟨e (Unitization.inr d), (hdiag d).trans hd⟩
  exact ⟨E, hE, e, r, hr, he, hcomp, hdiag⟩

end NonUnitalStarSubalgebra
