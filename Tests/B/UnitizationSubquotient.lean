/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Typed consumers of the production results.
-/

import Mathlib.Analysis.CStarAlgebra.Hom
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.UnitizationSubquotient

set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra

universe u v w

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {B : Type v} [CStarAlgebra B]

example (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)] :
    ∃ (E : StarSubalgebra ℂ (Unitization ℂ A))
        (_hE : IsClosed (E : Set (Unitization ℂ A)))
        (e : Unitization ℂ D ≃⋆ₐ[ℂ] E),
      E.subtype.comp e.toStarAlgHom =
        Unitization.starMap (NonUnitalStarSubalgebraClass.subtype D) :=
  D.exists_unitization_range_equiv

example (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (q : D →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q) :
    ∃ (E : StarSubalgebra ℂ (Unitization ℂ A))
        (_hE : IsClosed (E : Set (Unitization ℂ A)))
        (e : Unitization ℂ D ≃⋆ₐ[ℂ] E) (r : E →⋆ₐ[ℂ] B),
      Function.Surjective r ∧
      E.subtype.comp e.toStarAlgHom =
        Unitization.starMap (NonUnitalStarSubalgebraClass.subtype D) ∧
      r.comp e.toStarAlgHom = Unitization.starLift q ∧
      ∀ d : D, r (e (Unitization.inr d)) = q d :=
  D.exists_unitization_subquotient q hq

-- Both actual maps have the expected value on every original element.
example (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (q : D →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q) :
    ∃ (E : StarSubalgebra ℂ (Unitization ℂ A))
        (_hE : IsClosed (E : Set (Unitization ℂ A)))
        (e : Unitization ℂ D ≃⋆ₐ[ℂ] E) (r : E →⋆ₐ[ℂ] B),
      Function.Surjective r ∧
      ∀ d : D, (e (Unitization.inr d) : Unitization ℂ A) = Unitization.inr (d : A) ∧
        r (e (Unitization.inr d)) = q d := by
  obtain ⟨E, hE, e, r, hr, he, _hcomp, hdiag⟩ :=
    D.exists_unitization_subquotient q hq
  refine ⟨E, hE, e, r, hr, ?_⟩
  intro d
  refine ⟨?_, hdiag d⟩
  have h := congrArg
    (fun f : Unitization ℂ D →⋆ₐ[ℂ] Unitization ℂ A => f (Unitization.inr d)) he
  change (e (Unitization.inr d) : Unitization ℂ A) =
    Unitization.starMap (NonUnitalStarSubalgebraClass.subtype D) (Unitization.inr d) at h
  simpa only [Unitization.starMap_inr, NonUnitalStarSubalgebraClass.subtype_apply] using h

-- The existing C-star isometry theorem preserves the actual unitization norm.
example (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)] :
    ∃ (E : StarSubalgebra ℂ (Unitization ℂ A))
        (_hE : IsClosed (E : Set (Unitization ℂ A)))
        (e : Unitization ℂ D ≃⋆ₐ[ℂ] E),
      ∀ z : Unitization ℂ D, ‖e z‖ = ‖z‖ := by
  obtain ⟨E, hE, e, _he⟩ := D.exists_unitization_range_equiv
  letI : IsClosed (E : Set (Unitization ℂ A)) := hE
  exact ⟨E, hE, e, fun z => NonUnitalStarAlgHom.norm_map e e.injective z⟩

-- A representation precomposed with the actual onto map has the same image.
example (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (q : D →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q)
    {C : Type w} [CStarAlgebra C] (pi : B →⋆ₐ[ℂ] C) :
    ∃ (E : StarSubalgebra ℂ (Unitization ℂ A))
        (_hE : IsClosed (E : Set (Unitization ℂ A)))
        (r : E →⋆ₐ[ℂ] B),
      Function.Surjective r ∧ (pi.comp r).range = pi.range := by
  obtain ⟨E, hE, _e, r, hr, _he, _hcomp, _hdiag⟩ :=
    D.exists_unitization_subquotient q hq
  refine ⟨E, hE, r, hr, ?_⟩
  apply SetLike.coe_injective
  exact hr.range_comp pi
