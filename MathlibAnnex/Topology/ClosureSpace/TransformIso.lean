/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.Category
public import MathlibAnnex.Topology.ClosureSpace.TransformMap

/-!
# G/P transforms on categorical isomorphisms

This is the bounded categorical interface for the already constructed transforms.
Only isomorphisms are transported. It does not assert that arbitrary continuous
functions induce G/P arrows. The latter would require hypotheses not available
from ordinary closure continuity alone. No separation hypothesis is imposed here.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace ClosureCat

local instance instFunLikeHomTransformIso (X Y : ClosureCat.{u}) : FunLike (X ⟶ Y) X Y := Hom.instFunLike X Y

/-- The existing G-transform, bundled as a closure-category object. -/
def gTransform (X : ClosureCat.{u}) : ClosureCat.{u} :=
  of X.str.GPoint X.str.gTransform

/-- The existing P-transform, bundled as a closure-category object. -/
def pTransform (X : ClosureCat.{u}) : ClosureCat.{u} :=
  of X.str.PPoint X.str.pTransform

/-- The actual continuous component-closure map between the two transforms. -/
def deltaHom (X : ClosureCat.{u}) : gTransform X ⟶ pTransform X :=
  ofHom X.str.delta X.str.continuous_delta

@[simp]
theorem deltaHom_apply (X : ClosureCat.{u}) (q : X.str.GPoint) :
    deltaHom X q = X.str.delta q := rfl

/-- Transport of G along an isomorphism, using the existing quotient map. -/
def gIso {X Y : ClosureCat.{u}} (e : X ≅ Y) : gTransform X ≅ gTransform Y :=
  isoOfHomeomorph (homeomorphOfIso e).gHomeomorph

/-- Transport of P along an isomorphism, using the existing image-of-sets map. -/
def pIso {X Y : ClosureCat.{u}} (e : X ≅ Y) : pTransform X ≅ pTransform Y :=
  isoOfHomeomorph (homeomorphOfIso e).pHomeomorph

@[simp]
theorem gIso_hom_toGPoint {X Y : ClosureCat.{u}} (e : X ≅ Y) (x : X) :
    (gIso e).hom (X.str.toGPoint x) = Y.str.toGPoint (e.hom x) := rfl

@[simp]
theorem pIso_hom_val {X Y : ClosureCat.{u}} (e : X ≅ Y) (p : X.str.PPoint) :
    ((pIso e).hom p).val = e.hom '' p.val := rfl

/-- G transport preserves the identity isomorphism. -/
@[simp]
theorem gIso_refl (X : ClosureCat.{u}) :
    gIso (CategoryTheory.Iso.refl X) = CategoryTheory.Iso.refl (gTransform X) := by
  apply CategoryTheory.Iso.ext
  apply Hom.ext
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  rfl

/-- P transport preserves the identity isomorphism. -/
@[simp]
theorem pIso_refl (X : ClosureCat.{u}) :
    pIso (CategoryTheory.Iso.refl X) = CategoryTheory.Iso.refl (pTransform X) := by
  apply CategoryTheory.Iso.ext
  apply Hom.ext
  intro p
  apply Subtype.ext
  change id '' p.val = p.val
  simp only [Set.image_id]

/-- G transport preserves composition, checked on actual quotient representatives. -/
theorem gIso_trans {X Y Z : ClosureCat.{u}} (e : X ≅ Y) (f : Y ≅ Z) :
    gIso (e ≪≫ f) = gIso e ≪≫ gIso f := by
  apply CategoryTheory.Iso.ext
  apply Hom.ext
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  rfl

/-- P transport preserves composition, checked on the actual image sets. -/
theorem pIso_trans {X Y Z : ClosureCat.{u}} (e : X ≅ Y) (f : Y ≅ Z) :
    pIso (e ≪≫ f) = pIso e ≪≫ pIso f := by
  apply CategoryTheory.Iso.ext
  apply Hom.ext
  intro p
  apply Subtype.ext
  change (f.hom ∘ e.hom) '' p.val = f.hom '' (e.hom '' p.val)
  simp only [Set.image_image, Function.comp_def]

/-- The existing delta square is an equality of actual closure-category arrows. -/
theorem gIso_hom_deltaHom {X Y : ClosureCat.{u}} (e : X ≅ Y) :
    (gIso e).hom ≫ deltaHom Y = deltaHom X ≫ (pIso e).hom := by
  apply Hom.ext
  intro q
  exact (homeomorphOfIso e).delta_gMap q

end ClosureCat
