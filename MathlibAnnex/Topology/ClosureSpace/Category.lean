/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.Maps
public import Mathlib.CategoryTheory.Iso

/-!
# The category of closure spaces and continuous functions

Objects with carrier in `Type u` form `ClosureCat.{u} : Type (u + 1)`;
morphisms lie in `Type u`. Continuity is the existing full closure-continuity
predicate, not finite continuity. Composition `f ≫ g` is the function `g ∘ f`.
No ordinary topology is installed on the carrier of a general closure space.

This supplies the actual category in Definition 3.12 and the isomorphism
correspondence in Remark 3.13 of arXiv:2504.05551v1.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

/-- A type equipped with the existing, explicit closure-space structure. -/
structure ClosureCat where
  /-- The underlying type. -/
  carrier : Type u
  /-- The closure structure, without a finite-union preservation assumption. -/
  str : ClosureSpace carrier

namespace ClosureCat

instance instCoeSort : CoeSort ClosureCat.{u} (Type u) := ⟨carrier⟩

/-- Bundle a closure space without changing its underlying type. -/
def of (α : Type u) (c : ClosureSpace α) : ClosureCat.{u} := ⟨α, c⟩

/-- A morphism is a function with its actual closure-continuity proof. -/
structure Hom (X Y : ClosureCat.{u}) where
  /-- The underlying function. -/
  toFun : X → Y
  /-- Preservation of closure in the forward direction. -/
  continuous_toFun : X.str.Continuous Y.str toFun

instance Hom.instFunLike (X Y : ClosureCat.{u}) : FunLike (Hom X Y) X Y where
  coe := Hom.toFun
  coe_injective := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    cases h
    rfl

@[ext]
theorem Hom.ext {X Y : ClosureCat.{u}} {f g : Hom X Y}
    (h : ∀ x : X, f x = g x) : f = g := DFunLike.ext _ _ h

/-- Full closure-continuous functions, with the usual identity and composition. -/
instance instCategory : Category.{u} ClosureCat.{u} where
  Hom := Hom
  id X := ⟨id, ClosureSpace.continuous_id X.str⟩
  comp f g := ⟨g ∘ f, g.continuous_toFun.comp f.continuous_toFun⟩
  id_comp f := Hom.ext (fun _ => rfl)
  comp_id f := Hom.ext (fun _ => rfl)
  assoc f g h := Hom.ext (fun _ => rfl)

local instance (X Y : ClosureCat.{u}) : FunLike (X ⟶ Y) X Y :=
  Hom.instFunLike X Y

/-- The public constructor for a closure-continuous arrow. -/
def ofHom {X Y : ClosureCat.{u}} (f : X → Y) (hf : X.str.Continuous Y.str f) :
    X ⟶ Y := ⟨f, hf⟩

@[simp]
theorem ofHom_apply {X Y : ClosureCat.{u}} (f : X → Y)
    (hf : X.str.Continuous Y.str f) (x : X) : ofHom f hf x = f x := rfl

@[simp]
theorem id_apply (X : ClosureCat.{u}) (x : X) : (𝟙 X : X ⟶ X) x = x := rfl

@[simp]
theorem comp_apply {X Y Z : ClosureCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := rfl

/-- An existing closure homeomorphism supplies an actual categorical isomorphism. -/
def isoOfHomeomorph {X Y : ClosureCat.{u}} (e : ClosureSpace.Homeomorph X.str Y.str) :
    X ≅ Y where
  hom := ofHom e.toEquiv e.continuous_toFun
  inv := ofHom e.toEquiv.symm e.continuous_invFun
  hom_inv_id := Hom.ext e.toEquiv.symm_apply_apply
  inv_hom_id := Hom.ext e.toEquiv.apply_symm_apply

/-- A categorical isomorphism supplies the existing closure homeomorphism. -/
def homeomorphOfIso {X Y : ClosureCat.{u}} (e : X ≅ Y) :
    ClosureSpace.Homeomorph X.str Y.str where
  toEquiv :=
    { toFun := e.hom
      invFun := e.inv
      left_inv := fun x => by
        have h := congrArg (fun f : X ⟶ X => f x) e.hom_inv_id
        exact h
      right_inv := fun y => by
        have h := congrArg (fun f : Y ⟶ Y => f y) e.inv_hom_id
        exact h }
  continuous_toFun := e.hom.continuous_toFun
  continuous_invFun := e.inv.continuous_toFun

@[simp]
theorem isoOfHomeomorph_hom_apply {X Y : ClosureCat.{u}}
    (e : ClosureSpace.Homeomorph X.str Y.str) (x : X) :
    (isoOfHomeomorph e).hom x = e.toEquiv x := rfl

@[simp]
theorem isoOfHomeomorph_inv_apply {X Y : ClosureCat.{u}}
    (e : ClosureSpace.Homeomorph X.str Y.str) (y : Y) :
    (isoOfHomeomorph e).inv y = e.toEquiv.symm y := rfl

@[simp]
theorem homeomorphOfIso_apply {X Y : ClosureCat.{u}} (e : X ≅ Y) (x : X) :
    (homeomorphOfIso e).toEquiv x = e.hom x := rfl

@[simp]
theorem homeomorphOfIso_symm_apply {X Y : ClosureCat.{u}} (e : X ≅ Y) (y : Y) :
    (homeomorphOfIso e).toEquiv.symm y = e.inv y := rfl

@[simp]
theorem homeomorphOfIso_isoOfHomeomorph {X Y : ClosureCat.{u}}
    (e : ClosureSpace.Homeomorph X.str Y.str) :
    homeomorphOfIso (isoOfHomeomorph e) = e := by
  cases e
  rfl

@[simp]
theorem isoOfHomeomorph_homeomorphOfIso {X Y : ClosureCat.{u}} (e : X ≅ Y) :
    isoOfHomeomorph (homeomorphOfIso e) = e := by
  apply CategoryTheory.Iso.ext
  apply Hom.ext
  intro x
  rfl

/-- Homeomorphisms and categorical isomorphisms are in bijective correspondence. -/
def homeomorphEquivIso (X Y : ClosureCat.{u}) :
    ClosureSpace.Homeomorph X.str Y.str ≃ (X ≅ Y) where
  toFun := isoOfHomeomorph
  invFun := homeomorphOfIso
  left_inv := homeomorphOfIso_isoOfHomeomorph
  right_inv := isoOfHomeomorph_homeomorphOfIso

/-- The identity homeomorphism gives the identity isomorphism. -/
@[simp]
theorem isoOfHomeomorph_refl (X : ClosureCat.{u}) :
    isoOfHomeomorph (ClosureSpace.Homeomorph.refl X.str) = CategoryTheory.Iso.refl X := by
  apply CategoryTheory.Iso.ext
  apply Hom.ext
  intro x
  rfl

/-- The isomorphism correspondence respects composition, in the same order. -/
theorem isoOfHomeomorph_trans {X Y Z : ClosureCat.{u}}
    (e : ClosureSpace.Homeomorph X.str Y.str) (f : ClosureSpace.Homeomorph Y.str Z.str) :
    isoOfHomeomorph (e.trans f) = isoOfHomeomorph e ≪≫ isoOfHomeomorph f := by
  apply CategoryTheory.Iso.ext
  apply Hom.ext
  intro x
  rfl

end ClosureCat
