/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.TopologicalCategory
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.CategoryTheory.Equivalence

/-!
# Topological closure spaces and TopCat

The two functors use the existing topology/closure constructions and leave
underlying functions unchanged. Both full-subcategory and TopCat arrow wrappers
are used through their public interfaces. The unit and counit are identity
functions, but are proved continuous for their actual endpoint structures.

Besides an adjoint equivalence with explicit triangle laws, this file proves
both strict inverse *equalities of functors*, using object equalities and the
identification of the components with `eqToIso`. Thus the equivalence alone is
not used as a substitute for Proposition 3.14's isomorphism of categories.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace ClosureCat
local instance (X Y : ClosureCat.{u}) : FunLike (X ⟶ Y) X Y := Hom.instFunLike X Y
namespace Topological

/-- The ordinary topology functor on the full subcategory; its arrows are the same functions. -/
def toTopCat : Topological.{u} ⥤ TopCat.{u} where
  obj X := @TopCat.of X.obj (X.obj.str.toTopologicalSpace X.property)
  map {X Y} f :=
    @TopCat.ofHom X.obj Y.obj
      (X.obj.str.toTopologicalSpace X.property) (Y.obj.str.toTopologicalSpace Y.property)
      (@ContinuousMap.mk X.obj Y.obj
        (X.obj.str.toTopologicalSpace X.property) (Y.obj.str.toTopologicalSpace Y.property)
        f.hom ((ClosureSpace.continuous_toTopologicalSpace_iff X.obj.str Y.obj.str
          X.property Y.property f.hom).mpr f.hom.continuous_toFun))
  map_id X := TopCat.ext (fun _ => rfl)
  map_comp f g := TopCat.ext (fun _ => rfl)

/-- The closure functor from TopCat into the actual topologizable full subcategory. -/
def fromTopCat : TopCat.{u} ⥤ Topological.{u} where
  obj X := of X (ClosureSpace.ofTopologicalSpace X.str)
    (ClosureSpace.isTopologizable_ofTopologicalSpace X.str)
  map {X Y} f := CategoryTheory.ObjectProperty.homMk
    (ClosureCat.ofHom f.hom
      ((ClosureSpace.continuous_ofTopologicalSpace_iff X.str Y.str f.hom).mpr
        f.hom.continuous))
  map_id X := hom_ext (fun _ => rfl)
  map_comp f g := hom_ext (fun _ => rfl)

@[simp]
theorem toTopCat_map_apply {X Y : Topological.{u}} (f : X ⟶ Y) (x : X.obj) :
    (toTopCat.map f).hom x = f.hom x := rfl

@[simp]
theorem fromTopCat_map_apply {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    (fromTopCat.map f).hom x = f.hom x := rfl

/-- The object round trip preserves the complete closure-space data. -/
@[simp]
theorem fromTopCat_obj_toTopCat_obj (X : Topological.{u}) :
    fromTopCat.obj (toTopCat.obj X) = X := by
  rcases X with ⟨⟨α, c⟩, hc⟩
  apply CategoryTheory.ObjectProperty.FullSubcategory.ext
  change ClosureCat.of α (ClosureSpace.ofTopologicalSpace (c.toTopologicalSpace hc)) =
    ClosureCat.of α c
  exact congrArg (ClosureCat.of α) (ClosureSpace.ofTopologicalSpace_toTopologicalSpace c hc)

/-- The object round trip preserves the complete ordinary topology. -/
@[simp]
theorem toTopCat_obj_fromTopCat_obj (X : TopCat.{u}) :
    toTopCat.obj (fromTopCat.obj X) = X := by
  exact congrArg (fun r : TopologicalSpace X => @TopCat.of X r)
    (ClosureSpace.toTopologicalSpace_ofTopologicalSpace X.str)

/-- The unit component is identity on the underlying carrier, not an arbitrary choice. -/
def unitComponent (X : Topological.{u}) : X ≅ fromTopCat.obj (toTopCat.obj X) :=
  isoOfClosureEq X.obj X.obj.str
    (ClosureSpace.ofTopologicalSpace (X.obj.str.toTopologicalSpace X.property))
    X.property (ClosureSpace.isTopologizable_ofTopologicalSpace _)
    (ClosureSpace.ofTopologicalSpace_toTopologicalSpace X.obj.str X.property).symm

@[simp]
theorem unitComponent_hom_apply (X : Topological.{u}) (x : X.obj) :
    (unitComponent X).hom.hom x = x := rfl

@[simp]
theorem unitComponent_inv_apply (X : Topological.{u}) (x : X.obj) :
    (unitComponent X).inv.hom x = x := rfl

/-- The unit is the canonical isomorphism associated to the proved object equality. -/
theorem unitComponent_eqToIso (X : Topological.{u}) :
    unitComponent X = eqToIso (fromTopCat_obj_toTopCat_obj X).symm := by
  exact isoOfClosureEq_eqToIso X.obj X.obj.str
    (ClosureSpace.ofTopologicalSpace (X.obj.str.toTopologicalSpace X.property))
    X.property (ClosureSpace.isTopologizable_ofTopologicalSpace _)
    (ClosureSpace.ofTopologicalSpace_toTopologicalSpace X.obj.str X.property).symm

/-- Identity on a fixed carrier with equal topologies, using the public TopCat arrow constructor. -/
def isoOfTopologyEq (α : Type u) (t r : TopologicalSpace α) (h : t = r) :
    @TopCat.of α t ≅ @TopCat.of α r where
  hom := @TopCat.ofHom α α t r
    (@ContinuousMap.mk α α t r id (by subst r; exact @continuous_id α t))
  inv := @TopCat.ofHom α α r t
    (@ContinuousMap.mk α α r t id (by subst r; exact @continuous_id α t))
  hom_inv_id := TopCat.ext (fun _ => rfl)
  inv_hom_id := TopCat.ext (fun _ => rfl)

@[simp]
theorem isoOfTopologyEq_hom_apply (α : Type u) (t r : TopologicalSpace α)
    (h : t = r) (x : α) : (isoOfTopologyEq α t r h).hom.hom x = x := rfl

@[simp]
theorem isoOfTopologyEq_inv_apply (α : Type u) (t r : TopologicalSpace α)
    (h : t = r) (x : α) : (isoOfTopologyEq α t r h).inv.hom x = x := rfl

theorem isoOfTopologyEq_eqToIso (α : Type u) (t r : TopologicalSpace α) (h : t = r) :
    isoOfTopologyEq α t r h =
      eqToIso (congrArg (fun s : TopologicalSpace α => @TopCat.of α s) h) := by
  cases h
  apply CategoryTheory.Iso.ext
  exact TopCat.ext (fun _ => rfl)

/-- The counit component is identity on the underlying carrier with the reconstructed topology. -/
def counitComponent (X : TopCat.{u}) : toTopCat.obj (fromTopCat.obj X) ≅ X :=
  isoOfTopologyEq X
    ((ClosureSpace.ofTopologicalSpace X.str).toTopologicalSpace
      (ClosureSpace.isTopologizable_ofTopologicalSpace X.str))
    X.str (ClosureSpace.toTopologicalSpace_ofTopologicalSpace X.str)

@[simp]
theorem counitComponent_hom_apply (X : TopCat.{u}) (x : X) :
    (counitComponent X).hom.hom x = x := rfl

@[simp]
theorem counitComponent_inv_apply (X : TopCat.{u}) (x : X) :
    (counitComponent X).inv.hom x = x := rfl

/-- The counit agrees with transport along the exact topology round-trip equality. -/
theorem counitComponent_eqToIso (X : TopCat.{u}) :
    counitComponent X = eqToIso (toTopCat_obj_fromTopCat_obj X) := by
  exact isoOfTopologyEq_eqToIso X
    ((ClosureSpace.ofTopologicalSpace X.str).toTopologicalSpace
      (ClosureSpace.isTopologizable_ofTopologicalSpace X.str))
    X.str (ClosureSpace.toTopologicalSpace_ofTopologicalSpace X.str)

/-- Naturality of the unit, proved as equality of the actual underlying functions. -/
theorem unitComponent_naturality {X Y : Topological.{u}} (f : X ⟶ Y) :
    f ≫ (unitComponent Y).hom =
      (unitComponent X).hom ≫ fromTopCat.map (toTopCat.map f) :=
  hom_ext (fun _ => rfl)

/-- Naturality of the counit, with both TopCat wrappers retained. -/
theorem counitComponent_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) :
    toTopCat.map (fromTopCat.map f) ≫ (counitComponent Y).hom =
      (counitComponent X).hom ≫ f :=
  TopCat.ext (fun _ => rfl)

/-- The natural unit; its inverse is also natural by `NatIso.ofComponents`. -/
def unitIso : 𝟭 Topological.{u} ≅ toTopCat ⋙ fromTopCat :=
  NatIso.ofComponents unitComponent (fun f => unitComponent_naturality f)

/-- The natural counit, with inverse naturality supplied by the same public constructor. -/
def counitIso : fromTopCat ⋙ toTopCat ≅ 𝟭 TopCat.{u} :=
  NatIso.ofComponents counitComponent (fun f => counitComponent_naturality f)

/-- The forward triangle is an equality of TopCat arrows, not just of objects. -/
theorem toTopCat_unitIso_comp (X : Topological.{u}) :
    toTopCat.map (unitIso.hom.app X) ≫ counitIso.hom.app (toTopCat.obj X) =
      𝟙 (toTopCat.obj X) := TopCat.ext (fun _ => rfl)

/-- The reverse triangle is also proved directly on underlying functions. -/
theorem unitIso_fromTopCat_comp (X : TopCat.{u}) :
    unitIso.hom.app (fromTopCat.obj X) ≫ fromTopCat.map (counitIso.hom.app X) =
      𝟙 (fromTopCat.obj X) := hom_ext (fun _ => rfl)

/-- The explicit adjoint equivalence between topological closure spaces and TopCat. -/
def equivalenceTopCat : Topological.{u} ≌ TopCat.{u} where
  functor := toTopCat
  inverse := fromTopCat
  unitIso := unitIso
  counitIso := counitIso
  functor_unitIso_comp := toTopCat_unitIso_comp

/-- A strict inverse equality of functors, stronger than a natural isomorphism. -/
theorem toTopCat_comp_fromTopCat : toTopCat.{u} ⋙ fromTopCat = 𝟭 Topological.{u} := by
  refine CategoryTheory.Functor.ext_of_iso unitIso.symm fromTopCat_obj_toTopCat_obj ?_
  intro X
  change (unitComponent X).inv = eqToHom (fromTopCat_obj_toTopCat_obj X)
  rw [unitComponent_eqToIso]
  rfl

/-- The other strict inverse equality of functors. -/
theorem fromTopCat_comp_toTopCat : fromTopCat.{u} ⋙ toTopCat = 𝟭 TopCat.{u} := by
  refine CategoryTheory.Functor.ext_of_iso counitIso toTopCat_obj_fromTopCat_obj ?_
  intro X
  change (counitComponent X).hom = eqToHom (toTopCat_obj_fromTopCat_obj X)
  rw [counitComponent_eqToIso]
  rfl

/-- After canonical endpoint transport, the arrow round trip is exactly the original arrow. -/
theorem fromTopCat_map_toTopCat_map {X Y : Topological.{u}} (f : X ⟶ Y) :
    fromTopCat.map (toTopCat.map f) =
      (unitComponent X).inv ≫ f ≫ (unitComponent Y).hom :=
  hom_ext (fun _ => rfl)

/-- The same arrow-level statement in TopCat, not a defeq identification with ContinuousMap. -/
theorem toTopCat_map_fromTopCat_map {X Y : TopCat.{u}} (f : X ⟶ Y) :
    toTopCat.map (fromTopCat.map f) =
      (counitComponent X).hom ≫ f ≫ (counitComponent Y).inv :=
  TopCat.ext (fun _ => rfl)

end Topological
end ClosureCat
