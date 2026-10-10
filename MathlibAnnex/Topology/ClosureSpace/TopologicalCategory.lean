/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.Category
public import MathlibAnnex.Topology.ClosureSpace.TopologicalMaps
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.EqToHom

/-!
# The isomorphism-closed full subcategory of topologizable closure spaces

The full subcategory uses Mathlib's actual `ObjectProperty.FullSubcategory`.
Its arrows have the induced-category wrapper; `.hom` and `homMk` access the
ambient arrow. No arrow is identified definitionally with its underlying function.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace ClosureCat

local instance (X Y : ClosureCat.{u}) : FunLike (X ⟶ Y) X Y := Hom.instFunLike X Y

/-- The existing finite-union-preservation property on a bundled closure space. -/
def IsTopologizable : ObjectProperty ClosureCat.{u} := fun X => X.str.IsTopologizable

instance instIsClosedUnderIsomorphismsIsTopologizable :
    (IsTopologizable : ObjectProperty ClosureCat.{u}).IsClosedUnderIsomorphisms where
  of_iso e hX := (homeomorphOfIso e).isTopologizable hX

/-- The full subcategory on exactly the topologizable closure spaces. -/
abbrev Topological : Type (u + 1) :=
  (IsTopologizable : ObjectProperty ClosureCat.{u}).FullSubcategory

namespace Topological

/-- Bundle a topologizable closure space, preserving its carrier. -/
def of (α : Type u) (c : ClosureSpace α) (hc : c.IsTopologizable) : Topological.{u} :=
  ⟨ClosureCat.of α c, hc⟩

/-- The actual full-subcategory inclusion. -/
def inclusion : Topological.{u} ⥤ ClosureCat.{u} :=
  (IsTopologizable : ObjectProperty ClosureCat.{u}).ι

/-- The inclusion is fully faithful, with every ambient arrow as its own preimage. -/
def inclusionFullyFaithful : inclusion.{u}.FullyFaithful :=
  (IsTopologizable : ObjectProperty ClosureCat.{u}).fullyFaithfulι

@[simp]
theorem inclusion_obj (X : Topological.{u}) : inclusion.obj X = X.obj := rfl

@[simp]
theorem inclusion_map {X Y : Topological.{u}} (f : X ⟶ Y) :
    inclusion.map f = f.hom := rfl

@[ext]
theorem hom_ext {X Y : Topological.{u}} {f g : X ⟶ Y}
    (h : ∀ x : X.obj, f.hom x = g.hom x) : f = g := by
  apply CategoryTheory.ObjectProperty.hom_ext
  exact ClosureCat.Hom.ext h

/-- Identity on a fixed carrier with equal closure structures, as an actual isomorphism. -/
def isoOfClosureEq (α : Type u) (c d : ClosureSpace α)
    (hc : c.IsTopologizable) (hd : d.IsTopologizable) (h : c = d) :
    of α c hc ≅ of α d hd where
  hom := CategoryTheory.ObjectProperty.homMk
    (ClosureCat.ofHom id (by cases h; exact ClosureSpace.continuous_id c))
  inv := CategoryTheory.ObjectProperty.homMk
    (ClosureCat.ofHom id (by cases h; exact ClosureSpace.continuous_id c))
  hom_inv_id := hom_ext (fun _ => rfl)
  inv_hom_id := hom_ext (fun _ => rfl)

@[simp]
theorem isoOfClosureEq_hom_apply (α : Type u) (c d : ClosureSpace α)
    (hc : c.IsTopologizable) (hd : d.IsTopologizable) (h : c = d) (x : α) :
    (isoOfClosureEq α c d hc hd h).hom.hom x = x := rfl

@[simp]
theorem isoOfClosureEq_inv_apply (α : Type u) (c d : ClosureSpace α)
    (hc : c.IsTopologizable) (hd : d.IsTopologizable) (h : c = d) (x : α) :
    (isoOfClosureEq α c d hc hd h).inv.hom x = x := rfl

/-- This identity-function isomorphism is the canonical isomorphism of equal objects. -/
theorem isoOfClosureEq_eqToIso (α : Type u) (c d : ClosureSpace α)
    (hc : c.IsTopologizable) (hd : d.IsTopologizable) (h : c = d) :
    isoOfClosureEq α c d hc hd h = eqToIso (by cases h; rfl) := by
  cases h
  apply CategoryTheory.Iso.ext
  exact hom_ext (fun _ => rfl)

end Topological
end ClosureCat
