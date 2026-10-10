/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.ComponentQuotient
public import MathlibAnnex.Topology.ClosureSpace.HullKernel

/-!
# Intersections of components in a hull-kernel space

For a family of proper subsets of an arbitrary set, intersect the members of
one component. These intersections are themselves actual subsets of the
ambient set. No submodule, ideal or other algebraic structure is assumed.

The component-closure and intersection representations are different types;
the equivalence below uses intersection in one direction and hull in the other.
Empty indexed intersections retain their ordinary value `univ`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace ClosureSpace
namespace HullKernel

variable {X : Type u} (F : Set (Set X)) (hF : Set.univ ∉ F)

/-- Intersect the members of the component of a hull-kernel point. -/
def componentKernel (I : F) : Set X := kernel F ((space F hF).component I)

/-- Closing a selection of members does not change their intersection. -/
@[simp]
theorem kernel_space_closure (S : Set F) :
    kernel F ((space F hF).closure S) = kernel F S := kernel_hull_kernel F S

theorem componentKernel_subset (I : F) : componentKernel F hF I ⊆ I.val :=
  fun _ hx => hx I ((space F hF).mem_component I)

theorem componentKernel_ne_univ (I : F) : componentKernel F hF I ≠ Set.univ := by
  intro h
  have hI : I.val = Set.univ := Set.Subset.antisymm (Set.subset_univ _) (by
    rw [← h]
    exact componentKernel_subset F hF I)
  exact hF (hI ▸ I.property)

theorem componentKernel_eq_of_related {I J : F} (h : (space F hF).Related I J) :
    componentKernel F hF I = componentKernel F hF J :=
  congrArg (kernel F) ((space F hF).component_eq_of_related h)

/-- The closure of a component is the hull of its intersection. -/
theorem componentClosure_eq_hull_componentKernel (I : F) :
    (space F hF).componentClosure I = hull F (componentKernel F hF I) := rfl

@[simp]
theorem kernel_componentClosure (I : F) :
    kernel F ((space F hF).componentClosure I) = componentKernel F hF I :=
  kernel_hull_kernel F ((space F hF).component I)

/-- Equality of component closures is exactly equality of their intersections. -/
theorem componentClosure_eq_iff_componentKernel_eq (I J : F) :
    (space F hF).componentClosure I = (space F hF).componentClosure J ↔
      componentKernel F hF I = componentKernel F hF J :=
  closure_eq_iff_kernel_eq F hF ((space F hF).component I) ((space F hF).component J)

/-- The family of component intersections. Repeated subsets give one member. -/
def componentKernelFamily : Set (Set X) := Set.range (componentKernel F hF)

/-- Points of the component-intersection family, as subsets of the ambient set. -/
abbrev ComponentKernelPoint : Type u := {J : Set X // J ∈ componentKernelFamily F hF}

/-- Send an original family member to its component intersection. -/
def toComponentKernelPoint (I : F) : ComponentKernelPoint F hF :=
  ⟨componentKernel F hF I, ⟨I, rfl⟩⟩

theorem toComponentKernelPoint_surjective :
    Function.Surjective (toComponentKernelPoint F hF) := by
  rintro ⟨J, I, rfl⟩
  exact ⟨I, rfl⟩

theorem univ_notMem_componentKernelFamily : Set.univ ∉ componentKernelFamily F hF := by
  rintro ⟨I, hI⟩
  exact componentKernel_ne_univ F hF I hI

/-- Hull-kernel closure on the component-intersection family. -/
def componentKernelClosure : ClosureSpace (ComponentKernelPoint F hF) :=
  space (componentKernelFamily F hF) (univ_notMem_componentKernelFamily F hF)

/-- Intersect the carrier of a P-point. -/
def pPointToComponentKernelPoint (p : (space F hF).PPoint) : ComponentKernelPoint F hF :=
  ⟨kernel F p.val, by
    obtain ⟨I, hI⟩ := p.property
    exact ⟨I, (kernel_componentClosure F hF I).symm.trans (congrArg (kernel F) hI)⟩⟩

/-- Recover the closed component as the hull of its intersection. -/
def componentKernelPointToPPoint (J : ComponentKernelPoint F hF) : (space F hF).PPoint :=
  ⟨hull F J.val, by
    obtain ⟨I, hI⟩ := J.property
    exact ⟨I, (componentClosure_eq_hull_componentKernel F hF I).trans
      (congrArg (hull F) hI)⟩⟩

/-- The intersection/hull equivalence; both inverse laws are actual set equalities. -/
def pPointEquivComponentKernelPoint : (space F hF).PPoint ≃ ComponentKernelPoint F hF where
  toFun := pPointToComponentKernelPoint F hF
  invFun := componentKernelPointToPPoint F hF
  left_inv p := by
    apply Subtype.ext
    change (space F hF).closure p.val = p.val
    exact ((space F hF).isClosed_iff p.val).mp ((space F hF).isClosed_pPoint p)
  right_inv J := by
    apply Subtype.ext
    change kernel F (hull F J.val) = J.val
    obtain ⟨I, hI⟩ := J.property
    rw [← hI]
    exact kernel_hull_kernel F ((space F hF).component I)

@[simp]
theorem pPointEquivComponentKernelPoint_toPPoint (I : F) :
    pPointEquivComponentKernelPoint F hF ((space F hF).toPPoint I) =
      toComponentKernelPoint F hF I := Subtype.ext (kernel_componentClosure F hF I)

/-- The kernel of a selected family of component intersections equals the
kernel of all original members whose component intersection was selected. -/
theorem kernel_componentKernelFamily (T : Set (ComponentKernelPoint F hF)) :
    kernel (componentKernelFamily F hF) T =
      kernel F (toComponentKernelPoint F hF ⁻¹' T) := by
  apply Set.ext
  intro x
  constructor
  · intro hx I hI
    exact componentKernel_subset F hF I (hx (toComponentKernelPoint F hF I) hI)
  · intro hx J hJ
    obtain ⟨I, hI⟩ := J.property
    change x ∈ J.val
    rw [← hI]
    intro I' hI'
    apply hx I'
    have heq : toComponentKernelPoint F hF I' = J := by
      apply Subtype.ext
      exact (componentKernel_eq_of_related F hF hI').symm.trans hI
    change toComponentKernelPoint F hF I' ∈ T
    rw [heq]
    exact hJ

/-- Membership in the new hull-kernel closure expressed in the original space.
This is the component-intersection criterion, before any G/P identification. -/
theorem mem_componentKernelClosure_iff (I : F) (T : Set (ComponentKernelPoint F hF)) :
    toComponentKernelPoint F hF I ∈ (componentKernelClosure F hF).closure T ↔
      (space F hF).componentClosure I ⊆
        (space F hF).closure (toComponentKernelPoint F hF ⁻¹' T) := by
  change (kernel (componentKernelFamily F hF) T ⊆ componentKernel F hF I) ↔ _
  rw [kernel_componentKernelFamily F hF T]
  constructor
  · intro h
    exact hull_antitone F h
  · intro h
    have hk := kernel_antitone F h
    simpa only [componentKernel, componentClosure, space_closure, kernel_hull_kernel] using hk

end HullKernel
end ClosureSpace
