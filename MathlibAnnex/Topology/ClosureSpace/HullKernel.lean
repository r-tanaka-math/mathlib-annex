/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.Induced

/-!
# Hull-kernel closure for arbitrary families of sets

No linear, normed, algebraic, or ideal structure is assumed. The kernel is an
intersection of members, including the empty intersection `univ`. Excluding
`univ` from the family is precisely the condition needed for empty preservation.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace ClosureSpace
namespace HullKernel

variable {X : Type u}

/-- Intersect the members selected by a set of points of the family subtype. -/
def kernel (F : Set (Set X)) (s : Set F) : Set X :=
  {x | ∀ I : F, I ∈ s → x ∈ I.val}

/-- Select all members containing a given subset of the ambient set. -/
def hull (F : Set (Set X)) (a : Set X) : Set F := {I | a ⊆ I.val}

@[simp]
theorem mem_kernel (F : Set (Set X)) (s : Set F) (x : X) :
    x ∈ kernel F s ↔ ∀ I : F, I ∈ s → x ∈ I.val := Iff.rfl

@[simp]
theorem mem_hull (F : Set (Set X)) (a : Set X) (I : F) :
    I ∈ hull F a ↔ a ⊆ I.val := Iff.rfl

@[simp]
theorem kernel_empty (F : Set (Set X)) : kernel F ∅ = Set.univ := by
  apply Set.ext
  intro x
  simp only [mem_kernel, Set.mem_empty_iff_false, false_implies, implies_true,
    Set.mem_univ]

theorem kernel_antitone (F : Set (Set X)) {s t : Set F} (hst : s ⊆ t) :
    kernel F t ⊆ kernel F s := fun _ hx I hI => hx I (hst hI)

theorem hull_antitone (F : Set (Set X)) {a b : Set X} (hab : a ⊆ b) :
    hull F b ⊆ hull F a := fun _ hI => hab.trans hI

theorem subset_hull_kernel (F : Set (Set X)) (s : Set F) : s ⊆ hull F (kernel F s) :=
  fun I hI _ hx => hx I hI

/-- The intersection does not change on passing to the hull-kernel closure. -/
@[simp]
theorem kernel_hull_kernel (F : Set (Set X)) (s : Set F) :
    kernel F (hull F (kernel F s)) = kernel F s := by
  apply Set.Subset.antisymm (kernel_antitone F (subset_hull_kernel F s))
  intro x hx I hI
  exact hI hx

/-- The generic hull-kernel closure space. -/
def space (F : Set (Set X)) (hF : Set.univ ∉ F) : ClosureSpace F where
  toClosureOperator := ClosureOperator.mk'
    (fun s => hull F (kernel F s))
    (by
      intro s t hst
      exact hull_antitone F (kernel_antitone F hst))
    (subset_hull_kernel F)
    (by
      intro s
      rw [kernel_hull_kernel])
  map_empty' := by
    change hull F (kernel F ∅) = ∅
    rw [kernel_empty]
    apply Set.eq_empty_iff_forall_notMem.2
    intro I hI
    have hval : I.val = Set.univ := Set.Subset.antisymm (Set.subset_univ _) hI
    exact hF (hval ▸ I.property)

@[simp]
theorem space_closure (F : Set (Set X)) (hF : Set.univ ∉ F) (s : Set F) :
    (space F hF).closure s = hull F (kernel F s) := rfl

/-- Hull-kernel closure is determined exactly by the intersection of the selected members. -/
theorem closure_eq_iff_kernel_eq (F : Set (Set X)) (hF : Set.univ ∉ F)
    (s t : Set F) :
    (space F hF).closure s = (space F hF).closure t ↔ kernel F s = kernel F t := by
  constructor
  · intro h
    have hk := congrArg (kernel F) h
    simpa only [space_closure, kernel_hull_kernel] using hk
  · intro h
    change hull F (kernel F s) = hull F (kernel F t)
    rw [h]

/-- A hull-kernel space is T0, even for a completely arbitrary family of subsets. -/
theorem isT0_space (F : Set (Set X)) (hF : Set.univ ∉ F) : (space F hF).IsT0 := by
  intro I J hIJ hJI
  apply Subtype.ext
  apply Set.Subset.antisymm
  · intro x hx
    apply hJI
    intro K hK
    have hK' : K = I := Set.mem_singleton_iff.1 hK
    subst K
    exact hx
  · intro x hx
    apply hIJ
    intro K hK
    have hK' : K = J := Set.mem_singleton_iff.1 hK
    subst K
    exact hx

/-- An antichain of subsets gives a T1 hull-kernel space. -/
theorem isT1_space_of_antichain (F : Set (Set X)) (hF : Set.univ ∉ F)
    (hanti : ∀ I J : F, I.val ⊆ J.val → I = J) : (space F hF).IsT1 := by
  intro I
  apply ((space F hF).isClosed_iff_closure_subset {I}).2
  intro J hJ
  apply Set.mem_singleton_iff.2
  apply (hanti I J ?_).symm
  intro x hx
  apply hJ
  intro K hK
  have hK' : K = I := Set.mem_singleton_iff.1 hK
  subst K
  exact hx

end HullKernel
end ClosureSpace
