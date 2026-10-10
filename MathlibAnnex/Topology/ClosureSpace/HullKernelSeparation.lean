/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.HullKernel

/-!
# Total intersections and density in hull-kernel spaces

The ambient sets need not be submodules, ideals, or closed sets of another topology.
The empty intersection is the full ambient set, without an exception in the definition.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace ClosureSpace
namespace HullKernel

variable {X : Type u}

/-- The existing kernel in ordinary indexed-intersection notation. -/
theorem kernel_eq_iInter (F : Set (Set X)) (s : Set F) :
    kernel F s = ⋂ I ∈ s, I.val := by
  apply Set.ext
  intro x
  simp only [mem_kernel, Set.mem_iInter]

/-- The total kernel is the intersection of the unbundled family. -/
theorem kernel_univ_eq_sInter (F : Set (Set X)) : kernel F Set.univ = ⋂₀ F := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    exact Set.mem_sInter.mpr (fun I hI => hx ⟨I, hI⟩ (Set.mem_univ _))
  · intro hx I _
    exact Set.mem_sInter.mp hx I.val I.property

/-- A family of points is closure-dense precisely when its kernel is the total kernel. -/
theorem closure_eq_univ_iff_kernel_eq (F : Set (Set X)) (hF : Set.univ ∉ F)
    (s : Set F) : (space F hF).closure s = Set.univ ↔
      kernel F s = kernel F Set.univ := by
  have h := closure_eq_iff_kernel_eq F hF s Set.univ
  simpa only [ClosureSpace.closure_univ] using h

end HullKernel
end ClosureSpace
