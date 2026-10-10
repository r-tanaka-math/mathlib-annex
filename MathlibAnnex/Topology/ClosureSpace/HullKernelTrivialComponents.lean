/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.HullKernelTransforms
public import MathlibAnnex.Topology.ClosureSpace.ComponentSubspace
public import MathlibAnnex.Topology.ClosureSpace.Topological

/-!
# Hull-kernel spectra when all components are singletons

The hypothesis is triviality of the component relation. Finite-union
preservation together with T1 is a sufficient condition, not a necessary
condition. No implication from T1 alone to topologizability is asserted.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace ClosureSpace

variable {X : Type u}

/-- A trivial component relation gives actual singleton component sets. -/
theorem component_eq_singleton (c : ClosureSpace X)
    (h : ∀ x y : X, c.Related x y ↔ x = y) (x : X) : c.component x = {x} := by
  apply Set.ext
  intro y
  change c.Related x y ↔ y = x
  exact (h x y).trans eq_comm

/-- Finite-union preservation and singleton closedness force trivial components. -/
theorem IsTopologizable.related_iff_eq {c : ClosureSpace X} (hc : c.IsTopologizable)
    (hT1 : c.IsT1) (x y : X) : c.Related x y ↔ x = y := by
  have hp : ∀ a b : X, a ≠ b → c.IsClosed {a, b} := by
    intro a b _
    have heq : ({a} ∪ {b} : Set X) = {a, b} := by
      ext z
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
    rw [← heq]
    exact hc.isClosed_union (hT1 a) (hT1 b)
  exact (c.forall_related_iff_eq_iff).mpr hp x y

namespace HullKernel

variable (F : Set (Set X)) (hF : Set.univ ∉ F)

/-- Intersecting a singleton family gives that member itself. -/
@[simp]
theorem kernel_singleton (I : F) : kernel F {I} = I.val := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    exact hx I (Set.mem_singleton I)
  · intro hx J hJ
    have hJI : J = I := Set.mem_singleton_iff.mp hJ
    exact hJI.symm ▸ hx

/-- With trivial components, every component intersection is the original member. -/
theorem componentKernel_eq_of_forall_related_iff_eq
    (h : ∀ I J : F, (space F hF).Related I J ↔ I = J) (I : F) :
    componentKernel F hF I = I.val := by
  change kernel F ((space F hF).component I) = I.val
  rw [(space F hF).component_eq_singleton h I, kernel_singleton]

theorem toComponentKernelPoint_injective_of_forall_related_iff_eq
    (h : ∀ I J : F, (space F hF).Related I J ↔ I = J) :
    Function.Injective (toComponentKernelPoint F hF) := by
  intro I J hIJ
  apply Subtype.ext
  have hv := congrArg Subtype.val hIJ
  change componentKernel F hF I = componentKernel F hF J at hv
  simpa only [componentKernel_eq_of_forall_related_iff_eq F hF h] using hv

/-- The two families of ambient subsets coincide when components are singletons. -/
theorem componentKernelFamily_eq_of_forall_related_iff_eq
    (h : ∀ I J : F, (space F hF).Related I J ↔ I = J) :
    componentKernelFamily F hF = F := by
  apply Set.ext
  intro J
  constructor
  · rintro ⟨I, hI⟩
    rw [componentKernel_eq_of_forall_related_iff_eq F hF h I] at hI
    exact hI ▸ I.property
  · intro hJ
    exact ⟨⟨J, hJ⟩, componentKernel_eq_of_forall_related_iff_eq F hF h ⟨J, hJ⟩⟩

/-- The original closure formula is preserved by the component-kernel map. -/
theorem image_toComponentKernelPoint_closure_of_forall_related_iff_eq
    (h : ∀ I J : F, (space F hF).Related I J ↔ I = J) (S : Set F) :
    toComponentKernelPoint F hF '' (space F hF).closure S =
      (componentKernelClosure F hF).closure (toComponentKernelPoint F hF '' S) := by
  have hk : kernel (componentKernelFamily F hF) (toComponentKernelPoint F hF '' S) =
      kernel F S := by
    apply Set.ext
    intro x
    constructor
    · intro hx I hI
      have hxI := hx (toComponentKernelPoint F hF I) ⟨I, hI, rfl⟩
      change x ∈ componentKernel F hF I at hxI
      rwa [componentKernel_eq_of_forall_related_iff_eq F hF h I] at hxI
    · intro hx J hJ
      obtain ⟨I, hI, rfl⟩ := hJ
      change x ∈ componentKernel F hF I
      rw [componentKernel_eq_of_forall_related_iff_eq F hF h I]
      exact hx I hI
  have hm (I : F) : toComponentKernelPoint F hF I ∈
      (componentKernelClosure F hF).closure (toComponentKernelPoint F hF '' S) ↔
        I ∈ (space F hF).closure S := by
    change kernel (componentKernelFamily F hF) (toComponentKernelPoint F hF '' S) ⊆
      componentKernel F hF I ↔ kernel F S ⊆ I.val
    rw [hk, componentKernel_eq_of_forall_related_iff_eq F hF h I]
  apply Set.ext
  intro J
  constructor
  · rintro ⟨I, hI, rfl⟩
    exact (hm I).mpr hI
  · intro hJ
    obtain ⟨I, rfl⟩ := toComponentKernelPoint_surjective F hF J
    exact ⟨I, (hm I).mp hJ, rfl⟩

/-- The original hull-kernel space is homeomorphic to its component-intersection spectrum. -/
noncomputable def homeomorphComponentKernelPointOfRelatedEq
    (h : ∀ I J : F, (space F hF).Related I J ↔ I = J) :
    Homeomorph (space F hF) (componentKernelClosure F hF) :=
  Homeomorph.ofImageClosure _ _
    (Equiv.ofBijective (toComponentKernelPoint F hF)
      ⟨toComponentKernelPoint_injective_of_forall_related_iff_eq F hF h,
        toComponentKernelPoint_surjective F hF⟩)
    (image_toComponentKernelPoint_closure_of_forall_related_iff_eq F hF h)

theorem componentPointToComponentKernelPoint_bijective_of_forall_related_iff_eq
    (h : ∀ I J : F, (space F hF).Related I J ↔ I = J) :
    Function.Bijective (componentPointToComponentKernelPoint F hF) := by
  refine ⟨?_, componentPointToComponentKernelPoint_surjective F hF⟩
  rintro ⟨C, I, rfl⟩ ⟨D, J, rfl⟩ hIJ
  have heq : I = J := toComponentKernelPoint_injective_of_forall_related_iff_eq F hF h hIJ
  cases heq
  rfl

/-- Gamma becomes a homeomorphism under the additional trivial-component hypothesis. -/
noncomputable def componentPointHomeomorphComponentKernelPointOfRelatedEq
    (h : ∀ I J : F, (space F hF).Related I J ↔ I = J) :
    Homeomorph (componentPointClosure F hF) (componentKernelClosure F hF) :=
  homeomorphInduced _ (Equiv.ofBijective (componentPointToComponentKernelPoint F hF)
    (componentPointToComponentKernelPoint_bijective_of_forall_related_iff_eq F hF h))

end HullKernel
end ClosureSpace
