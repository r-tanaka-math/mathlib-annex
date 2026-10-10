/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.ComponentKernel

/-!
# Hull-kernel models for the G- and P-transforms

The P-transform's points are closed components in the original point set;
component-kernel points are intersections in the ambient set. Their bijection
preserves closure. The G-model keeps actual component subsets, and pulls back
component-kernel closure along their intersection map.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace ClosureSpace
namespace HullKernel

variable {X : Type u} (F : Set (Set X)) (hF : Set.univ ∉ F)

/-- The preimages of corresponding selections agree under the P-point equivalence. -/
theorem preimage_toComponentKernelPoint_image (T : Set (space F hF).PPoint) :
    toComponentKernelPoint F hF ⁻¹' (pPointEquivComponentKernelPoint F hF '' T) =
      (space F hF).toPPoint ⁻¹' T := by
  apply Set.ext
  intro I
  change toComponentKernelPoint F hF I ∈ (pPointEquivComponentKernelPoint F hF '' T) ↔ _
  rw [← pPointEquivComponentKernelPoint_toPPoint F hF I]
  constructor
  · rintro ⟨p, hp, heq⟩
    have heq' := (pPointEquivComponentKernelPoint F hF).injective heq
    change (space F hF).toPPoint I ∈ T
    rw [← heq']
    exact hp
  · intro hI
    exact ⟨(space F hF).toPPoint I, hI, rfl⟩

/-- Closure membership is preserved in both directions, not merely on singletons. -/
theorem pPointEquivComponentKernelPoint_mem_closure_iff
    (T : Set (space F hF).PPoint) (p : (space F hF).PPoint) :
    pPointEquivComponentKernelPoint F hF p ∈
        (componentKernelClosure F hF).closure (pPointEquivComponentKernelPoint F hF '' T) ↔
      p ∈ (space F hF).pTransform.closure T := by
  rcases p with ⟨p, I, rfl⟩
  change pPointEquivComponentKernelPoint F hF ((space F hF).toPPoint I) ∈ _ ↔
    (space F hF).componentClosure I ⊆
      (space F hF).closure ((space F hF).toPPoint ⁻¹' T)
  rw [pPointEquivComponentKernelPoint_toPPoint, mem_componentKernelClosure_iff,
    preimage_toComponentKernelPoint_image]

/-- Exact preservation of the complete P-closure formula. -/
theorem image_pPointEquivComponentKernelPoint_closure (T : Set (space F hF).PPoint) :
    pPointEquivComponentKernelPoint F hF '' (space F hF).pTransform.closure T =
      (componentKernelClosure F hF).closure (pPointEquivComponentKernelPoint F hF '' T) := by
  apply Set.ext
  intro J
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (pPointEquivComponentKernelPoint_mem_closure_iff F hF T p).mpr hp
  · intro hJ
    obtain ⟨p, rfl⟩ := (pPointEquivComponentKernelPoint F hF).surjective J
    exact ⟨p, (pPointEquivComponentKernelPoint_mem_closure_iff F hF T p).mp hJ, rfl⟩

/-- The P-transform is homeomorphic to the family of component intersections. -/
def pPointHomeomorphComponentKernelPoint :
    Homeomorph (space F hF).pTransform (componentKernelClosure F hF) :=
  Homeomorph.ofImageClosure _ _ (pPointEquivComponentKernelPoint F hF)
    (image_pPointEquivComponentKernelPoint_closure F hF)

/-- Intersect an actual component subset to obtain a component-kernel point. -/
def componentPointToComponentKernelPoint (C : (space F hF).ComponentPoint) :
    ComponentKernelPoint F hF :=
  ⟨kernel F C.val, by
    obtain ⟨I, hI⟩ := C.property
    exact ⟨I, congrArg (kernel F) hI⟩⟩

@[simp]
theorem componentPointToComponentKernelPoint_toComponentPoint (I : F) :
    componentPointToComponentKernelPoint F hF ((space F hF).toComponentPoint I) =
      toComponentKernelPoint F hF I := rfl

theorem componentPointToComponentKernelPoint_surjective :
    Function.Surjective (componentPointToComponentKernelPoint F hF) := by
  intro J
  obtain ⟨I, rfl⟩ := toComponentKernelPoint_surjective F hF J
  exact ⟨(space F hF).toComponentPoint I, rfl⟩

/-- The concrete component model of the G-transform has pullback closure. -/
def componentPointClosure : ClosureSpace (space F hF).ComponentPoint :=
  (componentKernelClosure F hF).induced (componentPointToComponentKernelPoint F hF)

/-- Commutativity of the quotient/component/intersection square. -/
theorem componentPointToComponentKernelPoint_gPointEquivComponentPoint
    (q : (space F hF).GPoint) :
    componentPointToComponentKernelPoint F hF ((space F hF).gPointEquivComponentPoint q) =
      pPointEquivComponentKernelPoint F hF ((space F hF).delta q) := by
  refine Quotient.inductionOn q ?_
  intro I
  exact (pPointEquivComponentKernelPoint_toPPoint F hF I).symm

/-- Naturality on image sets, with no injectivity claim for the intersection map. -/
theorem image_componentPointToComponentKernelPoint_gPointEquivComponentPoint
    (S : Set (space F hF).GPoint) :
    componentPointToComponentKernelPoint F hF '' ((space F hF).gPointEquivComponentPoint '' S) =
      pPointEquivComponentKernelPoint F hF '' ((space F hF).delta '' S) := by
  apply Set.ext
  intro J
  constructor
  · rintro ⟨C, ⟨q, hq, rfl⟩, hJ⟩
    exact ⟨(space F hF).delta q, ⟨q, hq, rfl⟩,
      (componentPointToComponentKernelPoint_gPointEquivComponentPoint F hF q).symm.trans hJ⟩
  · rintro ⟨p, ⟨q, hq, rfl⟩, hJ⟩
    exact ⟨(space F hF).gPointEquivComponentPoint q, ⟨q, hq, rfl⟩,
      (componentPointToComponentKernelPoint_gPointEquivComponentPoint F hF q).trans hJ⟩

/-- The G-closure comparison follows from the actual P-homeomorphism and
commuting maps, without identifying the two point types by definitional equality. -/
theorem gPointEquivComponentPoint_mem_closure_iff
    (S : Set (space F hF).GPoint) (q : (space F hF).GPoint) :
    (space F hF).gPointEquivComponentPoint q ∈
        (componentPointClosure F hF).closure ((space F hF).gPointEquivComponentPoint '' S) ↔
      q ∈ (space F hF).gTransform.closure S := by
  change componentPointToComponentKernelPoint F hF ((space F hF).gPointEquivComponentPoint q) ∈
      (componentKernelClosure F hF).closure
        (componentPointToComponentKernelPoint F hF ''
          ((space F hF).gPointEquivComponentPoint '' S)) ↔ _
  rw [componentPointToComponentKernelPoint_gPointEquivComponentPoint,
    image_componentPointToComponentKernelPoint_gPointEquivComponentPoint]
  exact pPointEquivComponentKernelPoint_mem_closure_iff F hF
    ((space F hF).delta '' S) ((space F hF).delta q)

/-- Exact preservation of G-closure under the quotient-to-subset equivalence. -/
theorem image_gPointEquivComponentPoint_closure (S : Set (space F hF).GPoint) :
    (space F hF).gPointEquivComponentPoint '' (space F hF).gTransform.closure S =
      (componentPointClosure F hF).closure ((space F hF).gPointEquivComponentPoint '' S) := by
  apply Set.ext
  intro C
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (gPointEquivComponentPoint_mem_closure_iff F hF S q).mpr hq
  · intro hC
    obtain ⟨q, rfl⟩ := (space F hF).gPointEquivComponentPoint.surjective C
    exact ⟨q, (gPointEquivComponentPoint_mem_closure_iff F hF S q).mp hC, rfl⟩

/-- The G-transform is homeomorphic to the concrete component-set model. -/
noncomputable def gPointHomeomorphComponentPoint :
    Homeomorph (space F hF).gTransform (componentPointClosure F hF) :=
  Homeomorph.ofImageClosure _ _ (space F hF).gPointEquivComponentPoint
    (image_gPointEquivComponentPoint_closure F hF)

end HullKernel
end ClosureSpace
