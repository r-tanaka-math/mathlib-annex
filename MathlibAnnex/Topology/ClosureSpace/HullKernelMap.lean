/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.HullKernel

/-!
# Transport of hull-kernel spaces

A pair of equivalences preserving incidence between points and sets transports
hull-kernel closure. Closure preservation is proved, not included in the input.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace ClosureSpace
namespace HullKernel

variable {X : Type u} {Y : Type v} {F : Set (Set X)} {G : Set (Set Y)}

/-- Incidence-preserving equivalences transport intersections of selected members. -/
theorem image_kernel (e : X ≃ Y) (φ : F ≃ G)
    (hmem : ∀ (I : F) (x : X), e x ∈ (φ I).val ↔ x ∈ I.val) (S : Set F) :
    e '' kernel F S = kernel G (φ '' S) := by
  apply Set.ext
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rintro J ⟨I, hI, rfl⟩
    exact (hmem I x).2 (hx I hI)
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    intro I hI
    apply (hmem I (e.symm y)).1
    simpa only [Equiv.apply_symm_apply] using hy (φ I) ⟨I, hI, rfl⟩

/-- Incidence-preserving equivalences commute with hull-kernel closure. -/
theorem image_closure (hF : Set.univ ∉ F) (hG : Set.univ ∉ G)
    (e : X ≃ Y) (φ : F ≃ G)
    (hmem : ∀ (I : F) (x : X), e x ∈ (φ I).val ↔ x ∈ I.val) (S : Set F) :
    φ '' (space F hF).closure S = (space G hG).closure (φ '' S) := by
  apply Set.ext
  intro J
  constructor
  · rintro ⟨I, hI, rfl⟩
    intro y hy
    have hy' : y ∈ e '' kernel F S := by
      rw [image_kernel e φ hmem]
      exact hy
    rcases hy' with ⟨x, hx, rfl⟩
    exact (hmem I x).2 (hI hx)
  · intro hJ
    refine ⟨φ.symm J, ?_, φ.apply_symm_apply J⟩
    intro x hx
    apply (hmem (φ.symm J) x).1
    have hx' : e x ∈ kernel G (φ '' S) := by
      rw [← image_kernel e φ hmem]
      exact ⟨x, hx, rfl⟩
    simpa only [Equiv.apply_symm_apply] using hJ hx'

/-- The induced homeomorphism of arbitrary hull-kernel families. -/
def homeomorphOfMemIff (hF : Set.univ ∉ F) (hG : Set.univ ∉ G)
    (e : X ≃ Y) (φ : F ≃ G)
    (hmem : ∀ (I : F) (x : X), e x ∈ (φ I).val ↔ x ∈ I.val) :
    Homeomorph (space F hF) (space G hG) :=
  Homeomorph.ofImageClosure _ _ φ (image_closure hF hG e φ hmem)

end HullKernel
end ClosureSpace
