/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import Mathlib.Analysis.Normed.Module.Dual

/-!
# Supporting functionals and unions of kernels

The scalar field may be real or complex. The continuous dual is Mathlib's
`StrongDual`. A union of kernels is a `Set`, not a submodule or an ideal.
No nonemptiness of the supporting family is built into its definition.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The closed-dual-ball functionals taking the norm value at a vector. -/
def normingFunctionals (x : E) : Set (StrongDual 𝕜 E) :=
  {f | ‖f‖ ≤ 1 ∧ f x = (‖x‖ : 𝕜)}

@[simp]
theorem mem_normingFunctionals (x : E) (f : StrongDual 𝕜 E) :
    f ∈ normingFunctionals 𝕜 x ↔ ‖f‖ ≤ 1 ∧ f x = (‖x‖ : 𝕜) := Iff.rfl

/-- Hahn-Banach supplies norming functionals, including at zero in the zero space. -/
theorem nonempty_normingFunctionals (x : E) : (normingFunctionals 𝕜 x).Nonempty :=
  exists_dual_vector'' 𝕜 x

/-- The closed-dual-ball functionals taking value one at every point of a set. -/
def supportFunctionals (F : Set E) : Set (StrongDual 𝕜 E) :=
  {f | ‖f‖ ≤ 1 ∧ ∀ x ∈ F, f x = 1}

@[simp]
theorem mem_supportFunctionals (F : Set E) (f : StrongDual 𝕜 E) :
    f ∈ supportFunctionals 𝕜 F ↔ ‖f‖ ≤ 1 ∧ ∀ x ∈ F, f x = 1 := Iff.rfl

/-- The norm bound is exactly membership in the closed dual unit ball. -/
theorem supportFunctionals_eq_setOf_mem_closedBall (F : Set E) :
    supportFunctionals 𝕜 F =
      {f : StrongDual 𝕜 E | f ∈ Metric.closedBall 0 1 ∧ ∀ x ∈ F, f x = 1} := by
  apply Set.ext
  intro f
  simp only [mem_supportFunctionals, Set.mem_setOf_eq, mem_closedBall_zero_iff]

/-- For a nonempty set, the pointwise support condition is the paper's image equality.
Nonemptiness is essential for the converse from a constant-value condition to that equality. -/
theorem mem_supportFunctionals_iff_image_eq (F : Set E) (hF : F.Nonempty)
    (f : StrongDual 𝕜 E) :
    f ∈ supportFunctionals 𝕜 F ↔ ‖f‖ ≤ 1 ∧ (f : E → 𝕜) '' F = {1} := by
  constructor
  · intro hf
    refine ⟨hf.1, ?_⟩
    apply Set.ext
    intro a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Set.mem_singleton_iff.2 (hf.2 x hx)
    · intro ha
      obtain ⟨x, hx⟩ := hF
      exact ⟨x, hx, (hf.2 x hx).trans (Set.mem_singleton_iff.1 ha).symm⟩
  · rintro ⟨hf, himage⟩
    refine ⟨hf, ?_⟩
    intro x hx
    apply Set.mem_singleton_iff.1
    rw [← himage]
    exact ⟨x, hx, rfl⟩

/-- A supporting functional of a nonempty subset of the closed unit ball has norm one.
This does not assert existence of such a functional. -/
theorem norm_eq_one_of_mem_supportFunctionals {F : Set E} (hF : F.Nonempty)
    (hball : ∀ x ∈ F, ‖x‖ ≤ 1) {f : StrongDual 𝕜 E}
    (hf : f ∈ supportFunctionals 𝕜 F) : ‖f‖ = 1 := by
  apply le_antisymm hf.1
  obtain ⟨x, hx⟩ := hF
  calc
    1 = ‖f x‖ := by rw [hf.2 x hx, norm_one]
    _ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
    _ ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left (hball x hx) (norm_nonneg f)
    _ = ‖f‖ := mul_one _

theorem supportFunctionals_antitone {F G : Set E} (hFG : F ⊆ G) :
    supportFunctionals 𝕜 G ⊆ supportFunctionals 𝕜 F :=
  fun _ hf => ⟨hf.1, fun x hx => hf.2 x (hFG hx)⟩

/-- A unit vector is supported by at least one closed-dual-ball functional. -/
theorem nonempty_supportFunctionals_singleton (x : E) (hx : ‖x‖ = 1) :
    (supportFunctionals 𝕜 {x}).Nonempty := by
  obtain ⟨f, hf, hfx⟩ := exists_dual_vector'' 𝕜 x
  refine ⟨f, hf, ?_⟩
  intro y hy
  have hyx : y = x := Set.mem_singleton_iff.1 hy
  subst y
  simpa [hx] using hfx

/-- The set-theoretic union of the kernels of all supporting functionals. -/
def supportKernelUnion (F : Set E) : Set E :=
  {x | ∃ f ∈ supportFunctionals 𝕜 F, f x = 0}

@[simp]
theorem mem_supportKernelUnion (F : Set E) (x : E) :
    x ∈ supportKernelUnion 𝕜 F ↔ ∃ f ∈ supportFunctionals 𝕜 F, f x = 0 := Iff.rfl

/-- The defining union, written using ordinary inverse images of zero. -/
theorem supportKernelUnion_eq_iUnion (F : Set E) :
    supportKernelUnion 𝕜 F =
      ⋃ f ∈ supportFunctionals 𝕜 F, (f : E → 𝕜) ⁻¹' {0} := by
  apply Set.ext
  intro x
  simp only [mem_supportKernelUnion, Set.mem_iUnion, Set.mem_preimage,
    Set.mem_singleton_iff, exists_prop]

theorem supportKernelUnion_antitone {F G : Set E} (hFG : F ⊆ G) :
    supportKernelUnion 𝕜 G ⊆ supportKernelUnion 𝕜 F := by
  rintro x ⟨f, hf, hfx⟩
  exact ⟨f, supportFunctionals_antitone 𝕜 hFG hf, hfx⟩

/-- Every point of a nonempty supporting set lies outside the union of kernels. -/
theorem notMem_supportKernelUnion_of_mem {F : Set E} {x : E} (hx : x ∈ F) :
    x ∉ supportKernelUnion 𝕜 F := by
  rintro ⟨f, hf, hfx⟩
  exact one_ne_zero ((hf.2 x hx).symm.trans hfx)

/-- The hull-kernel admissibility condition needs no existence theorem for support. -/
theorem supportKernelUnion_ne_univ {F : Set E} (hF : F.Nonempty) :
    supportKernelUnion 𝕜 F ≠ Set.univ := by
  intro h
  obtain ⟨x, hx⟩ := hF
  apply notMem_supportKernelUnion_of_mem 𝕜 hx
  rw [h]
  exact Set.mem_univ x

/-- At zero, membership detects whether the supporting family is nonempty. -/
theorem zero_mem_supportKernelUnion_iff (F : Set E) :
    (0 : E) ∈ supportKernelUnion 𝕜 F ↔ (supportFunctionals 𝕜 F).Nonempty := by
  constructor
  · rintro ⟨f, hf, _⟩
    exact ⟨f, hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, hf, f.map_zero⟩

/-- Nonemptiness in `supportKernelUnion_ne_univ` cannot simply be dropped. -/
@[simp]
theorem supportKernelUnion_empty : supportKernelUnion 𝕜 (∅ : Set E) = Set.univ := by
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro x _
  refine ⟨0, ⟨by simp, ?_⟩, ?_⟩
  · intro y hy
    exact False.elim hy
  · rfl

/-- A singleton-support identity converts the union into one kernel.
This theorem does not assert that the supporting family is a singleton. -/
theorem supportKernelUnion_eq_preimage_zero_of_supportFunctionals_eq_singleton
    (F : Set E) (f : StrongDual 𝕜 E) (hF : supportFunctionals 𝕜 F = {f}) :
    supportKernelUnion 𝕜 F = (f : E → 𝕜) ⁻¹' {0} := by
  apply Set.ext
  intro x
  constructor
  · rintro ⟨g, hg, hgx⟩
    rw [hF] at hg
    have hgf : g = f := Set.mem_singleton_iff.1 hg
    subst g
    exact hgx
  · intro hx
    refine ⟨f, ?_, hx⟩
    rw [hF]
    exact Set.mem_singleton f

end NormedSpace
