/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.Basic
public import MathlibAnnex.Analysis.Normed.GeometricStructure.MaximalFace
public import MathlibAnnex.Topology.ClosureSpace.HullKernelSeparation

/-!
# Separation by all geometric-structure points

Every nonzero vector is omitted by a point of the original face-defined GSS.
The proof normalizes the vector and puts it in a maximal face; it does not use
uniqueness of supporting functionals or identify a union of kernels with a submodule.
Consequently, the total intersection is `{0}` and the hull-kernel density criterion
is exactly the criterion in Lemma 4.1 of JMAA 521 (2023), 126944.
Completeness and nontriviality of the primal space are not assumptions.
-/

@[expose] public section

set_option autoImplicit false

open Set Metric

universe u v

namespace NormedSpace

section KernelUnion

variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A union of kernels is stable under scalar multiplication, without an additivity claim. -/
theorem smul_mem_supportKernelUnion {F : Set E} {x : E}
    (hx : x ∈ supportKernelUnion 𝕜 F) (a : 𝕜) : a • x ∈ supportKernelUnion 𝕜 F := by
  rcases hx with ⟨f, hf, hfx⟩
  refine ⟨f, hf, ?_⟩
  rw [map_smul, hfx, smul_zero]

end KernelUnion

variable (𝕜 : Type v) [RCLike 𝕜]
variable (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Zero belongs to every actual GSS point, using existence of support for maximal faces. -/
theorem GeometricStructureSpace.zero_mem (I : GeometricStructureSpace 𝕜 E) :
    (0 : E) ∈ I.val := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  obtain ⟨F, hF, hI⟩ := I.property
  rw [← hI]
  exact (zero_mem_supportKernelUnion_iff 𝕜 F).mpr (hF.nonempty_supportFunctionals 𝕜)

/-- A normalized nonzero vector lies in a maximal face and outside that face's kernel union. -/
theorem exists_geometricStructureSpace_notMem {x : E} (hx : x ≠ 0) :
    ∃ I : GeometricStructureSpace 𝕜 E, x ∉ I.val := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hunit : (‖x‖ : 𝕜)⁻¹ • x ∈ sphere (0 : E) 1 := by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg x), inv_mul_cancel₀ hxnorm]
  obtain ⟨F, hxF, hF⟩ := exists_isMaximalFace_of_mem_sphere hunit
  refine ⟨⟨supportKernelUnion 𝕜 F, ⟨F, hF, rfl⟩⟩, ?_⟩
  intro hxI
  exact notMem_supportKernelUnion_of_mem 𝕜 hxF
    (smul_mem_supportKernelUnion 𝕜 hxI (‖x‖ : 𝕜)⁻¹)

/-- The total intersection of GSS points is zero, including the zero-space case. -/
theorem iInter_geometricStructureSpace :
    (⋂ I : GeometricStructureSpace 𝕜 E, I.val) = ({0} : Set E) := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    apply Set.mem_singleton_iff.mpr
    by_contra hxzero
    obtain ⟨I, hI⟩ := exists_geometricStructureSpace_notMem 𝕜 E hxzero
    exact hI (Set.mem_iInter.mp hx I)
  · intro hx
    have hxzero : x = 0 := Set.mem_singleton_iff.mp hx
    subst x
    exact Set.mem_iInter.mpr (GeometricStructureSpace.zero_mem 𝕜 E)

/-- The total kernel in the generic hull-kernel interface. -/
theorem kernel_geometricStructureFamily_univ :
    ClosureSpace.HullKernel.kernel (geometricStructureFamily 𝕜 E) Set.univ = {0} := by
  have h : ClosureSpace.HullKernel.kernel (geometricStructureFamily 𝕜 E) Set.univ =
      ⋂ I : GeometricStructureSpace 𝕜 E, I.val := by
    apply Set.ext
    intro x
    constructor
    · intro hx
      exact Set.mem_iInter.mpr (fun I => hx I (Set.mem_univ I))
    · intro hx I _
      exact Set.mem_iInter.mp hx I
  exact h.trans (iInter_geometricStructureSpace 𝕜 E)

/-- Unbundled version of the same separation theorem. -/
theorem sInter_geometricStructureFamily : ⋂₀ geometricStructureFamily 𝕜 E = {0} := by
  rw [← ClosureSpace.HullKernel.kernel_univ_eq_sInter]
  exact kernel_geometricStructureFamily_univ 𝕜 E

/-- The full-closure criterion in terms of the existing generic kernel. -/
theorem geometricStructureClosure_eq_univ_iff_kernel_eq_singleton_zero
    (S : Set (GeometricStructureSpace 𝕜 E)) :
    (geometricStructureClosure 𝕜 E).closure S = Set.univ ↔
      ClosureSpace.HullKernel.kernel (geometricStructureFamily 𝕜 E) S = {0} := by
  have h := ClosureSpace.HullKernel.closure_eq_univ_iff_kernel_eq
    (geometricStructureFamily 𝕜 E) (univ_notMem_geometricStructureFamily 𝕜 E) S
  rw [kernel_geometricStructureFamily_univ 𝕜 E] at h
  exact h

/-- Lemma 4.1, expressed with an actual intersection of the selected GSS points. -/
theorem geometricStructureClosure_eq_univ_iff_iInter_eq_singleton_zero
    (S : Set (GeometricStructureSpace 𝕜 E)) :
    (geometricStructureClosure 𝕜 E).closure S = Set.univ ↔
      (⋂ I ∈ S, I.val) = ({0} : Set E) := by
  rw [geometricStructureClosure_eq_univ_iff_kernel_eq_singleton_zero]
  have h := ClosureSpace.HullKernel.kernel_eq_iInter (geometricStructureFamily 𝕜 E) S
  exact ⟨fun hkernel => h.symm.trans hkernel, fun hinter => h.trans hinter⟩

/-- The empty set is closure-dense exactly when the primal space is the zero space.
The empty intersection is still `univ`; the GSS definition is not changed. -/
theorem geometricStructureClosure_empty_eq_univ_iff :
    (geometricStructureClosure 𝕜 E).closure ∅ = Set.univ ↔ Subsingleton E := by
  rw [geometricStructureClosure_eq_univ_iff_kernel_eq_singleton_zero]
  change ClosureSpace.HullKernel.kernel (geometricStructureFamily 𝕜 E)
    (∅ : Set ↑(geometricStructureFamily 𝕜 E)) = {0} ↔ Subsingleton E
  rw [ClosureSpace.HullKernel.kernel_empty]
  constructor
  · intro h
    have hz : ∀ x : E, x = 0 := fun x => Set.mem_singleton_iff.mp (h ▸ Set.mem_univ x)
    exact ⟨fun x y => (hz x).trans (hz y).symm⟩
  · intro h
    letI : Subsingleton E := h
    apply Set.ext
    intro x
    constructor
    · intro _
      exact Set.mem_singleton_iff.mpr (Subsingleton.elim x 0)
    · intro _
      exact Set.mem_univ x

end NormedSpace
