/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.Basic
public import MathlibAnnex.Analysis.Normed.GeometricStructure.FilterAntichain

/-!
# The filter presentation of the face-defined geometric structure space

The comparison is for nontrivial normed spaces and requires no completeness.
The original face-defined space remains empty in the zero-space case. No
second definition of the geometric structure space is introduced.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- In nontrivial normed spaces, the existing family of face kernels equals
the family of intersection kernels of maximal orthogonality filters. -/
theorem mem_geometricStructureFamily_iff_exists_maximal_filter [Nontrivial E] (I : Set E) :
    I ∈ geometricStructureFamily 𝕜 E ↔
      ∃ U : Set E, IsMaximalBirkhoffJamesFilter 𝕜 U ∧ birkhoffJamesKernel 𝕜 U = I := by
  letI : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  change (∃ F : Set E, IsMaximalFace F ∧ supportKernelUnion 𝕜 F = I) ↔ _
  constructor
  · rintro ⟨F, hF, rfl⟩
    obtain ⟨U, _, hU, hUI⟩ := hF.exists_isMaximalBirkhoffJamesFilter 𝕜
    exact ⟨U, hU, hUI⟩
  · rintro ⟨U, hU, rfl⟩
    obtain ⟨f, hf⟩ := hU.1.exists_common_absoluteNormingFunctional 𝕜
    exact ⟨unitBallSupportFace 𝕜 f, hU.isMaximalFace_unitBallSupportFace 𝕜 hf,
      (hU.kernel_eq_supportKernelUnion 𝕜 hf).symm⟩

/-- Distinct members of the actual face-defined family are incomparable. The
zero-space case is discharged from the already defined empty family. -/
theorem GeometricStructureSpace.eq_of_subset (I J : GeometricStructureSpace 𝕜 E)
    (hIJ : I.val ⊆ J.val) : I = J := by
  classical
  rcases subsingleton_or_nontrivial E with hE | hE
  · letI := hE
    exact False.elim ((isEmpty_geometricStructureSpace_of_subsingleton 𝕜 E).false I)
  · letI := hE
    letI : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
    obtain ⟨U, hU, hUI⟩ :=
      (mem_geometricStructureFamily_iff_exists_maximal_filter 𝕜 E I.val).mp I.property
    obtain ⟨W, hW, hWJ⟩ :=
      (mem_geometricStructureFamily_iff_exists_maximal_filter 𝕜 E J.val).mp J.property
    have heq : U = W := hU.eq_of_kernel_subset 𝕜 hW (by rwa [hUI, hWJ])
    apply Subtype.ext
    exact hUI.symm.trans ((congrArg (birkhoffJamesKernel 𝕜) heq).trans hWJ)

/-- T1 separation of the existing geometric-structure closure, including the
empty zero-space case. This invokes the original generic hull-kernel API. -/
theorem isT1_geometricStructureClosure : (geometricStructureClosure 𝕜 E).IsT1 :=
  ClosureSpace.HullKernel.isT1_space_of_antichain (geometricStructureFamily 𝕜 E)
    (univ_notMem_geometricStructureFamily 𝕜 E) (GeometricStructureSpace.eq_of_subset 𝕜 E)

end NormedSpace
