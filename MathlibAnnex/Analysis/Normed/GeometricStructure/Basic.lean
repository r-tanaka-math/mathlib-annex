/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.Face
public import MathlibAnnex.Analysis.Normed.GeometricStructure.Support
public import MathlibAnnex.Topology.ClosureSpace.HullKernel

/-!
# The geometric structure space from maximal faces

`S(E)` is a family of sets `I_F`, and not a family of maximal faces: different faces
with the same union of kernels yield the same point. The real structure used for
faces is the canonical restriction of scalars from the given `RCLike` field.
Completeness, finite dimension, and nontriviality are not assumed.

The representation by extreme-functional kernels is a subsequent bridge theorem,
not the definition. No C*-algebra result is imported here.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The family of unions of supporting kernels, indexed by maximal faces.
The existential is propositional: repeated subsets are not repeated points. -/
def geometricStructureFamily : Set (Set E) :=
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  {I | ∃ F : Set E, IsMaximalFace F ∧ supportKernelUnion 𝕜 F = I}

theorem mem_geometricStructureFamily (I : Set E) :
    I ∈ geometricStructureFamily 𝕜 E ↔
      (letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
       ∃ F : Set E, IsMaximalFace F ∧ supportKernelUnion 𝕜 F = I) := Iff.rfl

/-- The family meets the exact admissibility condition for the generic hull-kernel space. -/
theorem univ_notMem_geometricStructureFamily :
    Set.univ ∉ geometricStructureFamily 𝕜 E := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  rintro ⟨F, hF, hI⟩
  exact supportKernelUnion_ne_univ 𝕜 hF.nonempty hI

/-- The points of the geometric structure space are actual subsets of the normed space. -/
def GeometricStructureSpace : Type u := {I : Set E // I ∈ geometricStructureFamily 𝕜 E}

/-- The hull-kernel closure on `S(E)`. -/
def geometricStructureClosure : ClosureSpace (GeometricStructureSpace 𝕜 E) :=
  ClosureSpace.HullKernel.space (geometricStructureFamily 𝕜 E)
    (univ_notMem_geometricStructureFamily 𝕜 E)

/-- The closure formula exposes the intersection, including the empty intersection. -/
theorem geometricStructureClosure_closure (S : Set (GeometricStructureSpace 𝕜 E)) :
    (geometricStructureClosure 𝕜 E).closure S =
      {I | (∀ x : E, (∀ J : GeometricStructureSpace 𝕜 E, J ∈ S → x ∈ J.val) →
        x ∈ I.val)} := rfl

/-- Generic hull-kernel separation gives T0, not yet the stronger T1 theorem. -/
theorem isT0_geometricStructureClosure : (geometricStructureClosure 𝕜 E).IsT0 :=
  ClosureSpace.HullKernel.isT0_space (geometricStructureFamily 𝕜 E)
    (univ_notMem_geometricStructureFamily 𝕜 E)

/-- The family is empty in the zero-space case. -/
theorem geometricStructureFamily_eq_empty_of_subsingleton [Subsingleton E] :
    geometricStructureFamily 𝕜 E = ∅ := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  apply Set.eq_empty_iff_forall_notMem.2
  rintro I ⟨F, hF, _⟩
  exact not_isMaximalFace_of_subsingleton F hF

/-- No geometric-structure-space point exists in the zero space. -/
theorem isEmpty_geometricStructureSpace_of_subsingleton [Subsingleton E] :
    IsEmpty (GeometricStructureSpace 𝕜 E) := by
  refine ⟨?_⟩
  intro I
  exact (Set.eq_empty_iff_forall_notMem.mp
    (geometricStructureFamily_eq_empty_of_subsingleton 𝕜 E)) I.val I.property

end NormedSpace
