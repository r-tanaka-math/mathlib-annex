/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.SmoothSpectrum
public import MathlibAnnex.Analysis.Normed.GeometricStructure.FilterPresentation
public import MathlibAnnex.Topology.ClosureSpace.Topological

/-!
# Failure of topologizability in reflexive smooth spaces of dimension at least two

The dimension hypothesis is cardinal-valued algebraic rank, not `finrank`.
The two geometric-structure points are built from continuous functionals obtained
by Hahn--Banach, rather than supplied as an extra hypothesis. This concerns the
original face-defined geometric structure space; its geometric and primitive
spectra can both be singletons without making this closure topological.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (hsmooth : ∀ x : E, x ≠ 0 → (normingFunctionals 𝕜 x).Subsingleton)
variable (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 E))

include hsmooth hreflexive

/-- Dimension at least two produces two distinct points of the original GSS. -/
theorem exists_ne_geometricStructureSpace_of_two_le_rank_of_smooth_of_reflexive
    (hdim : 2 ≤ Module.rank 𝕜 E) :
    ∃ I J : GeometricStructureSpace 𝕜 E, I ≠ J := by
  obtain ⟨f, g, hf, hg, hker⟩ :=
    exists_ne_zero_dual_preimage_zero_ne_of_two_le_rank hdim
  let I : GeometricStructureSpace 𝕜 E :=
    ⟨(f : E → 𝕜) ⁻¹' {0},
      preimage_zero_mem_geometricStructureFamily_of_smooth_of_surjective_inclusionInDoubleDual
        𝕜 hsmooth hreflexive hf⟩
  let J : GeometricStructureSpace 𝕜 E :=
    ⟨(g : E → 𝕜) ⁻¹' {0},
      preimage_zero_mem_geometricStructureFamily_of_smooth_of_surjective_inclusionInDoubleDual
        𝕜 hsmooth hreflexive hg⟩
  exact ⟨I, J, fun h => hker (congrArg Subtype.val h)⟩

/-- The original GSS closure does not preserve finite unions in dimension at least
 two. Completeness of the ambient space is not needed in addition to the stated
 analytic reflexivity and smoothness hypotheses. -/
theorem not_isTopologizable_geometricStructureClosure_of_two_le_rank_of_smooth_of_reflexive
    (hdim : 2 ≤ Module.rank 𝕜 E) :
    ¬ (geometricStructureClosure 𝕜 E).IsTopologizable := by
  obtain ⟨I, J, hIJ⟩ :=
    exists_ne_geometricStructureSpace_of_two_le_rank_of_smooth_of_reflexive
      𝕜 hsmooth hreflexive hdim
  intro htop
  apply not_isClosed_pair_geometricStructureClosure_of_smooth_of_reflexive
    𝕜 hsmooth hreflexive hIJ
  have hT1 := isT1_geometricStructureClosure 𝕜 E
  simpa only [Set.singleton_union] using htop.isClosed_union (hT1 I) (hT1 J)

end NormedSpace
