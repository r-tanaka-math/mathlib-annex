import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import MathlibAnnex.Analysis.InnerProductSpace.StrongOperator

/-!
# Strong limits of decreasing orthogonal projections

The result is stated for an arbitrary directed preorder.  For a decreasing
sequence it identifies the strong limit with the orthogonal projection onto
the common fixed subspace, represented by the infimum of the ranges.
-/

set_option autoImplicit false

open Filter Topology

namespace Submodule

variable {𝕜 E ι : Type*}
variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E] [Preorder ι]

private theorem closure_iSup_orthogonal (U : ι → Submodule 𝕜 E)
    [∀ i, (U i).HasOrthogonalProjection] :
    (⨆ i, (U i)ᗮ).topologicalClosure = (⨅ i, U i)ᗮ := by
  rw [← orthogonal_orthogonal_eq_closure, ← iInf_orthogonal]
  simp only [orthogonal_orthogonal]

/-- Orthogonal projections onto an antitone family of complete subspaces
converge strongly to the projection onto their intersection. -/
theorem tendsto_starProjection_iInf (U : ι → Submodule 𝕜 E)
    [∀ i, (U i).HasOrthogonalProjection]
    [(⨅ i, U i).HasOrthogonalProjection] (hU : Antitone U) (x : E) :
    Tendsto (fun i ↦ (U i).starProjection x) atTop
      (𝓝 ((⨅ i, U i).starProjection x)) := by
  let V : ι → Submodule 𝕜 E := fun i ↦ (U i)ᗮ
  have hV : Monotone V := fun _ _ hij ↦ orthogonal_le (hU hij)
  have hlim := starProjection_tendsto_closure_iSup V hV x
  have hclosure : (⨆ i, V i).topologicalClosure = (⨅ i, U i)ᗮ :=
    closure_iSup_orthogonal U
  have hlim' : Tendsto (fun i ↦ (V i).starProjection x) atTop
      (𝓝 ((⨅ i, U i)ᗮ.starProjection x)) := by
    simpa only [hclosure] using hlim
  have hcomp : Tendsto (fun i ↦ x - (V i).starProjection x) atTop
      (𝓝 (x - (⨅ i, U i)ᗮ.starProjection x)) := by
    exact tendsto_const_nhds.sub hlim'
  simpa [V, starProjection_orthogonal] using hcomp

/-- Operator-valued formulation of `tendsto_starProjection_iInf`. -/
theorem stronglyConverges_starProjection_iInf (U : ι → Submodule 𝕜 E)
    [∀ i, (U i).HasOrthogonalProjection]
    [(⨅ i, U i).HasOrthogonalProjection] (hU : Antitone U) :
    ContinuousLinearMap.StronglyConverges (fun i ↦ (U i).starProjection) atTop
      (⨅ i, U i).starProjection :=
  fun x ↦ tendsto_starProjection_iInf U hU x

/-- The infimum of the ranges is exactly the common fixed-point subspace. -/
theorem mem_iInf_iff_starProjection_eq_self (U : ι → Submodule 𝕜 E)
    [∀ i, (U i).HasOrthogonalProjection] {x : E} :
    x ∈ ⨅ i, U i ↔ ∀ i, (U i).starProjection x = x := by
  simp only [mem_iInf, starProjection_eq_self_iff]

end Submodule
