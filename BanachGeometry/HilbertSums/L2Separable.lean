/- Shared proof boundary: the existing lp_two_separable theorem, moved
without a new premise so concrete scalar duals need not import construction data. -/
import BanachGeometry.Basic
import Mathlib.Topology.Algebra.Module.Basic

open scoped ENNReal BigOperators Topology
noncomputable section
namespace BanachGeometry.HilbertSums

theorem lp_two_separable {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)]
    [∀ n, NormedSpace ℝ (G n)] [∀ n, TopologicalSpace.SeparableSpace (G n)] :
    TopologicalSpace.SeparableSpace (lp G 2) := by
  let S : Set (lp G 2) := ⋃ n, Set.range (fun x : G n => lp.single 2 n x)
  have hs : TopologicalSpace.IsSeparable S := by
    apply TopologicalSpace.IsSeparable.iUnion
    intro n
    exact TopologicalSpace.isSeparable_range
      (lp.isometry_single (p := 2) (E := G) n).continuous
  have hd : Dense (Submodule.span ℝ S : Set (lp G 2)) := by
    intro y
    have hmem (N : ℕ) : (∑ n ∈ Finset.range N, lp.single 2 n (y n)) ∈ Submodule.span ℝ S := by
      apply Submodule.sum_mem
      intro n _
      exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨n, ⟨y n, rfl⟩⟩)
    have ht := (lp.hasSum_single (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) y).tendsto_sum_nat
    exact isClosed_closure.mem_of_tendsto ht
      (Filter.Eventually.of_forall fun N => subset_closure (hmem N))
  have hspan : TopologicalSpace.IsSeparable (Submodule.span ℝ S : Set (lp G 2)) := hs.span
  exact hd.isSeparable_iff.mp hspan

end BanachGeometry.HilbertSums
