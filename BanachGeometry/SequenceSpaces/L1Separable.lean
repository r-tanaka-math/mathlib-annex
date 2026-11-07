import BanachGeometry.SequenceSpaces.L1Map
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Bases

/-!
# Separable heterogeneous ℓ₁ sums

The canonical sum of single-coordinate vectors converges in ℓ₁ norm. Its
partial sums lie in the span of the coordinate ranges. This gives a direct
proof of separability for the particular ℓ₁ model used in W01.
-/

noncomputable section
open Filter TopologicalSpace
namespace BanachGeometry

universe u v
variable {ι : Type u} (E : ι → Type v)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

def l1CoordinateSet : Set (L1Sum E) := by
  classical
  exact ⋃ i : ι, Set.range (lp.single (E := E) 1 i)

theorem dense_span_l1CoordinateSet : Dense (Submodule.span ℝ (l1CoordinateSet E) : Set (L1Sum E)) := by
  classical
  intro x
  apply mem_closure_of_tendsto (lp.hasSum_single (p := 1) (by simp) x)
  apply Filter.Eventually.of_forall
  intro s
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.subset_span
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_range_self (x i)⟩

instance l1SeparableSpace [Countable ι] [∀ i, SeparableSpace (E i)] :
    SeparableSpace (L1Sum E) := by
  classical
  have hs : IsSeparable (l1CoordinateSet E) :=
    IsSeparable.iUnion fun i => isSeparable_range
      (lp.singleContinuousLinearMap ℝ E 1 i).continuous
  exact (dense_span_l1CoordinateSet E).isSeparable_iff.1 (hs.span (R := ℝ))

instance l1Nontrivial [Nonempty ι] [∀ i, Nontrivial (E i)] : Nontrivial (L1Sum E) := by
  classical
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (E i)
  refine ⟨⟨lp.single 1 i x, lp.single 1 i y, ?_⟩⟩
  intro h
  apply hxy
  simpa only [lp.single_apply_self] using congrArg (fun z : L1Sum E => z i) h

end BanachGeometry
