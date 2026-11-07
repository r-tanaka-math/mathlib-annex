import BanachGeometry.SequenceSpaces.C0Sum
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Bases

/-! Closedness, completeness and separability of the heterogeneous c₀ sum.
Closedness uses the supremum norm on the ambient ℓ∞ sum. Separability uses norm
convergence of finite heads and separability of the span of the countable union
of coordinate ranges. No norm or common interface instance is replaced.
Execution evidence is recorded in the external receipts. -/

noncomputable section
open Filter TopologicalSpace
open scoped ENNReal
namespace BanachGeometry

universe u v
variable {ι : Type u} (E : ι → Type v)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

/-- The norm-null condition is closed in the actual supremum norm. -/
theorem isClosed_c0Submodule : IsClosed (c0Submodule E : Set (lp E ∞)) := by
  refine isClosed_iff_clusterPt.mpr ?_
  intro f hf
  rw [clusterPt_principal_iff] at hf
  change Tendsto (fun i => ‖f i‖) cofinite (nhds 0)
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  obtain ⟨g, hg, hgnull⟩ := hf (Metric.ball f (ε / 2))
    (Metric.ball_mem_nhds f (half_pos hε))
  have hgf : ‖f - g‖ < ε / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hg
  change Tendsto (fun i => ‖g i‖) cofinite (nhds 0) at hgnull
  have hsmall : ∀ᶠ i in cofinite, ‖g i‖ < ε / 2 :=
    hgnull.eventually (eventually_lt_nhds (half_pos hε))
  filter_upwards [hsmall] with i hi
  have hcoord : ‖(f - g) i‖ ≤ ‖f - g‖ :=
    lp.norm_apply_le_norm ENNReal.top_ne_zero (f - g) i
  have hcoord' : ‖f i - g i‖ ≤ ‖f - g‖ := by
    simpa only [lp.coeFn_sub, Pi.sub_apply] using hcoord
  have hnorm : ‖f i‖ < ε := by
    calc
      ‖f i‖ = ‖(f i - g i) + g i‖ := by rw [sub_add_cancel]
      _ ≤ ‖f i - g i‖ + ‖g i‖ := norm_add_le _ _
      _ ≤ ‖f - g‖ + ‖g i‖ := add_le_add hcoord' le_rfl
      _ < ε / 2 + ε / 2 := add_lt_add hgf hi
      _ = ε := add_halves ε
  simpa only [Real.dist_eq, sub_zero, abs_norm] using hnorm

/-- Completeness is inherited from the closed subspace of the complete ℓ∞ sum. -/
instance c0SumCompleteSpace [∀ i, CompleteSpace (E i)] : CompleteSpace (C0Sum E) :=
  (isClosed_c0Submodule E).isComplete.completeSpace_coe

namespace C0Sum
variable {E}

/-- Inclusion into a single heterogeneous coordinate, with finite support. -/
def single (i : ι) (x : E i) : C0Sum E := by
  classical
  refine ⟨lp.single ∞ i x, ?_⟩
  change Tendsto (fun j => ‖lp.single ∞ i x j‖) cofinite (nhds 0)
  apply (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ)) cofinite (nhds 0)).congr'
  filter_upwards [eventually_cofinite_ne i] with j hj
  simp only [lp.single_apply_ne ∞ i x hj, norm_zero]

@[simp] theorem single_apply_self (i : ι) (x : E i) : single i x i = x := by
  classical
  exact lp.single_apply_self ∞ i x

theorem single_apply_ne (i : ι) (x : E i) {j : ι} (h : j ≠ i) :
    single i x j = 0 := by
  classical
  exact lp.single_apply_ne ∞ i x h

@[simp] theorem norm_single (i : ι) (x : E i) : ‖single i x‖ = ‖x‖ := by
  classical
  exact lp.norm_single (by simp : (0 : ℝ≥0∞) < ∞) i x

def singleLinearIsometry (i : ι) : E i →ₗᵢ[ℝ] C0Sum E where
  toFun := single i
  map_add' x y := by
    classical
    apply Subtype.ext
    exact lp.single_add ∞ i x y
  map_smul' a x := by
    classical
    apply Subtype.ext
    exact lp.single_smul ∞ i a x
  norm_map' := norm_single i

instance singleNontrivial [Nonempty ι] [∀ i, Nontrivial (E i)] : Nontrivial (C0Sum E) := by
  classical
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (E i)
  refine ⟨⟨single i x, single i y, ?_⟩⟩
  intro h
  apply hxy
  simpa using congrArg (fun z : C0Sum E => z i) h

end C0Sum

section Sequence
variable (V : ℕ → Type*) [∀ n, NormedAddCommGroup (V n)]
    [∀ n, NormedSpace ℝ (V n)]

namespace C0Sum

/-- The first n coordinates, including the empty head for n=0. -/
def head (n : ℕ) (x : C0Sum V) : C0Sum V :=
  ∑ i ∈ Finset.range n, single i (x i)

theorem head_apply (n : ℕ) (x : C0Sum V) (i : ℕ) :
    head V n x i = if i < n then x i else 0 := by
  induction n with
  | zero => simp [head]
  | succ n ih =>
    rw [head, Finset.sum_range_succ, add_apply]
    change head V n x i + single n (x n) i = _
    rw [ih]
    by_cases he : i = n
    · subst i
      simp
    · rw [single_apply_ne n (x n) he, add_zero]
      by_cases hi : i < n
      · simp [hi, show i < n + 1 by omega]
      · simp [hi, show ¬ i < n + 1 by omega]

/-- Finite heads converge in the inherited supremum norm, not merely pointwise. -/
theorem tendsto_head (x : C0Sum V) : Tendsto (fun n => head V n x) atTop (nhds x) := by
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  have he : ∀ᶠ i in atTop, ‖x i‖ < ε / 2 :=
    x.null_atTop.eventually (eventually_lt_nhds (half_pos hε))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 he
  refine Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro n hn
  have hb : ‖head V n x - x‖ ≤ ε / 2 := by
    apply C0Sum.norm_le (le_of_lt (half_pos hε))
    intro i
    rw [sub_apply, head_apply]
    by_cases hi : i < n
    · simpa [hi] using (le_of_lt (half_pos hε))
    · simpa only [if_neg hi, zero_sub, norm_neg] using
        (hN i (le_trans hn (Nat.le_of_not_gt hi))).le
  simpa only [dist_eq_norm] using hb.trans_lt (half_lt_self hε)

def coordinateSet : Set (C0Sum V) := ⋃ i : ℕ, Set.range (single (E := V) i)

theorem dense_span_coordinateSet : Dense (Submodule.span ℝ (coordinateSet V) : Set (C0Sum V)) := by
  intro x
  apply mem_closure_of_tendsto (tendsto_head V x)
  apply Filter.Eventually.of_forall
  intro n
  change (∑ i ∈ Finset.range n, single i (x i)) ∈ Submodule.span ℝ (coordinateSet V)
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.subset_span
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_range_self (x i)⟩

/-- Countably many separable coordinate ranges have separable dense real span. -/
instance separableSpace [∀ n, SeparableSpace (V n)] : SeparableSpace (C0Sum V) := by
  have hs : IsSeparable (coordinateSet V) :=
    IsSeparable.iUnion fun i => isSeparable_range (singleLinearIsometry (E := V) i).continuous
  exact (dense_span_coordinateSet V).isSeparable_iff.1 (hs.span (R := ℝ))

end C0Sum
end Sequence
end BanachGeometry
