import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Pointwise Cauchy control on a dense sequence

This metric lemma has no linear, algebraic, or C-star-algebra hypotheses.  The
domain and codomain may also live in independent universes.
-/

set_option autoImplicit false

open Filter

namespace MathlibAnnex.Metric

universe u v

/-- A sequence of isometries is pointwise Cauchy everywhere if it is
pointwise Cauchy on a dense sequence. -/
theorem cauchySeq_of_isometry_on_dense
    {X : Type u} {Y : Type v} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (d : ℕ → X) (hd : DenseRange d) (f : ℕ → X → Y)
    (hf : ∀ n, Isometry (f n))
    (hfd : ∀ j, CauchySeq (fun n => f n (d j))) :
    ∀ x, CauchySeq (fun n => f n x) := by
  intro x
  rw [Metric.cauchySeq_iff]
  intro epsilon hepsilon
  obtain ⟨j, hj⟩ :=
    (Metric.denseRange_iff.mp hd) x (epsilon / 3) (by positivity)
  obtain ⟨N, hN⟩ :=
    (Metric.cauchySeq_iff.mp (hfd j)) (epsilon / 3) (by positivity)
  refine ⟨N, ?_⟩
  intro m hm n hn
  calc
    dist (f m x) (f n x) ≤
        dist (f m x) (f m (d j)) + dist (f m (d j)) (f n x) :=
      dist_triangle _ _ _
    _ ≤ dist (f m x) (f m (d j)) +
          (dist (f m (d j)) (f n (d j)) + dist (f n (d j)) (f n x)) := by
      gcongr
      exact dist_triangle _ _ _
    _ = dist (f m x) (f m (d j)) +
          dist (f m (d j)) (f n (d j)) + dist (f n (d j)) (f n x) := by
      ring
    _ = dist x (d j) + dist (f m (d j)) (f n (d j)) + dist (d j) x := by
      rw [(hf m).dist_eq, (hf n).dist_eq]
    _ < epsilon / 3 + epsilon / 3 + epsilon / 3 := by
      exact add_lt_add (add_lt_add hj (hN m hm n hn))
        (by simpa [dist_comm] using hj)
    _ = epsilon := by ring

/-- A real-time family of isometries converges to the same pointwise limit as
a discrete family when, on every interval `[n+1,n+2]`, it is uniformly close
to the `n`th discrete map on the first `n` points of a dense sequence. -/
theorem tendsto_atTop_of_isometry_segment_approx
    {X : Type u} {Y : Type v} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (d : ℕ → X) (hd : DenseRange d)
    (f : ℕ → X → Y) (g : ℝ → X → Y)
    (hf : ∀ n, Isometry (f n)) (hg : ∀ t, Isometry (g t))
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (hsegment : ∀ n j, j ≤ n →
      ∀ t : Set.Icc ((n + 1 : ℕ) : ℝ) (n + 2 : ℝ),
        dist (g t (d j)) (f n (d j)) ≤ error n)
    (x : X) (y : Y) (hfx : Tendsto (fun n => f n x) atTop (nhds y)) :
    Tendsto (fun t => g t x) atTop (nhds y) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨j, hj⟩ :=
    (Metric.denseRange_iff.mp hd) x (epsilon / 8) (by positivity)
  obtain ⟨Ne, hNe⟩ :=
    (Metric.tendsto_atTop.mp herror) (epsilon / 4) (by positivity)
  obtain ⟨Nf, hNf⟩ :=
    (Metric.tendsto_atTop.mp hfx) (epsilon / 2) (by positivity)
  let N : ℕ := max j (max Ne Nf)
  refine ⟨((N + 1 : ℕ) : ℝ), ?_⟩
  intro t ht
  have ht0 : 0 ≤ t := le_trans (by positivity : (0 : ℝ) ≤ (N + 1 : ℕ)) ht
  let k : ℕ := ⌊t⌋₊
  have hkt : (k : ℝ) ≤ t := Nat.floor_le ht0
  have htk : t < (k : ℝ) + 1 := Nat.lt_floor_add_one t
  have hkN : N + 1 ≤ k := by
    by_contra h
    have hk : k ≤ N := by omega
    have : t < (N : ℝ) + 1 := lt_of_lt_of_le htk (by exact_mod_cast Nat.succ_le_succ hk)
    norm_num at ht
    linarith
  let n : ℕ := k - 1
  have hnk : n + 1 = k := by
    dsimp only [n]
    omega
  have hnN : N ≤ n := by
    dsimp only [n]
    omega
  have hjn : j ≤ n := le_trans (le_max_left _ _) hnN
  have hNen : Ne ≤ n :=
    le_trans (le_trans (le_max_left Ne Nf) (le_max_right j _)) hnN
  have hNfn : Nf ≤ n :=
    le_trans (le_trans (le_max_right Ne Nf) (le_max_right j _)) hnN
  let ts : Set.Icc ((n + 1 : ℕ) : ℝ) (n + 2 : ℝ) :=
    ⟨t, by
      constructor
      · rw [hnk]
        exact hkt
      · have hle : t ≤ (k : ℝ) + 1 := htk.le
        rw [← hnk] at hle
        norm_num at hle ⊢
        linarith⟩
  have herr := hNe n hNen
  rw [dist_zero_right (error n)] at herr
  have herr' : error n < epsilon / 4 := by
    exact lt_of_le_of_lt (le_abs_self _) (by simpa [Real.norm_eq_abs] using herr)
  have hseg := hsegment n j hjn ts
  have hdisc := hNf n hNfn
  calc
    dist (g t x) y ≤
        dist (g t x) (g t (d j)) +
          dist (g t (d j)) (f n (d j)) +
            dist (f n (d j)) (f n x) + dist (f n x) y := by
      calc
        _ ≤ dist (g t x) (g t (d j)) + dist (g t (d j)) y :=
          dist_triangle _ _ _
        _ ≤ dist (g t x) (g t (d j)) +
            (dist (g t (d j)) (f n (d j)) + dist (f n (d j)) y) := by
          gcongr
          exact dist_triangle _ _ _
        _ ≤ dist (g t x) (g t (d j)) +
            (dist (g t (d j)) (f n (d j)) +
              (dist (f n (d j)) (f n x) + dist (f n x) y)) := by
          gcongr
          exact dist_triangle _ _ _
        _ = _ := by ring
    _ = dist x (d j) + dist (g t (d j)) (f n (d j)) +
          dist (d j) x + dist (f n x) y := by
      rw [(hg t).dist_eq, (hf n).dist_eq]
    _ ≤ dist x (d j) + error n + dist (d j) x + dist (f n x) y := by
      gcongr
    _ < epsilon / 8 + epsilon / 4 + epsilon / 8 + epsilon / 2 := by
      exact add_lt_add (add_lt_add (add_lt_add hj herr')
        (by simpa [dist_comm] using hj)) hdisc
    _ = epsilon := by ring

/-- Pointwise limits may be composed along a moving input when the outer
maps are isometries. -/
theorem tendsto_comp_of_isometry
    {I : Type*} {X : Type u} {Y : Type v} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {l : Filter I} (f : I → X → Y) (g : I → X)
    (hf : ∀ i, Isometry (f i)) {x : X} {y : Y}
    (hg : Tendsto g l (nhds x)) (hfx : Tendsto (fun i ↦ f i x) l (nhds y)) :
    Tendsto (fun i ↦ f i (g i)) l (nhds y) := by
  rw [Metric.tendsto_nhds] at hg hfx ⊢
  intro epsilon hepsilon
  filter_upwards [hg (epsilon / 2) (by positivity),
    hfx (epsilon / 2) (by positivity)] with i hgi hfi
  calc
    dist (f i (g i)) y ≤ dist (f i (g i)) (f i x) + dist (f i x) y :=
      dist_triangle _ _ _
    _ = dist (g i) x + dist (f i x) y := by rw [(hf i).dist_eq]
    _ < epsilon / 2 + epsilon / 2 := add_lt_add hgi hfi
    _ = epsilon := by ring

end MathlibAnnex.Metric
