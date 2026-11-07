import BanachGeometry.WeakSequences.TailReduction
import Mathlib.Topology.Sequences
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Compactness.Compact

/-! Weak-Cauchy subsequences in spaces with separable dual, by countably
many scalar evaluations and a compact product of real intervals. -/

noncomputable section
open Filter TopologicalSpace
namespace BanachGeometry
namespace SeparableDual

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [SeparableSpace (B →L[ℝ] ℝ)]

theorem unit_sequence_subsequence (u : ℕ → B) (hu : ∀ n, ‖u n‖ ≤ 1) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ WeaklyCauchy (u ∘ s) := by
  let φ : ℕ → B →L[ℝ] ℝ := denseSeq (B →L[ℝ] ℝ)
  let K : Set (ℕ → ℝ) := Set.pi Set.univ (fun k => Set.Icc (-‖φ k‖) ‖φ k‖)
  let y : ℕ → ℕ → ℝ := fun n k => φ k (u n)
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hy : ∀ n, y n ∈ K := by
    intro n
    change ∀ k ∈ (Set.univ : Set ℕ), -‖φ k‖ ≤ φ k (u n) ∧ φ k (u n) ≤ ‖φ k‖
    intro k hk
    have hb : ‖φ k (u n)‖ ≤ ‖φ k‖ := by
      calc
        ‖φ k (u n)‖ ≤ ‖φ k‖ * ‖u n‖ := (φ k).le_opNorm _
        _ ≤ ‖φ k‖ * 1 := mul_le_mul_of_nonneg_left (hu n) (norm_nonneg _)
        _ = ‖φ k‖ := mul_one _
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hb)
  obtain ⟨z, hz, s, hs, ht⟩ := hK.tendsto_subseq hy
  refine ⟨s, hs, ?_⟩
  intro f
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := (denseRange_denseSeq (B →L[ℝ] ℝ)).exists_dist_lt f (by positivity : 0 < ε / 4)
  have hclose : ‖f - φ k‖ < ε / 4 := by simpa only [dist_eq_norm] using hk
  have heval : CauchySeq (fun n => φ k (u (s n))) := (ht.apply_nhds k).cauchySeq
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp heval (ε / 2) (by positivity)
  refine ⟨N, ?_⟩
  intro n hn m hm
  have hmid : ‖φ k (u (s n)) - φ k (u (s m))‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hN n hn m hm
  have hleft : ‖(f - φ k) (u (s n))‖ < ε / 4 := by
    apply lt_of_le_of_lt _ hclose
    calc
      ‖(f - φ k) (u (s n))‖ ≤ ‖f - φ k‖ * ‖u (s n)‖ := (f - φ k).le_opNorm _
      _ ≤ ‖f - φ k‖ * 1 := mul_le_mul_of_nonneg_left (hu _) (norm_nonneg _)
      _ = ‖f - φ k‖ := mul_one _
  have hright : ‖(f - φ k) (u (s m))‖ < ε / 4 := by
    apply lt_of_le_of_lt _ hclose
    calc
      ‖(f - φ k) (u (s m))‖ ≤ ‖f - φ k‖ * ‖u (s m)‖ := (f - φ k).le_opNorm _
      _ ≤ ‖f - φ k‖ * 1 := mul_le_mul_of_nonneg_left (hu _) (norm_nonneg _)
      _ = ‖f - φ k‖ := mul_one _
  have hdiff : ‖f (u (s n)) - f (u (s m))‖ < ε := by
    calc
      ‖f (u (s n)) - f (u (s m))‖ =
          ‖(f - φ k) (u (s n)) + (φ k (u (s n)) - φ k (u (s m))) -
            (f - φ k) (u (s m))‖ := by
        congr 1; simp only [ContinuousLinearMap.sub_apply]; abel
      _ ≤ ‖(f - φ k) (u (s n)) + (φ k (u (s n)) - φ k (u (s m)))‖ +
          ‖(f - φ k) (u (s m))‖ := norm_sub_le _ _
      _ ≤ (‖(f - φ k) (u (s n))‖ + ‖φ k (u (s n)) - φ k (u (s m))‖) +
          ‖(f - φ k) (u (s m))‖ := add_le_add (norm_add_le _ _) le_rfl
      _ < ε := by linarith
  simpa only [Function.comp_def, dist_eq_norm] using hdiff

end SeparableDual
end BanachGeometry
