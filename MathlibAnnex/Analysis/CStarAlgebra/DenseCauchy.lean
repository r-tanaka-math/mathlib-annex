import MathlibAnnex.Analysis.CStarAlgebra.ApproximateIntertwining
import MathlibAnnex.Topology.MetricSpace.DenseCauchy

/-!
# Pointwise Cauchy control from a dense sequence

These lemmas isolate the analytic bookkeeping used by approximately inner
intertwining arguments.  Uniformly isometric maps need step estimates only
on an increasing finite prefix of a dense sequence.
-/

set_option autoImplicit false

open Filter

namespace MathlibAnnex.CStarAlgebra

variable {A : Type*} [CStarAlgebra A]

/-- A sequence of isometries which is Cauchy on a dense sequence is Cauchy
at every point. -/
theorem cauchySeq_of_isometry_on_dense
    (d : ℕ → A) (hd : DenseRange d) (f : ℕ → A → A)
    (hf : ∀ n, Isometry (f n))
    (hfd : ∀ j, CauchySeq (fun n => f n (d j))) :
    ∀ a, CauchySeq (fun n => f n a) :=
  MathlibAnnex.Metric.cauchySeq_of_isometry_on_dense d hd f hf hfd

/-- Summable step bounds on successively longer prefixes of a dense sequence
give pointwise Cauchy control everywhere. -/
theorem cauchySeq_of_summable_dense_steps
    (d : ℕ → A) (hd : DenseRange d)
    (f : ℕ → StarAlgEquiv ℂ A A)
    (budget : ℕ → ℝ) (hbudget : Summable budget)
    (hstep : ∀ n j, j ≤ n →
      ‖f (n + 1) (d j) - f n (d j)‖ ≤ budget n) :
    ∀ a, CauchySeq (fun n => f n a) := by
  apply cauchySeq_of_isometry_on_dense d hd (fun n => f n)
    (fun n => StarAlgEquiv.isometry (f n))
  intro j
  apply cauchySeq_of_summable_norm_step
  rw [← summable_nat_add_iff j]
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => hstep (n + j) j (by omega))
  exact (summable_nat_add_iff j).mpr hbudget

/-- Pointwise Cauchy sequences of isometries remain pointwise Cauchy under
diagonal composition.  The moving-input estimate is the only extra point. -/
theorem cauchySeq_trans_of_isometry
    (f g : ℕ → StarAlgEquiv ℂ A A)
    (hf : ∀ a, CauchySeq (fun n => f n a))
    (hg : ∀ a, CauchySeq (fun n => g n a)) :
    ∀ a, CauchySeq (fun n => (g n).trans (f n) a) := by
  intro a
  obtain ⟨b, hgb⟩ := cauchySeq_tendsto_of_complete (hg a)
  rw [Metric.cauchySeq_iff]
  intro epsilon hepsilon
  obtain ⟨Ng, hNg⟩ := (Metric.tendsto_atTop.mp hgb) (epsilon / 3) (by positivity)
  obtain ⟨Nf, hNf⟩ := (Metric.cauchySeq_iff.mp (hf b))
    (epsilon / 3) (by positivity)
  refine ⟨max Ng Nf, ?_⟩
  intro m hm n hn
  have hgm := hNg m (le_trans (le_max_left Ng Nf) hm)
  have hgn := hNg n (le_trans (le_max_left Ng Nf) hn)
  have hfm := le_trans (le_max_right Ng Nf) hm
  have hfn := le_trans (le_max_right Ng Nf) hn
  calc
    dist (f m (g m a)) (f n (g n a)) ≤
        dist (f m (g m a)) (f m b) +
          dist (f m b) (f n b) + dist (f n b) (f n (g n a)) := by
      calc
        _ ≤ dist (f m (g m a)) (f m b) + dist (f m b) (f n (g n a)) :=
          dist_triangle _ _ _
        _ ≤ dist (f m (g m a)) (f m b) +
            (dist (f m b) (f n b) + dist (f n b) (f n (g n a))) := by
          gcongr
          exact dist_triangle _ _ _
        _ = _ := by ring
    _ = dist (g m a) b + dist (f m b) (f n b) + dist b (g n a) := by
      rw [(StarAlgEquiv.isometry (f m)).dist_eq,
        (StarAlgEquiv.isometry (f n)).dist_eq]
    _ < epsilon / 3 + epsilon / 3 + epsilon / 3 := by
      exact add_lt_add (add_lt_add hgm (hNf m hfm n hfn))
        (by simpa [dist_comm] using hgn)
    _ = epsilon := by ring

/-- Contractive functionals and isometric test maps extend a vanishing state
estimate from increasing prefixes of a dense sequence to every element. -/
theorem tendsto_functional_of_dense_prefix
    (d : ℕ → A) (hd : DenseRange d)
    (f : ℕ → StarAlgEquiv ℂ A A)
    (phi psi : A →L[ℂ] ℂ)
    (hphi : ∀ a, ‖phi a‖ ≤ ‖a‖) (hpsi : ∀ a, ‖psi a‖ ≤ ‖a‖)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (happrox : ∀ n j, j ≤ n →
      ‖phi (f n (d j)) - psi (d j)‖ < error n) :
    ∀ a, Tendsto (fun n => phi (f n a)) atTop (nhds (psi a)) := by
  intro a
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨j, hj⟩ := (Metric.denseRange_iff.mp hd) a (epsilon / 4) (by positivity)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp herror) (epsilon / 2) (by positivity)
  refine ⟨max N j, ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (le_max_left N j) hn
  have hjn : j ≤ n := le_trans (le_max_right N j) hn
  have herr := hN n hnN
  rw [dist_zero_right] at herr
  have herr' : error n < epsilon / 2 := by
    exact lt_of_le_of_lt (le_abs_self _) (by simpa [Real.norm_eq_abs] using herr)
  have hj' : ‖a - d j‖ < epsilon / 4 := by
    simpa only [dist_eq_norm] using hj
  rw [dist_eq_norm]
  calc
    ‖phi (f n a) - psi a‖ ≤
        ‖phi (f n a) - phi (f n (d j))‖ +
          ‖phi (f n (d j)) - psi (d j)‖ +
            ‖psi (d j) - psi a‖ := by
      calc
        _ ≤ ‖phi (f n a) - phi (f n (d j))‖ +
            ‖phi (f n (d j)) - psi a‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ‖phi (f n a) - phi (f n (d j))‖ +
            (‖phi (f n (d j)) - psi (d j)‖ + ‖psi (d j) - psi a‖) := by
          gcongr
          exact norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ = _ := by ring
    _ ≤ ‖f n a - f n (d j)‖ + error n + ‖d j - a‖ := by
      exact add_le_add (add_le_add
        (by simpa only [map_sub] using hphi (f n a - f n (d j)))
        (le_of_lt (happrox n j hjn)))
        (by simpa only [map_sub] using hpsi (d j - a))
    _ = ‖a - d j‖ + error n + ‖d j - a‖ := by
      have hdist : ‖f n a - f n (d j)‖ = ‖a - d j‖ := by
        simpa only [dist_eq_norm] using
          (StarAlgEquiv.isometry (f n)).dist_eq a (d j)
      rw [hdist]
    _ < epsilon / 4 + epsilon / 2 + epsilon / 4 := by
      exact add_lt_add (add_lt_add hj' herr') (by simpa [norm_sub_rev] using hj')
    _ = epsilon := by ring

end MathlibAnnex.CStarAlgebra
