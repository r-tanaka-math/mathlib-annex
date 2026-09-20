import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteCentral.BasisOperators
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.UniversalNormalTests

/-!
# One finite compression for all normal gauge tests

C06, UNBUILT. The coordinate projections are contractions and form one net
indexed by ALL finite subsets of one Hilbert basis. The gauges use the actual
source-state corner functionals from C03, not arbitrary B(H) functionals.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexOrder
namespace MathlibAnnex.FiniteCentral
open MathlibAnnex.RepresentedCentralCorner MathlibAnnex.RepresentedBidual
open MathlibAnnex.CStarBilinear
universe u v w t
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {ι : Type w}
variable (b : HilbertBasis ι ℂ H)

/-- The SAME projection is used on both sides. -/
def compression (s : Finset ι) (T : H →L[ℂ] H) : H →L[ℂ] H :=
  coordinateProjection b s * T * coordinateProjection b s

theorem norm_compression_le (s : Finset ι) (T : H →L[ℂ] H) :
    ‖compression b s T‖ ≤ ‖T‖ := by
  calc
    _ ≤ (‖coordinateProjection b s‖ * ‖T‖) * ‖coordinateProjection b s‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖T‖) * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right (norm_coordinateProjection_le_one b s) (norm_nonneg T))
      (norm_coordinateProjection_le_one b s) (norm_nonneg _) (by positivity)
    _ = ‖T‖ := by ring

@[simp] theorem star_compression (s : Finset ι) (T : H →L[ℂ] H) :
    star (compression b s T) = compression b s (star T) := by
  simp only [compression, star_mul, star_coordinateProjection]
  rw [mul_assoc]

/-- Quantitative two-sided compression error. -/
theorem compression_error_bound (s : Finset ι) (T : H →L[ℂ] H) (x : H) :
    ‖compression b s T x - T x‖ ≤
      ‖T‖ * ‖coordinateProjection b s x - x‖ +
        ‖coordinateProjection b s (T x) - T x‖ := by
  have he : compression b s T x - T x =
      coordinateProjection b s (T (coordinateProjection b s x - x)) +
        (coordinateProjection b s (T x) - T x) := by
    simp only [compression, ContinuousLinearMap.mul_apply, map_sub]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add_left
  calc
    _ ≤ ‖coordinateProjection b s‖ * ‖T (coordinateProjection b s x - x)‖ :=
      (coordinateProjection b s).le_opNorm _
    _ ≤ 1 * (‖T‖ * ‖coordinateProjection b s x - x‖) := mul_le_mul
      (norm_coordinateProjection_le_one b s) (T.le_opNorm _) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem tendsto_compression (T : H →L[ℂ] H) (x : H) :
    Tendsto (fun s : Finset ι => compression b s T x) atTop (𝓝 (T x)) := by
  classical
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun s => norm_nonneg _) (compression_error_bound b · T x)
  have h1 := ((tendsto_coordinateProjection b x).sub_const x).norm.const_mul ‖T‖
  have h2 := ((tendsto_coordinateProjection b (T x)).sub_const (T x)).norm
  simpa only [sub_self, norm_zero, mul_zero, add_zero] using h1.add h2

theorem tendsto_compression_star (T : H →L[ℂ] H) (x : H) :
    Tendsto (fun s : Finset ι => star (compression b s T) x) atTop (𝓝 (star T x)) := by
  simpa only [star_compression] using tendsto_compression b (star T) x

theorem norm_compression_error_le (s : Finset ι) (T : H →L[ℂ] H) :
    ‖T - compression b s T‖ ≤ 2 * ‖T‖ :=
  (norm_sub_le _ _).trans (by linarith [norm_compression_le b s T])

/-- Turn pointwise strong convergence into WOT convergence, with no
assertion that multiplication is jointly WOT continuous. -/
theorem wot_of_strong {κ : Type t} (l : Filter κ)
    (T : κ → H →L[ℂ] H) (U : H →L[ℂ] H)
    (h : ∀ x, Tendsto (fun i => T i x) l (𝓝 (U x))) :
    Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (T i)) l
      (𝓝 (ContinuousLinearMapWOT.ofCLM U)) := by
  apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
  intro x y
  exact (innerSL ℂ y).continuous.continuousAt.tendsto.comp (h x)

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial H]
variable (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)

/-- Only ACTUAL corner functionals are used here; their bounded normality
was constructed from the fixed predual, rather than assumed for every form. -/
theorem tendsto_compression_gauge (T : H →L[ℂ] H) (phi : StrongDual ℂ A) :
    Tendsto (fun s : Finset ι => strongStarGauge (cornerFunctional pi hpi phi)
      (T - compression b s T)) atTop (𝓝 0) := by
  have hX (x : H) : Tendsto (fun s : Finset ι => (T - compression b s T) x)
      atTop (𝓝 0) := by
    simpa only [ContinuousLinearMap.sub_apply, sub_self] using
       (show Tendsto (fun _ : Finset ι => T x) atTop (𝓝 (T x)) from
         tendsto_const_nhds).sub (tendsto_compression b T x)
  have hXs (x : H) : Tendsto (fun s : Finset ι => star (T - compression b s T) x)
      atTop (𝓝 0) := by
    simpa only [star_sub, ContinuousLinearMap.sub_apply, sub_self] using
       (show Tendsto (fun _ : Finset ι => star T x) atTop (𝓝 (star T x)) from
         tendsto_const_nhds).sub (tendsto_compression_star b T x)
  exact tendsto_cornerGauge_zero pi hpi atTop _ hX hXs (2 * ‖T‖)
    (Eventually.of_forall (fun s => norm_compression_error_le b s T)) phi

/-- A finite conjunction at one filter, proved by finite-set induction. -/
theorem eventually_all_finite {J : Type t} [Fintype J] {κ : Type*}
    (l : Filter κ) (P : κ → J → Prop) (h : ∀ j, ∀ᶠ i in l, P i j) :
    ∀ᶠ i in l, ∀ j, P i j := by
  classical
  have hs (s : Finset J) : ∀ᶠ i in l, ∀ j ∈ s, P i j := by
    induction s using Finset.induction_on with
    | empty => exact Eventually.of_forall (by simp)
    | @insert j s hj ih =>
      filter_upwards [h j, ih] with i hij his
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hks
      · exact hij
      · exact his k hks
  simpa only [Finset.mem_univ, forall_const] using hs Finset.univ

/-- A finite conjunction is selected from one common filter, not by
independently choosing a projection for every test. -/
theorem exists_common_compression {J : Type t} [Fintype J]
    (T : J → H →L[ℂ] H) (phi psi : J → StrongDual ℂ A)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ s : Finset ι, ∀ j,
      strongStarGauge (cornerFunctional pi hpi (phi j)) (T j - compression b s (T j)) ≤ delta ∧
      strongStarGauge (cornerFunctional pi hpi (psi j)) (T j - compression b s (T j)) ≤ delta := by
  classical
  have hj (j : J) : ∀ᶠ s : Finset ι in atTop,
      strongStarGauge (cornerFunctional pi hpi (phi j)) (T j - compression b s (T j)) ≤ delta ∧
      strongStarGauge (cornerFunctional pi hpi (psi j)) (T j - compression b s (T j)) ≤ delta := by
    have hp := (tendsto_compression_gauge b pi hpi (T j) (phi j))
      (eventually_lt_nhds hdelta)
    have hq := (tendsto_compression_gauge b pi hpi (T j) (psi j))
      (eventually_lt_nhds hdelta)
    filter_upwards [hp, hq] with s hps hqs
    exact ⟨le_of_lt hps, le_of_lt hqs⟩
  have hall : ∀ᶠ s : Finset ι in atTop, ∀ j : J,
      strongStarGauge (cornerFunctional pi hpi (phi j)) (T j - compression b s (T j)) ≤ delta ∧
      strongStarGauge (cornerFunctional pi hpi (psi j)) (T j - compression b s (T j)) ≤ delta := by
    exact eventually_all_finite atTop _ hj
  exact hall.exists

/-- Tail projections converge strongly to zero and have norm at most one. -/
theorem tendsto_tail_functional (phi : StrongDual ℂ A) :
    Tendsto (fun s : Finset ι => cornerFunctional pi hpi phi
      (1 - coordinateProjection b s)) atTop (𝓝 0) := by
  have ht (x : H) : Tendsto (fun s : Finset ι =>
      ((1 : H →L[ℂ] H) - coordinateProjection b s) x) atTop (𝓝 0) := by
    simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
       sub_self] using
         (show Tendsto (fun _ : Finset ι => x) atTop (𝓝 x) from
           tendsto_const_nhds).sub (tendsto_coordinateProjection b x)
  have hh := tendsto_cornerFunctional pi hpi atTop
    (fun s : Finset ι => 1 - coordinateProjection b s) 0
    (wot_of_strong atTop _ 0 ht) 1
    (Eventually.of_forall (norm_tail_projection_le_one b)) phi
  simpa only [map_zero] using hh

theorem exists_common_small_tail {J : Type t} [Fintype J]
    (phi psi : J → StrongDual ℂ A) {eta : ℝ} (heta : 0 < eta) :
    ∃ s : Finset ι, ∀ j,
      ‖cornerFunctional pi hpi (phi j) (1 - coordinateProjection b s)‖ < eta ∧
      ‖cornerFunctional pi hpi (psi j) (1 - coordinateProjection b s)‖ < eta := by
  classical
  have hj (j : J) : ∀ᶠ s : Finset ι in atTop,
      ‖cornerFunctional pi hpi (phi j) (1 - coordinateProjection b s)‖ < eta ∧
      ‖cornerFunctional pi hpi (psi j) (1 - coordinateProjection b s)‖ < eta := by
    have hp := (tendsto_tail_functional b pi hpi (phi j)).norm
    have hq := (tendsto_tail_functional b pi hpi (psi j)).norm
    have hε : ‖(0 : ℂ)‖ < eta := by simpa using heta
    have hp' : ∀ᶠ s : Finset ι in atTop,
        ‖cornerFunctional pi hpi (phi j) (1 - coordinateProjection b s)‖ < eta :=
      hp (eventually_lt_nhds hε)
    have hq' : ∀ᶠ s : Finset ι in atTop,
        ‖cornerFunctional pi hpi (psi j) (1 - coordinateProjection b s)‖ < eta :=
      hq (eventually_lt_nhds hε)
    exact hp'.and hq'
  exact (eventually_all_finite atTop _ hj).exists

end MathlibAnnex.FiniteCentral
