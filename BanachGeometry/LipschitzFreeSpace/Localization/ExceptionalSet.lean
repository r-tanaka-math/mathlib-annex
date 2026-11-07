/- Provenance adaptation: finite exceptional-set architecture with arbitrary increment subspaces and finite-dimensional projections.
Source: openai/math@4eaee87548250b2682affda7d05d947c05554bae, lean/OAI/Analysis/LipschitzEquivalence/LocalLipschitz.lean.
Apache-2.0 upstream material; current attribution and proof ranges: ATTRIBUTION/PROVENANCE.json. -/
/- R6 8.1 exceptional-set estimate for arbitrary complete real Hilbert target.
Adapted proof architecture: upstream LocalLipschitz.badSet_finite, openai/math
4eaee87548250b2682affda7d05d947c05554bae (Apache-2.0, LICENSES/OPENAI_MATH_APACHE_2_0.txt).
Changes: arbitrary increment subspaces, arbitrary open neighborhoods, finite-dimensional
head projection; no fixed-coordinate target or domain separability premise here.
Local execution status is recorded in the external qualification receipts. -/
import BanachGeometry.LipschitzFreeSpace.Localization.FiniteProjection
import BanachGeometry.LipschitzFreeGeometry.LocalLipschitz

noncomputable section
open scoped Topology NNReal InnerProductSpace
open Filter Set
namespace BanachGeometry.LipschitzFreeLocalization
open BanachGeometry.LipschitzFreeGeometry.LocalLipschitz
open BanachGeometry.LipschitzFreeGeometry.CoordinateLocality

universe uM uH
variable {M : Type uM} {H : Type uH} [MetricSpace M]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Local scalar test constant depends on the projections of b, not on values D(x). -/
theorem scalar_increment_lipschitzOn (D : M → H) {L : ℝ≥0} (hD : LipschitzWith L D)
    (F K : Submodule ℝ H) [F.HasOrthogonalProjection] [K.HasOrthogonalProjection]
    (hFK : ∀ f ∈ F, ∀ k ∈ K, ⟪f, k⟫_ℝ = 0)
    (S : Set M) (hinc : ∀ x ∈ S, ∀ y ∈ S, D x - D y ∈ F ⊔ K) (b : H) :
    LipschitzOnWith (⟨(L : ℝ) * (‖F.starProjection b‖ + ‖K.starProjection b‖), by positivity⟩ : ℝ≥0)
      (fun x => ⟪D x, b⟫_ℝ) S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq, ← inner_sub_left]
  have ht := abs_inner_le_projection_norms F K hFK (hinc x hx y hy) b
  have hd := hD.dist_le_mul x y
  rw [dist_eq_norm] at hd
  exact ht.trans (by
    change (‖F.starProjection b‖ + ‖K.starProjection b‖) * ‖D x - D y‖ ≤
      (L : ℝ) * (‖F.starProjection b‖ + ‖K.starProjection b‖) * dist x y
    calc
      _ ≤ (‖F.starProjection b‖ + ‖K.starProjection b‖) * ((L : ℝ) * dist x y) :=
        mul_le_mul_of_nonneg_left hd (add_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring)

/-- The countable basis/subsequence is supplied later on a compact subset only.
This theorem works for any basis family satisfying the displayed neighborhood property. -/
theorem badSet_finite_of_incrementLocality [CompleteSpace H]
    (D : M → H) {L : ℝ≥0} (hL : 0 < L) (hD : LipschitzWith L D)
    (hloc : IncrementLocality D) (b : ℕ → H) (hbn : ∀ i, ‖b i‖ ≤ 1)
    (hb : BanachGeometry.WeakNull b) {B : Type*} (O : B → Set M)
    (hbase : ∀ z : M, ∀ U : Set M, IsOpen U → z ∈ U → ∃ j, z ∈ O j ∧ O j ⊆ U)
    (a : B → ℝ)
    (ha : ∀ j, Tendsto (fun i => constant (fun x => ⟪D x, b i⟫_ℝ) (O j)) atTop (𝓝 (a j)))
    {η : ℝ} (hη : 0 < η) : (badSet O a η).Finite := by
  classical
  by_contra hn
  have hinf : (badSet O a η).Infinite := hn
  let e : ℕ ↪ badSet O a η := hinf.natEmbedding _
  let t : ℝ := η / (4 * (L : ℝ))
  have hL' : 0 < (L : ℝ) := hL
  have ht : 0 < t := div_pos hη (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / t ^ 2)
  let z : Fin N → M := fun j => (e j.val).val
  have hz : Function.Injective z := by
    intro i j hij
    apply Fin.ext
    apply e.injective
    exact Subtype.ext hij
  obtain ⟨U, hU, F, hF, K, hK, horth, hinc⟩ := hloc z hz
  letI : FiniteDimensional ℝ F := hF
  letI : ∀ j, CompleteSpace (K j) := fun j => (hK j).1.completeSpace_coe
  letI : ∀ j, (K j).HasOrthogonalProjection := fun j => inferInstance
  have hFK (j : Fin N) : ∀ f ∈ F, ∀ k ∈ K j, ⟪f, k⟫_ℝ = 0 := by
    intro f hf k hk
    exact (Submodule.mem_orthogonal _ _).mp ((hK j).2 hk) f hf
  choose j hzj hj using fun k => hbase (z k) (U k) (hU k).1 (hU k).2
  have hja (k : Fin N) : η ≤ a (j k) := (e k.val).property (j k) (hzj k)
  have hhead := tendsto_norm_starProjection_zero F hb
  have hbound (k : Fin N) : ∀ᶠ i in atTop, t ≤ ‖(K k).starProjection (b i)‖ := by
    have hsmall := hhead.eventually (eventually_lt_nhds ht)
    have hbig := (ha (j k)).eventually (eventually_gt_nhds (show η / 2 < a (j k) by linarith [hja k]))
    filter_upwards [hsmall, hbig] with i hi hgi
    have hconst := BanachGeometry.LipschitzFreeGeometry.LocalLipschitz.constant_le (scalar_increment_lipschitzOn D hD F (K k) (hFK k)
      (O (j k)) (fun x hx y hy => hinc k x (hj k hx) y (hj k hy)) (b i))
    change constant (fun x => ⟪D x, b i⟫_ℝ) (O (j k)) ≤
      (L : ℝ) * (‖F.starProjection (b i)‖ + ‖(K k).starProjection (b i)‖) at hconst
    have htid : (L : ℝ) * t = η / 4 := by dsimp [t]; field_simp [ne_of_gt hL'] <;> ring
    nlinarith
  obtain ⟨i, hi⟩ := (Filter.eventually_all.mpr hbound).exists
  have hcard := card_le_one_div_sq_of_large_projections K horth (b i) (hbn i) ht hi
  have hcard' : (N : ℝ) ≤ 1 / t ^ 2 := by simpa using hcard
  exact (not_lt_of_ge hcard') hN

end BanachGeometry.LipschitzFreeLocalization
