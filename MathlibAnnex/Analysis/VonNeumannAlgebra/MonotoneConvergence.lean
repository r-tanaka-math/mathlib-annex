import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.MonotoneConvergence
import MathlibAnnex.Analysis.InnerProductSpace.StrongOperator

/-!
# Monotone convergence of bounded positive operators

An increasing norm-bounded family of positive operators on a complex Hilbert
space has a least upper bound and converges strongly to it. The index is an
arbitrary nonempty directed preorder. Neither separability nor a countable
cofinal subset is required.

The analytic estimate is obtained from the existing C-star factorization of a
positive element as `star S * S`. Scalar monotone convergence then makes each
orbit a Cauchy filter. `ContinuousLinearMap.ofTendstoOfBoundedRange` supplies the
bounded operator represented by the pointwise limit.

All topology on the ambient operator type remains the usual operator-norm
topology. Strong convergence uses the existing `StronglyConverges` predicate.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped InnerProduct

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The positive cone is closed under strong limits along nontrivial filters.
Eventual positivity is enough. -/
theorem nonneg_of_stronglyConverges {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → H →L[ℂ] H} {T : H →L[ℂ] H}
    (hlim : StronglyConverges f l T) (hpos : ∀ᶠ i in l, 0 ≤ f i) : 0 ≤ T := by
  refine nonneg_iff_isPositive.mpr ⟨?_, ?_⟩
  · intro x y
    change inner ℂ (T x) y = inner ℂ x (T y)
    apply tendsto_nhds_unique_of_eventuallyEq
      ((hlim x).inner tendsto_const_nhds)
      (tendsto_const_nhds.inner (hlim y))
    filter_upwards [hpos] with i hi
    exact (nonneg_iff_isPositive.mp hi).inner_left_eq_inner_right x y
  · intro x
    change 0 ≤ (inner ℂ (T x) x).re
    have hreal : Tendsto (fun i ↦ (inner ℂ (f i x) x).re) l
        (𝓝 (inner ℂ (T x) x).re) :=
      Complex.continuous_re.continuousAt.tendsto.comp
        ((hlim x).inner tendsto_const_nhds)
    exact ge_of_tendsto hreal <| hpos.mono fun i hi ↦
      (nonneg_iff_isPositive.mp hi).re_inner_nonneg_left x

/-- A strong limit of an increasing net is its least upper bound in the
Loewner order. The existence of the limit is a separate analytic issue. -/
theorem isLUB_of_stronglyConverges_of_monotone {ι : Type*}
    [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {f : ι → H →L[ℂ] H} {T : H →L[ℂ] H}
    (hmono : Monotone f) (hlim : StronglyConverges f atTop T) :
    IsLUB (Set.range f) T := by
  constructor
  · rintro _ ⟨i, rfl⟩
    apply sub_nonneg.mp
    apply nonneg_of_stronglyConverges (hlim.sub (StronglyConverges.const (f i)))
    filter_upwards [eventually_ge_atTop i] with j hij
    exact sub_nonneg.mpr (hmono hij)
  · intro U hU
    apply sub_nonneg.mp
    apply nonneg_of_stronglyConverges ((StronglyConverges.const U).sub hlim)
    exact Eventually.of_forall fun i ↦ sub_nonneg.mpr (hU (mem_range_self i))

/-- Positivity improves the operator-norm bound to a quadratic-form bound.
This estimate applies in particular to every positive difference in a
monotone family. -/
theorem norm_apply_sq_le_norm_mul_re_inner {T : H →L[ℂ] H}
    (hT : 0 ≤ T) (x : H) :
    ‖T x‖ ^ 2 ≤ ‖T‖ * (inner ℂ x (T x)).re := by
  obtain ⟨S, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hT
  calc
    ‖(star S * S) x‖ ^ 2 = ‖(star S) (S x)‖ ^ 2 := rfl
    _ ≤ (‖star S‖ * ‖S x‖) ^ 2 := by
      have h := (star S).le_opNorm (S x)
      nlinarith [norm_nonneg ((star S) (S x)),
        mul_nonneg (norm_nonneg (star S)) (norm_nonneg (S x))]
    _ = ‖star S * S‖ * (inner ℂ x ((star S * S) x)).re := by
      change (‖star S‖ * ‖S x‖) ^ 2 = ‖star S * S‖ * (inner ℂ x (star S (S x))).re
      have he : (inner ℂ (S x) (S x)).re = ‖S x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) (S x)
      rw [norm_star, CStarRing.norm_star_mul_self, star_eq_adjoint, adjoint_inner_right, he]
      ring

private theorem cauchy_map_apply_of_monotone_of_norm_bounded {ι : Type*}
    [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (f : ι → H →L[ℂ] H) (hmono : Monotone f)
    {C : ℝ} (hC : 0 < C) (hbound : ∀ i, ‖f i‖ ≤ C) (x : H) :
    Cauchy (Filter.map (fun i ↦ f i x) atTop) := by
  let q : ι → ℝ := fun i ↦ (inner ℂ x (f i x)).re
  have hqmono : Monotone q := by
    intro i j hij
    have h := (le_def.mp (hmono hij)).re_inner_nonneg_right x
    change 0 ≤ (inner ℂ x ((f j - f i) x)).re at h
    simpa only [q, sub_apply, inner_sub_right, Complex.sub_re, sub_nonneg] using h
  have hqbound : BddAbove (Set.range q) := by
    refine ⟨C * ‖x‖ ^ 2, ?_⟩
    rintro _ ⟨i, rfl⟩
    calc
      q i ≤ ‖inner ℂ x (f i x)‖ := Complex.re_le_norm _
      _ ≤ ‖x‖ * ‖f i x‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (C * ‖x‖) :=
        mul_le_mul_of_nonneg_left ((f i).le_of_opNorm_le (hbound i) x) (norm_nonneg x)
      _ = C * ‖x‖ ^ 2 := by ring
  let a : ℝ := ⨆ i, q i
  have hqle (i : ι) : q i ≤ a := le_ciSup hqbound i
  have hqlim : Tendsto q atTop (𝓝 a) := tendsto_atTop_ciSup hqmono hqbound
  refine Metric.cauchy_iff.mpr ⟨inferInstance, ?_⟩
  intro ε hε
  let δ : ℝ := (ε / 2) ^ 2 / (2 * C)
  have htwoC : 0 < 2 * C := mul_pos (by norm_num) hC
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_order.mp hqlim).1 (a - δ) (sub_lt_self a hδ))
  have htail : ∀ n, N ≤ n → dist (f n x) (f N x) < ε / 2 := by
    intro n hn
    have hD : 0 ≤ f n - f N := sub_nonneg.mpr (hmono hn)
    have hDbound : ‖f n - f N‖ ≤ 2 * C := calc
      ‖f n - f N‖ ≤ ‖f n‖ + ‖f N‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (hbound n) (hbound N)
      _ = 2 * C := by ring
    have hqdiff : 0 ≤ q n - q N := sub_nonneg.mpr (hqmono hn)
    have hsq : ‖f n x - f N x‖ ^ 2 ≤ (2 * C) * (q n - q N) := calc
      ‖f n x - f N x‖ ^ 2 = ‖(f n - f N) x‖ ^ 2 := rfl
      _ ≤ ‖f n - f N‖ * (inner ℂ x ((f n - f N) x)).re :=
        norm_apply_sq_le_norm_mul_re_inner hD x
      _ = ‖f n - f N‖ * (q n - q N) := by
        simp only [q, sub_apply, inner_sub_right, Complex.sub_re]
      _ ≤ (2 * C) * (q n - q N) :=
        mul_le_mul_of_nonneg_right hDbound hqdiff
    have hgap : q n - q N < δ := by
      have := hN N le_rfl
      have := hqle n
      linarith
    have hsmall : (2 * C) * (q n - q N) < (ε / 2) ^ 2 := by
      have h := (lt_div_iff₀ htwoC).mp hgap
      simpa only [mul_comm] using h
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (f n x - f N x), half_pos hε]
  refine ⟨(fun i ↦ f i x) '' Set.Ici N, ?_, ?_⟩
  · change ∀ᶠ i in atTop, f i x ∈ (fun j ↦ f j x) '' Set.Ici N
    filter_upwards [eventually_ge_atTop N] with i hi
    exact ⟨i, hi, rfl⟩
  · rintro y ⟨i, hi, rfl⟩ z ⟨j, hj, rfl⟩
    calc
      dist (f i x) (f j x) ≤ dist (f i x) (f N x) + dist (f N x) (f j x) :=
        dist_triangle _ _ _
      _ < ε / 2 + ε / 2 :=
        add_lt_add (htail i hi) (by simpa only [dist_comm] using htail j hj)
      _ = ε := by ring

/-- Every bounded increasing positive operator net has an ambient least
upper bound, and the entire net converges strongly to that upper bound. -/
theorem exists_isLUB_stronglyConverges_of_monotone {ι : Type*}
    [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (f : ι → H →L[ℂ] H) (hmono : Monotone f) (hpos : ∀ i, 0 ≤ f i)
    (hbounded : ∃ C : ℝ, ∀ i, ‖f i‖ ≤ C) :
    ∃ T : H →L[ℂ] H, 0 ≤ T ∧ IsLUB (Set.range f) T ∧
      StronglyConverges f atTop T := by
  classical
  obtain ⟨C₀, hC₀⟩ := hbounded
  let C : ℝ := max C₀ 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right C₀ 1)
  have hbound (i : ι) : ‖f i‖ ≤ C := (hC₀ i).trans (le_max_left C₀ 1)
  have hex : ∀ x : H, ∃ y : H, Tendsto (fun i ↦ f i x) atTop (𝓝 y) := by
    intro x
    exact cauchy_map_iff_exists_tendsto.mp
      (cauchy_map_apply_of_monotone_of_norm_bounded f hmono hC hbound x)
  choose g hg using hex
  have hnorm : Bornology.IsBounded (Set.range f) :=
    isBounded_iff_forall_norm_le.mpr ⟨C, Set.forall_mem_range.mpr hbound⟩
  let T : H →L[ℂ] H := ofTendstoOfBoundedRange g f (tendsto_pi_nhds.mpr hg) hnorm
  have hlim : StronglyConverges f atTop T := by
    intro x
    exact hg x
  exact ⟨T, nonneg_of_stronglyConverges hlim (Eventually.of_forall hpos),
    isLUB_of_stronglyConverges_of_monotone hmono hlim, hlim⟩

/-- Order boundedness is sufficient for the monotone convergence theorem;
the required norm bound follows from the existing C-star order estimate. -/
theorem exists_isLUB_stronglyConverges_of_monotone_of_bddAbove {ι : Type*}
    [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (f : ι → H →L[ℂ] H) (hmono : Monotone f) (hpos : ∀ i, 0 ≤ f i)
    (hbounded : BddAbove (Set.range f)) :
    ∃ T : H →L[ℂ] H, 0 ≤ T ∧ IsLUB (Set.range f) T ∧
      StronglyConverges f atTop T := by
  obtain ⟨U, hU⟩ := hbounded
  exact exists_isLUB_stronglyConverges_of_monotone f hmono hpos
    ⟨‖U‖, fun i ↦ CStarAlgebra.norm_le_norm_of_le_of_nonneg
      (hU (mem_range_self i)) (hpos i)⟩

end ContinuousLinearMap
