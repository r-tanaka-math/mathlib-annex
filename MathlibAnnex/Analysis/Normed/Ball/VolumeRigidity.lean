import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Strict volume and gauge rigidity for unit balls

This candidate separates two reusable facts.

* A compact proper subset of the closed unit ball of a continuous real seminorm leaves an open
  defect and therefore has strictly smaller additive Haar measure.
* Inclusion, respectively equality, of closed seminorm unit balls under a linear map gives a
  pointwise seminorm inequality, respectively equality.

No convexity of the compact subset is assumed.  Equality of measures is never used without an
independent set-inclusion hypothesis.

This file is a build candidate.  It becomes an admitted MathlibAnnex source only after the pinned
local integration build, recovery tests, dependency audit, and owner-authorized admission.
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace MathlibAnnex

namespace SeminormBall

variable {E F : Type*}

private theorem mem_interior_of_lt
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Seminorm ℝ E) (hp : Continuous p) {x : E} (hx : p x < 1) :
    x ∈ interior (p.closedBall 0 1) := by
  have hopen : IsOpen {z : E | p z < 1} :=
    isOpen_lt hp continuous_const
  have hsub : {z : E | p z < 1} ⊆ p.closedBall 0 1 := by
    intro z hz
    exact p.mem_closedBall_zero.mpr hz.le
  exact interior_maximal hsub hopen hx

private theorem exists_radial_contraction
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : IsClosed K) {y : E} (hy : y ∉ K) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ t • y ∉ K := by
  have hopen : IsOpen Kᶜ := hK.isOpen_compl
  rcases (Metric.isOpen_iff.mp hopen y hy) with ⟨δ, hδ, hball⟩
  let a : ℝ := min (1 / 2 : ℝ) (δ / (2 * (‖y‖ + 1)))
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have ha_half : a ≤ (1 / 2 : ℝ) := min_le_left _ _
  have ha_delta : a ≤ δ / (2 * (‖y‖ + 1)) := min_le_right _ _
  let t : ℝ := 1 - a
  have ht0 : 0 < t := by
    dsimp [t]
    linarith
  have ht1 : t < 1 := by
    dsimp [t]
    linarith
  have ht_sub : t - 1 = -a := by simp [t]
  have habs : |t - 1| = a := by
    rw [ht_sub, abs_neg, abs_of_pos ha]
  have hdist : dist (t • y) y < δ := by
    rw [dist_eq_norm]
    have hsubsmul : t • y - y = (t - 1) • y := by module
    rw [hsubsmul, norm_smul, Real.norm_eq_abs, habs]
    have hnorm : ‖y‖ < ‖y‖ + 1 := by linarith [norm_nonneg y]
    calc
      a * ‖y‖ ≤ (δ / (2 * (‖y‖ + 1))) * ‖y‖ :=
        mul_le_mul_of_nonneg_right ha_delta (norm_nonneg y)
      _ < (δ / (2 * (‖y‖ + 1))) * (‖y‖ + 1) := by
        gcongr
      _ = δ / 2 := by
        field_simp [show 0 < ‖y‖ + 1 by positivity]
      _ < δ := by linarith
  have hmem : t • y ∈ Metric.ball y δ := by
    simpa [Metric.mem_ball] using hdist
  exact ⟨t, ht0, ht1, hball hmem⟩

/-- A compact proper subset of the closed unit ball of a continuous real seminorm leaves a
nonempty open defect.  The compact set itself need not be convex. -/
theorem interior_sdiff_nonempty
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Seminorm ℝ E) (hp : Continuous p)
    {K : Set E} (hKcompact : IsCompact K)
    (hsub : K ⊆ p.closedBall 0 1) (hne : K ≠ p.closedBall 0 1) :
    (interior (p.closedBall 0 1 \ K)).Nonempty := by
  have hproper : ∃ y, y ∈ p.closedBall 0 1 ∧ y ∉ K := by
    by_contra h
    push Not at h
    exact hne (Set.Subset.antisymm hsub h)
  rcases hproper with ⟨y, hyBall, hyK⟩
  rcases exists_radial_contraction hKcompact.isClosed hyK with
    ⟨t, ht0, ht1, htyK⟩
  have htyInt : t • y ∈ interior (p.closedBall 0 1) := by
    apply mem_interior_of_lt p hp
    rw [map_smul_eq_mul p t y, Real.norm_eq_abs, abs_of_pos ht0]
    have hpy : p y ≤ 1 := p.mem_closedBall_zero.mp hyBall
    calc
      t * p y ≤ t * 1 := mul_le_mul_of_nonneg_left hpy ht0.le
      _ = t := by ring
      _ < 1 := ht1
  have hopen : IsOpen (interior (p.closedBall 0 1) ∩ Kᶜ) :=
    isOpen_interior.inter hKcompact.isClosed.isOpen_compl
  have hsubset : interior (p.closedBall 0 1) ∩ Kᶜ ⊆
      p.closedBall 0 1 \ K := by
    intro z hz
    exact ⟨interior_subset hz.1, hz.2⟩
  have hinter : interior (p.closedBall 0 1) ∩ Kᶜ ⊆
      interior (p.closedBall 0 1 \ K) :=
    interior_maximal hsubset hopen
  exact ⟨t • y, hinter ⟨htyInt, htyK⟩⟩

/-- A compact proper subset of the closed unit ball of a continuous real seminorm has strictly
smaller additive Haar measure. -/
theorem measure_lt
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (p : Seminorm ℝ E) (hp : Continuous p)
    {K : Set E} (hKcompact : IsCompact K)
    (hsub : K ⊆ p.closedBall 0 1) (hne : K ≠ p.closedBall 0 1) :
    μ K < μ (p.closedBall 0 1) := by
  have hdiff_nonzero : μ (p.closedBall 0 1 \ K) ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior μ
      (interior_sdiff_nonempty p hp hKcompact hsub hne)).ne'
  have hKmeas : MeasurableSet K := hKcompact.measurableSet
  have hballClosed : IsClosed (p.closedBall 0 1) := by
    rw [show p.closedBall 0 1 = {x : E | p x ≤ 1} by
      ext x
      exact p.mem_closedBall_zero]
    exact isClosed_le hp continuous_const
  have hdecomp : p.closedBall 0 1 = K ∪ (p.closedBall 0 1 \ K) := by
    ext x
    constructor
    · intro hx
      by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr ⟨hx, hxK⟩
    · intro hx
      exact hx.elim (fun hxK => hsub hxK) (fun h => h.1)
  have hdiffmeas : MeasurableSet (p.closedBall 0 1 \ K) :=
    hballClosed.measurableSet.diff hKmeas
  rw [hdecomp, measure_union disjoint_sdiff_right hdiffmeas]
  exact ENNReal.lt_add_right hKcompact.measure_ne_top hdiff_nonzero

/-- Inclusion of closed seminorm unit balls gives the pointwise gauge inequality. -/
theorem map_le
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (p : Seminorm ℝ E) (q : Seminorm ℝ F)
    (hp : ∀ x : E, p x = 0 → x = 0)
    (L : E →ₗ[ℝ] F)
    (hsub : L '' p.closedBall 0 1 ⊆ q.closedBall 0 1) (x : E) :
    q (L x) ≤ p x := by
  by_cases hx : x = 0
  · subst x
    simp
  let a : ℝ := p x
  have ha_nonneg : 0 ≤ p x := apply_nonneg p x
  have ha_ne : p x ≠ 0 := fun h => hx (hp x h)
  have ha : 0 < a := by
    dsimp [a]
    exact lt_of_le_of_ne ha_nonneg ha_ne.symm
  have hu : a⁻¹ • x ∈ p.closedBall 0 1 := by
    apply p.mem_closedBall_zero.mpr
    rw [map_smul_eq_mul p a⁻¹ x, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ha)]
    simp [a, ha.ne']
  have hLu : L (a⁻¹ • x) ∈ q.closedBall 0 1 := hsub ⟨_, hu, rfl⟩
  have hscaled : a⁻¹ * q (L x) ≤ 1 := by
    simpa [map_smul, map_smul_eq_mul q, Real.norm_eq_abs,
      abs_of_pos ha] using q.mem_closedBall_zero.mp hLu
  have hdiv : q (L x) / a ≤ 1 := by
    simpa [div_eq_inv_mul, mul_comm] using hscaled
  have hle : q (L x) ≤ 1 * a := (div_le_iff₀ ha).mp hdiv
  simpa [a] using hle

/-- A bijective linear map carrying one closed seminorm unit ball exactly onto another preserves
both gauges. -/
theorem map_eq
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (p : Seminorm ℝ E) (q : Seminorm ℝ F)
    (hp : ∀ x : E, p x = 0 → x = 0)
    (hq : ∀ y : F, q y = 0 → y = 0)
    (L : E →ₗ[ℝ] F) (hbij : Function.Bijective L)
    (hball : L '' p.closedBall 0 1 = q.closedBall 0 1) (x : E) :
    q (L x) = p x := by
  let e : E ≃ₗ[ℝ] F := LinearEquiv.ofBijective L hbij
  have hforwardSubset : L '' p.closedBall 0 1 ⊆ q.closedBall 0 1 := by
    intro y hy
    rwa [← hball]
  have hforward : q (L x) ≤ p x :=
    map_le p q hp L hforwardSubset x
  have hinverse : e.symm '' q.closedBall 0 1 ⊆ p.closedBall 0 1 := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    rw [← hball] at hy
    rcases hy with ⟨u, hu, hLu⟩
    have hEq : e.symm y = u := by
      apply e.injective
      simp [e, hLu]
    simpa [hEq] using hu
  have hreverse : p (e.symm (L x)) ≤ q (L x) :=
    map_le q p hq e.symm.toLinearMap hinverse (L x)
  have hEx : e.symm (L x) = x := by simp [e]
  exact le_antisymm hforward (by simpa [hEx] using hreverse)

end SeminormBall

namespace NormBall

variable {E F : Type*}

/-- Standard-norm specialization of `SeminormBall.measure_lt`. -/
theorem measure_lt
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {K : Set E} (hKcompact : IsCompact K)
    (hsub : K ⊆ Metric.closedBall (0 : E) 1)
    (hne : K ≠ Metric.closedBall (0 : E) 1) :
    μ K < μ (Metric.closedBall (0 : E) 1) := by
  let p : Seminorm ℝ E := normSeminorm ℝ E
  have hp : Continuous p := by
    simpa [p] using (continuous_norm : Continuous fun x : E => ‖x‖)
  have hsub' : K ⊆ p.closedBall 0 1 := by
    simpa [p] using hsub
  have hne' : K ≠ p.closedBall 0 1 := by
    simpa [p] using hne
  simpa [p] using
    (SeminormBall.measure_lt μ p hp hKcompact hsub' hne')

/-- Standard-norm specialization of `SeminormBall.map_le`. -/
theorem map_le
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →ₗ[ℝ] F)
    (hsub : L '' Metric.closedBall (0 : E) 1 ⊆
      Metric.closedBall (0 : F) 1) (x : E) :
    ‖L x‖ ≤ ‖x‖ := by
  let p : Seminorm ℝ E := normSeminorm ℝ E
  let q : Seminorm ℝ F := normSeminorm ℝ F
  have hp : ∀ z : E, p z = 0 → z = 0 := by
    intro z hz
    exact norm_eq_zero.mp (by simpa [p] using hz)
  have hsub' : L '' p.closedBall 0 1 ⊆ q.closedBall 0 1 := by
    simpa [p, q] using hsub
  simpa [p, q] using
    (SeminormBall.map_le p q hp L hsub' x)

/-- Standard-norm specialization of `SeminormBall.map_eq`. -/
theorem map_eq
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →ₗ[ℝ] F) (hbij : Function.Bijective L)
    (hball : L '' Metric.closedBall (0 : E) 1 =
      Metric.closedBall (0 : F) 1) (x : E) :
    ‖L x‖ = ‖x‖ := by
  let p : Seminorm ℝ E := normSeminorm ℝ E
  let q : Seminorm ℝ F := normSeminorm ℝ F
  have hp : ∀ z : E, p z = 0 → z = 0 := by
    intro z hz
    exact norm_eq_zero.mp (by simpa [p] using hz)
  have hq : ∀ z : F, q z = 0 → z = 0 := by
    intro z hz
    exact norm_eq_zero.mp (by simpa [q] using hz)
  have hball' : L '' p.closedBall 0 1 = q.closedBall 0 1 := by
    simpa [p, q] using hball
  simpa [p, q] using
    (SeminormBall.map_eq p q hp hq L hbij hball' x)

end NormBall

end MathlibAnnex
