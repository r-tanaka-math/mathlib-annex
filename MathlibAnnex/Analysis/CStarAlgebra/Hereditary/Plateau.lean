/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.Hereditary.CornerEquivalence
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# An exact local unit on a smaller nonzero hereditary corner

For a positive `a` and `0 < δ < ‖a‖₊`, the cutoff `b = (a - δ)₊` is nonzero.
The zero-preserving function `t / max δ t` gives a positive contraction `e`
inside `Her(a)` which fixes `b` on both sides. Consequently it fixes the full
closed hereditary algebra `Her(b)`, using the existing closed-equalizer lemmas.
The element `e` belongs to the larger corner, not necessarily to `Her(b)`;
neither element is asserted to be a projection.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra NNReal

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- A cutoff strictly below the original positive element's norm is nonzero.
This reuses the existing cutoff error estimate in the original C-star norm. -/
theorem cfcₙ_tsub_ne_zero {a : A} (ha : 0 ≤ a) {δ : ℝ≥0}
    (hδ : δ < ‖a‖₊) : cfcₙ (fun t : ℝ≥0 => t - δ) a ≠ 0 := by
  intro hz
  have h := nnnorm_sub_cfcₙ_tsub_le ha δ
  rw [hz, sub_zero] at h
  exact (not_le_of_gt hδ) h

/-- A positive CFC element in the larger corner, with an exact plateau on
the positive cutoff. It is not a unit of the ambient algebra. -/
def hereditaryPlateauUnit (a : A) (δ : ℝ≥0) : A :=
  cfcₙ (fun t : ℝ≥0 => t / max δ t) a

theorem hereditaryPlateauUnit_nonneg (a : A) (δ : ℝ≥0) :
    0 ≤ hereditaryPlateauUnit a δ := cfcₙ_predicate _ _

theorem hereditaryPlateauUnit_mem_hereditarySubalgebra {a : A}
    (ha : 0 ≤ a) (δ : ℝ≥0) :
    hereditaryPlateauUnit a δ ∈ hereditarySubalgebra a :=
  cfcₙ_nnreal_mem (𝕜 := ℂ) (fun t : ℝ≥0 => t / max δ t)
    (self_mem_hereditarySubalgebra ha)

theorem norm_hereditaryPlateauUnit_le_one (a : A) {δ : ℝ≥0} (hδ : 0 < δ) :
    ‖hereditaryPlateauUnit a δ‖ ≤ 1 := by
  have h : ‖hereditaryPlateauUnit a δ‖₊ ≤ 1 := by
    apply nnnorm_cfcₙ_nnreal_le
    intro t ht
    exact (div_le_one (lt_of_lt_of_le hδ (le_max_left δ t))).mpr (le_max_right δ t)
  exact h

/-- The scalar plateau is exact on the support of the cutoff. -/
private theorem div_max_mul_tsub {δ : ℝ≥0} (hδ : 0 < δ) (t : ℝ≥0) :
    (t / max δ t) * (t - δ) = t - δ := by
  by_cases ht : t ≤ δ
  · simp only [tsub_eq_zero_of_le ht, mul_zero]
  · have hδt : δ ≤ t := (lt_of_not_ge ht).le
    have ht0 : t ≠ 0 := ne_of_gt (hδ.trans_le hδt)
    rw [max_eq_right hδt, div_self ht0, one_mul]

/-- The multiplication identity is evaluated by the real nonunital CFC,
with continuity and the zero value supplied explicitly. -/
theorem hereditaryPlateauUnit_mul_cfcₙ_tsub (a : A) {δ : ℝ≥0} (hδ : 0 < δ) :
    hereditaryPlateauUnit a δ * cfcₙ (fun t : ℝ≥0 => t - δ) a =
      cfcₙ (fun t : ℝ≥0 => t - δ) a := by
  have he : Continuous (fun t : ℝ≥0 => t / max δ t) :=
    continuous_id.div₀ (continuous_const.max continuous_id)
      (fun t => ne_of_gt (lt_of_lt_of_le hδ (le_max_left δ t)))
  have hb : Continuous (fun t : ℝ≥0 => t - δ) := by fun_prop
  rw [hereditaryPlateauUnit,
    ← cfcₙ_mul _ _ _ he.continuousOn (by simp) hb.continuousOn (by simp)]
  exact cfcₙ_congr fun t _ => div_max_mul_tsub hδ t

theorem cfcₙ_tsub_mul_hereditaryPlateauUnit (a : A) {δ : ℝ≥0} (hδ : 0 < δ) :
    cfcₙ (fun t : ℝ≥0 => t - δ) a * hereditaryPlateauUnit a δ =
      cfcₙ (fun t : ℝ≥0 => t - δ) a := by
  calc
    _ = hereditaryPlateauUnit a δ * cfcₙ (fun t : ℝ≥0 => t - δ) a :=
      (cfcₙ_commute_cfcₙ (fun t : ℝ≥0 => t - δ)
        (fun t : ℝ≥0 => t / max δ t) a).eq
    _ = _ := hereditaryPlateauUnit_mul_cfcₙ_tsub a hδ

/-- The exact plateau fixes every closure element, not only CFC functions of `a`. -/
theorem hereditaryPlateauUnit_mul_eq_self_of_mem (a : A) {δ : ℝ≥0}
    (hδ : 0 < δ) {z : A}
    (hz : z ∈ hereditarySubalgebra (cfcₙ (fun t : ℝ≥0 => t - δ) a)) :
    hereditaryPlateauUnit a δ * z = z ∧ z * hereditaryPlateauUnit a δ = z := by
  have hb : 0 ≤ cfcₙ (fun t : ℝ≥0 => t - δ) a := cfcₙ_predicate _ _
  constructor
  · exact mul_eq_self_of_mem_hereditarySubalgebra
      (hereditaryPlateauUnit_mul_cfcₙ_tsub a hδ) hz
  · apply mul_eq_self_of_mem_hereditarySubalgebra_right _ hz
    simpa only [hb.star_eq] using cfcₙ_tsub_mul_hereditaryPlateauUnit a hδ

/-- When the fixed corner is nonzero, the local unit has norm exactly one. -/
theorem norm_hereditaryPlateauUnit {a : A} (ha : 0 ≤ a) {δ : ℝ≥0}
    (hδ : 0 < δ) (hδa : δ < ‖a‖₊) : ‖hereditaryPlateauUnit a δ‖ = 1 := by
  let b := cfcₙ (fun t : ℝ≥0 => t - δ) a
  have hb0 : b ≠ 0 := cfcₙ_tsub_ne_zero ha hδa
  have hb : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  have he : hereditaryPlateauUnit a δ * b = b := hereditaryPlateauUnit_mul_cfcₙ_tsub a hδ
  have hm : ‖b‖ ≤ ‖hereditaryPlateauUnit a δ‖ * ‖b‖ := by
    calc
      ‖b‖ = ‖hereditaryPlateauUnit a δ * b‖ := congrArg norm he.symm
      _ ≤ ‖hereditaryPlateauUnit a δ‖ * ‖b‖ := norm_mul_le _ _
  have hn := norm_hereditaryPlateauUnit_le_one a hδ
  have hge : (1 : ℝ) ≤ ‖hereditaryPlateauUnit a δ‖ :=
    (mul_le_mul_iff_left₀ hb).mp (by simpa only [one_mul] using hm)
  exact le_antisymm hn hge

/-- Every nonzero positive element has a smaller nonzero hereditary plateau
and a positive contractive exact local unit in its original hereditary algebra. -/
theorem exists_nonzero_hereditary_plateau {a : A} (ha : 0 ≤ a) (ha0 : a ≠ 0) :
    ∃ b e : A, 0 ≤ b ∧ b ≠ 0 ∧ b ∈ hereditarySubalgebra a ∧
      0 ≤ e ∧ ‖e‖ ≤ 1 ∧ e ∈ hereditarySubalgebra a ∧ e * b = b ∧ b * e = b := by
  have hna : (0 : ℝ≥0) < ‖a‖₊ :=
    pos_iff_ne_zero.mpr (fun h => ha0 (nnnorm_eq_zero.mp h))
  obtain ⟨δ, hδ, hδa⟩ := exists_between hna
  refine ⟨cfcₙ (fun t : ℝ≥0 => t - δ) a, hereditaryPlateauUnit a δ,
    cfcₙ_predicate _ _, cfcₙ_tsub_ne_zero ha hδa,
    cfcₙ_tsub_mem_hereditarySubalgebra ha δ, hereditaryPlateauUnit_nonneg a δ,
    norm_hereditaryPlateauUnit_le_one a hδ,
    hereditaryPlateauUnit_mem_hereditarySubalgebra ha δ,
    hereditaryPlateauUnit_mul_cfcₙ_tsub a hδ, cfcₙ_tsub_mul_hereditaryPlateauUnit a hδ⟩

end MathlibAnnex.Analysis.CStarAlgebra
