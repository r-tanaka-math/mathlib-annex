/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.Hereditary.CornerEquivalence
import MathlibAnnex.Analysis.CStarAlgebra.Hereditary.Plateau
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.SquareZero
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# A contractive link between orthogonal hereditary corners

For a square-zero element `x`, put `p = x⋆x`. The scalar function
`sqrt t / max δ t` is continuous and zero preserving when `δ > 0`.
The existing nonunital CFC produces

* `c = (p - δ)₊`, written as `cfcₙ (fun t : ℝ≥0 => t - δ) p`;
* `v = x * cfcₙ (cutoffInverseSqrt δ) p`;
* the positive target generator `v * c * star v`.

The cutoff is nonzero for `δ < ‖p‖₊`, and `v` is contractive. The exact
relations `star v * v * c = c` and `c * v = 0` hold in the original algebra.
The generic hereditary conjugation equivalence then supplies the actual
isomorphism of the two full closed sandwich algebras. Neither `c` nor
`star v * v` is asserted to be a projection.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra NNReal

namespace MathlibAnnex.Analysis.CStarAlgebra

/-- A zero-preserving continuous regularization of the reciprocal square root.
The nonnegative-real domain is exactly the spectrum used for a positive CFC. -/
def cutoffInverseSqrt (δ t : ℝ≥0) : ℝ≥0 := NNReal.sqrt t / max δ t

@[simp]
theorem cutoffInverseSqrt_zero (δ : ℝ≥0) : cutoffInverseSqrt δ 0 = 0 := by
  simp [cutoffInverseSqrt]

theorem continuous_cutoffInverseSqrt {δ : ℝ≥0} (hδ : 0 < δ) :
    Continuous (cutoffInverseSqrt δ) :=
  NNReal.continuous_sqrt.div₀ (continuous_const.max continuous_id)
    (fun t => ne_of_gt (lt_of_lt_of_le hδ (le_max_left δ t)))

private theorem cutoffInverseSqrt_mul_self (δ t : ℝ≥0) :
    cutoffInverseSqrt δ t * t * cutoffInverseSqrt δ t =
      (t / max δ t) * (t / max δ t) := by
  simp only [cutoffInverseSqrt, div_eq_mul_inv]
  calc
    NNReal.sqrt t * (max δ t)⁻¹ * t * (NNReal.sqrt t * (max δ t)⁻¹) =
        (NNReal.sqrt t * NNReal.sqrt t) * t * ((max δ t)⁻¹ * (max δ t)⁻¹) := by
          ring
    _ = (t * (max δ t)⁻¹) * (t * (max δ t)⁻¹) := by
      rw [NNReal.mul_self_sqrt]
      ring

/-- This scalar estimate becomes the C-star norm bound for the actual link. -/
theorem cutoffInverseSqrt_mul_self_le_one {δ : ℝ≥0} (hδ : 0 < δ) (t : ℝ≥0) :
    cutoffInverseSqrt δ t * t * cutoffInverseSqrt δ t ≤ 1 := by
  rw [cutoffInverseSqrt_mul_self]
  have hratio : t / max δ t ≤ 1 :=
    (div_le_one (lt_of_lt_of_le hδ (le_max_left δ t))).mpr (le_max_right δ t)
  simpa only [one_mul] using mul_le_mul hratio hratio (by positivity) (by positivity)

/-- Above the cutoff the regularized inverse is exact; below it the positive
cutoff vanishes. This is an identity of functions, before functional calculus. -/
theorem cutoffInverseSqrt_mul_tsub {δ : ℝ≥0} (hδ : 0 < δ) (t : ℝ≥0) :
    (cutoffInverseSqrt δ t * t * cutoffInverseSqrt δ t) * (t - δ) = t - δ := by
  by_cases ht : t ≤ δ
  · simp only [tsub_eq_zero_of_le ht, mul_zero]
  · have hδt : δ ≤ t := (lt_of_not_ge ht).le
    have ht0 : t ≠ 0 := ne_of_gt (hδ.trans_le hδt)
    rw [cutoffInverseSqrt_mul_self, max_eq_right hδt, div_self ht0, one_mul, one_mul]

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- The positive cutoff of `x⋆x`, using the existing nonunital functional calculus. -/
def hereditaryCornerCutoff (x : A) (δ : ℝ≥0) : A :=
  cfcₙ (fun t : ℝ≥0 => t - δ) (star x * x)

/-- The regularized polar link, an element of the original C-star algebra. -/
def hereditaryCornerLink (x : A) (δ : ℝ≥0) : A :=
  x * cfcₙ (cutoffInverseSqrt δ) (star x * x)

theorem hereditaryCornerCutoff_nonneg (x : A) (δ : ℝ≥0) :
    0 ≤ hereditaryCornerCutoff x δ := cfcₙ_predicate _ _

theorem hereditaryCornerCutoff_ne_zero {x : A} {δ : ℝ≥0}
    (hδ : δ < ‖star x * x‖₊) : hereditaryCornerCutoff x δ ≠ 0 := by
  exact cfcₙ_tsub_ne_zero (star_mul_self_nonneg x) hδ

private theorem star_mul_hereditaryCornerLink (x : A) {δ : ℝ≥0} (hδ : 0 < δ) :
    star (hereditaryCornerLink x δ) * hereditaryCornerLink x δ =
      cfcₙ (fun t : ℝ≥0 => cutoffInverseSqrt δ t * t * cutoffInverseSqrt δ t)
        (star x * x) := by
  have hg := continuous_cutoffInverseSqrt hδ
  have hg0 := cutoffInverseSqrt_zero δ
  have hpositive : 0 ≤ cfcₙ (cutoffInverseSqrt δ) (star x * x) :=
    cfcₙ_predicate _ _
  rw [cfcₙ_mul (fun t : ℝ≥0 => cutoffInverseSqrt δ t * t) (cutoffInverseSqrt δ) (star x * x) (hg.mul continuous_id).continuousOn
      (by simp only [hg0, mul_zero]) hg.continuousOn hg0,
    cfcₙ_mul (cutoffInverseSqrt δ) (fun t : ℝ≥0 => t) (star x * x) hg.continuousOn hg0 continuous_id.continuousOn rfl,
    cfcₙ_id' ℝ≥0 (star x * x) (star_mul_self_nonneg x)]
  simp only [hereditaryCornerLink, star_mul, hpositive.star_eq, mul_assoc]

/-- The C-star identity turns the scalar bound into contractivity of the link. -/
theorem norm_hereditaryCornerLink_le_one (x : A) {δ : ℝ≥0} (hδ : 0 < δ) :
    ‖hereditaryCornerLink x δ‖ ≤ 1 := by
  have hn : ‖star (hereditaryCornerLink x δ) * hereditaryCornerLink x δ‖₊ ≤ 1 := by
    rw [star_mul_hereditaryCornerLink x hδ]
    exact nnnorm_cfcₙ_nnreal_le fun t _ => cutoffInverseSqrt_mul_self_le_one hδ t
  have hn' : ‖star (hereditaryCornerLink x δ) * hereditaryCornerLink x δ‖ ≤ (1 : ℝ) := hn
  rw [CStarRing.norm_star_mul_self] at hn'
  nlinarith only [hn', norm_nonneg (hereditaryCornerLink x δ)]

/-- The positive initial product acts as the identity on the selected cutoff. -/
theorem star_mul_hereditaryCornerLink_mul_hereditaryCornerCutoff
    (x : A) {δ : ℝ≥0} (hδ : 0 < δ) :
    star (hereditaryCornerLink x δ) * hereditaryCornerLink x δ *
      hereditaryCornerCutoff x δ = hereditaryCornerCutoff x δ := by
  have hg := continuous_cutoffInverseSqrt hδ
  have hg0 := cutoffInverseSqrt_zero δ
  have hc : Continuous (fun t : ℝ≥0 => t - δ) := by fun_prop
  rw [star_mul_hereditaryCornerLink x hδ, hereditaryCornerCutoff,
    ← cfcₙ_mul (fun t : ℝ≥0 => cutoffInverseSqrt δ t * t * cutoffInverseSqrt δ t)
      (fun t : ℝ≥0 => t - δ) (star x * x) ((hg.mul continuous_id).mul hg).continuousOn
      (by simp only [hg0, mul_zero, zero_mul]) hc.continuousOn (by simp)]
  exact cfcₙ_congr fun t _ => cutoffInverseSqrt_mul_tsub hδ t

private theorem mul_eq_zero_of_mem_hereditarySubalgebra_star_mul_self
    {x z : A} (hxx : x * x = 0) (hz : z ∈ hereditarySubalgebra (star x * x)) :
    z * x = 0 := by
  apply mul_eq_zero_of_mem_hereditarySubalgebra_right (a := star x * x) _ hz
  rw [(star_mul_self_nonneg x).star_eq, mul_assoc, hxx, mul_zero]

/-- The positive cutoff annihilates the original square-zero element. This uses
the genuine hereditary closure, not just the singly generated commutative algebra. -/
theorem hereditaryCornerCutoff_mul_eq_zero {x : A} (hxx : x * x = 0) (δ : ℝ≥0) :
    hereditaryCornerCutoff x δ * x = 0 :=
  mul_eq_zero_of_mem_hereditarySubalgebra_star_mul_self hxx
    (cfcₙ_tsub_mem_hereditarySubalgebra (star_mul_self_nonneg x) δ)

theorem hereditaryCornerCutoff_mul_hereditaryCornerLink_eq_zero
    {x : A} (hxx : x * x = 0) (δ : ℝ≥0) :
    hereditaryCornerCutoff x δ * hereditaryCornerLink x δ = 0 := by
  rw [hereditaryCornerLink, ← mul_assoc, hereditaryCornerCutoff_mul_eq_zero hxx δ,
    zero_mul]

/-- The regularized link itself has square zero. -/
theorem hereditaryCornerLink_mul_self_eq_zero {x : A}
    (hxx : x * x = 0) (δ : ℝ≥0) :
    hereditaryCornerLink x δ * hereditaryCornerLink x δ = 0 := by
  have hg : cfcₙ (cutoffInverseSqrt δ) (star x * x) ∈
      hereditarySubalgebra (star x * x) :=
    cfcₙ_nnreal_mem (𝕜 := ℂ) (cutoffInverseSqrt δ)
      (self_mem_hereditarySubalgebra (star_mul_self_nonneg x))
  have hgx := mul_eq_zero_of_mem_hereditarySubalgebra_star_mul_self hxx hg
  calc
    hereditaryCornerLink x δ * hereditaryCornerLink x δ =
        x * (cfcₙ (cutoffInverseSqrt δ) (star x * x) * x) *
          cfcₙ (cutoffInverseSqrt δ) (star x * x) := by
            simp only [hereditaryCornerLink, mul_assoc]
    _ = 0 := by rw [hgx, mul_zero, zero_mul]

/-- The cutoff remains in any closed hereditary algebra containing `x`. -/
theorem hereditaryCornerCutoff_mem_hereditarySubalgebra {a x : A}
    (hx : x ∈ hereditarySubalgebra a) (δ : ℝ≥0) :
    hereditaryCornerCutoff x δ ∈ hereditarySubalgebra a :=
  cfcₙ_nnreal_mem (𝕜 := ℂ) (fun t : ℝ≥0 => t - δ)
    ((hereditarySubalgebra a).mul_mem (show star x ∈ hereditarySubalgebra a from star_mem hx) hx)

/-- The link is an actual element of the same parent hereditary algebra. -/
theorem hereditaryCornerLink_mem_hereditarySubalgebra {a x : A}
    (hx : x ∈ hereditarySubalgebra a) (δ : ℝ≥0) :
    hereditaryCornerLink x δ ∈ hereditarySubalgebra a :=
  (hereditarySubalgebra a).mul_mem hx
    (cfcₙ_nnreal_mem (𝕜 := ℂ) (s := hereditarySubalgebra a) (cutoffInverseSqrt δ)
      ((hereditarySubalgebra a).mul_mem (show star x ∈ hereditarySubalgebra a from star_mem hx) hx))

/-- The target positive generator is nonzero because inverse conjugation sends
it back to the nonzero cutoff. -/
theorem hereditaryCornerLink_conjugate_ne_zero {x : A} {δ : ℝ≥0}
    (hδ : 0 < δ) (hδx : δ < ‖star x * x‖₊) :
    hereditaryCornerLink x δ * hereditaryCornerCutoff x δ *
      star (hereditaryCornerLink x δ) ≠ 0 := by
  intro hz
  have h := star_mul_conjugate_mul_eq
    (hereditaryCornerCutoff_nonneg x δ).isSelfAdjoint
    (star_mul_hereditaryCornerLink_mul_hereditaryCornerCutoff x hδ)
  rw [hz, mul_zero, zero_mul] at h
  exact hereditaryCornerCutoff_ne_zero hδx h.symm

/-- An actual square-zero element yields two orthogonal nonzero positive
hereditary generators linked by a contraction in the same parent corner.
The two maps between their full hereditary algebras are supplied by
`hereditaryConjugateEquiv`; no matrix units in the ambient algebra are assumed. -/
theorem exists_contractive_hereditary_corner_link_of_square_zero
    {a x : A} (hxa : x ∈ hereditarySubalgebra a) (hx : x ≠ 0) (hxx : x * x = 0) :
    ∃ c v : A, c ∈ hereditarySubalgebra a ∧ v ∈ hereditarySubalgebra a ∧
      0 ≤ c ∧ c ≠ 0 ∧ ‖v‖ ≤ 1 ∧ v * v = 0 ∧ star v * v * c = c ∧ c * v = 0 ∧
      v * c * star v ∈ hereditarySubalgebra a ∧ 0 ≤ v * c * star v ∧
      v * c * star v ≠ 0 ∧ c * (v * c * star v) = 0 ∧ (v * c * star v) * c = 0 := by
  have hp : star x * x ≠ 0 := fun h => hx (star_mul_self_eq_zero.mp h)
  have hnp : (0 : ℝ≥0) < ‖star x * x‖₊ := by
    exact pos_iff_ne_zero.mpr (fun h => hp (nnnorm_eq_zero.mp h))
  obtain ⟨δ, hδ, hδx⟩ := exists_between hnp
  let c := hereditaryCornerCutoff x δ
  let v := hereditaryCornerLink x δ
  have hc : 0 ≤ c := hereditaryCornerCutoff_nonneg x δ
  have hc_mem : c ∈ hereditarySubalgebra a := hereditaryCornerCutoff_mem_hereditarySubalgebra hxa δ
  have hv_mem : v ∈ hereditarySubalgebra a := hereditaryCornerLink_mem_hereditarySubalgebra hxa δ
  have hcv : c * v = 0 := hereditaryCornerCutoff_mul_hereditaryCornerLink_eq_zero hxx δ
  have hq : 0 ≤ v * c * star v := star_right_conjugate_nonneg hc v
  have hcq : c * (v * c * star v) = 0 := by
    calc
      c * (v * c * star v) = (c * v) * c * star v := by simp only [mul_assoc]
      _ = 0 := by rw [hcv, zero_mul, zero_mul]
  refine ⟨c, v, hc_mem, hv_mem, hc, hereditaryCornerCutoff_ne_zero hδx,
    norm_hereditaryCornerLink_le_one x hδ, hereditaryCornerLink_mul_self_eq_zero hxx δ,
    star_mul_hereditaryCornerLink_mul_hereditaryCornerCutoff x hδ, hcv,
    (hereditarySubalgebra a).mul_mem ((hereditarySubalgebra a).mul_mem hv_mem hc_mem)
      (show star v ∈ hereditarySubalgebra a from star_mem hv_mem), hq, hereditaryCornerLink_conjugate_ne_zero hδ hδx, hcq, ?_⟩
  have h := congrArg star hcq
  rw [star_mul, hq.star_eq, hc.star_eq, star_zero] at h
  exact h

/-- Every nonzero hereditary algebra in an antiliminal algebra has an actual
contractive link to an orthogonal nonzero hereditary corner. -/
theorem IsAntiliminal.exists_contractive_hereditary_corner_link
    (hA : IsAntiliminal A) {a : A} (ha : a ≠ 0) :
    ∃ c v : A, c ∈ hereditarySubalgebra a ∧ v ∈ hereditarySubalgebra a ∧
      0 ≤ c ∧ c ≠ 0 ∧ ‖v‖ ≤ 1 ∧ v * v = 0 ∧ star v * v * c = c ∧ c * v = 0 ∧
      v * c * star v ∈ hereditarySubalgebra a ∧ 0 ≤ v * c * star v ∧
      v * c * star v ≠ 0 ∧ c * (v * c * star v) = 0 ∧ (v * c * star v) * c = 0 := by
  obtain ⟨x, hx_mem, hx, hxx⟩ :=
    hA.exists_ne_zero_mul_self_eq_zero_mem_hereditarySubalgebra ha
  exact exists_contractive_hereditary_corner_link_of_square_zero hx_mem hx hxx

end MathlibAnnex.Analysis.CStarAlgebra
