/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.HilbertBasisCardinalNets
import MathlibAnnex.Analysis.InnerProductSpace.OperatorCutoffReal
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Cardinal compactness and closed subspaces of the literal operator range

The forward implication restricts the actual operator to the closed preimage of a
closed target submodule. Banach's open mapping theorem then supplies bounded lifts.
For the reverse implication one uses the supplied two-threshold cutoff, whose literal
image is closed, and recenters a net for a single small-residual approximation.

The final real and complex theorems instantiate that analytic bridge with the actual
cutoff theorems. No assumption on a bounded inverse of the original operator, no
closedness of its full range, and no regularity of the cardinal are used. Basis indices
in the equivalence live in the target universe, where Hilbert bases are known to exist;
the forward comparison separately permits arbitrary index universes.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Bornology
open scoped Cardinal Topology

universe uF uH uK uI uA
namespace ContinuousLinearMap

variable {𝕜 : Type uF} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [hH : CompleteSpace H]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [hK : CompleteSpace K]

include hH hK in
/-- Restricting to the preimage of a closed submodule in the literal range gives
bounded lifts. The original operator need not have closed range or be injective. -/
theorem exists_preimage_norm_le_of_closed_submodule_le_range
    (T : H →L[𝕜] K) (M : Submodule 𝕜 K)
    (hM : IsClosed (M : Set K)) (hMT : M ≤ T.range) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : M, ∃ x : H,
      T x = (y : K) ∧ ‖x‖ ≤ C * ‖y‖ := by
  let D : Submodule 𝕜 H := M.comap T.toLinearMap
  have hD : IsClosed (D : Set H) := hM.preimage T.continuous
  letI : CompleteSpace D := hD.completeSpace_coe
  letI : CompleteSpace M := hM.completeSpace_coe
  let q₀ : D →ₗ[𝕜] M :=
    { toFun := fun x => ⟨T x, x.property⟩
      map_add' := by intro x y; apply Subtype.ext; exact map_add T (x : H) (y : H)
      map_smul' := by intro c x; apply Subtype.ext; exact map_smul T c (x : H) }
  let q : D →L[𝕜] M := q₀.mkContinuous ‖T‖ (fun x => T.le_opNorm x)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := hMT y.property
    change T x = (y : K) at hx
    have hxD : x ∈ D := by
      change T x ∈ M
      rw [hx]
      exact y.property
    exact ⟨⟨x, hxD⟩, Subtype.ext hx⟩
  obtain ⟨C, hC, hlift⟩ := q.exists_preimage_norm_le (σ' := RingHom.id 𝕜) hq
  refine ⟨C, hC, ?_⟩
  intro y
  obtain ⟨x, hx, hnorm⟩ := hlift y
  exact ⟨x, congrArg Subtype.val hx, hnorm⟩

include hH hK in
/-- The unit ball of a closed submodule in the range is covered by one bounded
source ball, followed by the actual orthogonal projection onto that submodule. -/
theorem cardinalTotallyBounded_closedBall_of_closed_submodule_le_range
    (T : H →L[𝕜] K) {α : Cardinal.{uA}} (hT : IsCardinalCompactOperator α T)
    (M : Submodule 𝕜 K) (hM : IsClosed (M : Set K)) (hMT : M ≤ T.range) :
    Metric.CardinalTotallyBounded α (Metric.closedBall (0 : M) 1) := by
  letI : CompleteSpace M := hM.completeSpace_coe
  obtain ⟨C, hC, hlift⟩ := T.exists_preimage_norm_le_of_closed_submodule_le_range M hM hMT
  have hn := (hT (Metric.closedBall (0 : H) C) isBounded_closedBall).image
    (f := M.orthogonalProjectionOnto) M.orthogonalProjectionOnto.uniformContinuous
  apply hn.subset
  intro y hy
  have hy1 : ‖y‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  obtain ⟨x, hx, hnorm⟩ := hlift y
  have hxB : x ∈ Metric.closedBall (0 : H) C := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hnorm.trans (by nlinarith)
  refine ⟨T x, ⟨x, hxB, rfl⟩, ?_⟩
  simp only [hx, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

include hH hK in
/-- Necessity for any chosen Hilbert basis, including indices in a separate universe. -/
theorem hilbertBasis_lift_mk_lt_of_isCardinalCompactOperator
    (T : H →L[𝕜] K) {α : Cardinal.{uA}} (hT : IsCardinalCompactOperator α T)
    (M : Submodule 𝕜 K) (hM : IsClosed (M : Set K)) (hMT : M ≤ T.range)
    {ι : Type uI} (b : HilbertBasis ι 𝕜 M) :
    Cardinal.lift.{uA} (#ι) < Cardinal.lift.{uI} α :=
  b.lift_mk_lt_of_cardinalTotallyBounded_closedBall
    (T.cardinalTotallyBounded_closedBall_of_closed_submodule_le_range hT M hM hMT)

include hK in
/-- The small-basis condition provides nets for every bounded subset of each
closed submodule in the range. Hilbert basis existence occurs in the target universe. -/
theorem cardinalTotallyBounded_of_forall_closed_submodule_hilbertBasis
    (T : H →L[𝕜] K) {α : Cardinal.{uA}} (hα : Cardinal.aleph0 ≤ α)
    (hdim : ∀ M : Submodule 𝕜 K, IsClosed (M : Set K) → M ≤ T.range →
      ∀ (ι : Type uK) (b : HilbertBasis ι 𝕜 M),
        Cardinal.lift.{uA} (#ι) < Cardinal.lift.{uK} α)
    (M : Submodule 𝕜 K) (hM : IsClosed (M : Set K)) (hMT : M ≤ T.range)
    {s : Set M} (hs : Bornology.IsBounded s) : Metric.CardinalTotallyBounded α s := by
  letI : CompleteSpace M := hM.completeSpace_coe
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 M
  exact b.cardinalTotallyBounded_of_isBounded hα (hdim M hM hMT w b) hs

include hH hK in
/-- Analytic bridge from an actual two-threshold cutoff to the literal-range
criterion. Both unconditional field-specific cutoffs are applied below. -/
theorem isCardinalCompactOperator_of_closed_submodule_hilbertBasis_of_cutoff
    (T : H →L[𝕜] K) {α : Cardinal.{uA}} (hα : Cardinal.aleph0 ≤ α)
    (hdim : ∀ M : Submodule 𝕜 K, IsClosed (M : Set K) → M ≤ T.range →
      ∀ (ι : Type uK) (b : HilbertBasis ι 𝕜 M),
        Cardinal.lift.{uA} (#ι) < Cardinal.lift.{uK} α)
    (hcut : ∀ η : ℝ, 0 < η → ∃ S : Submodule 𝕜 H,
      IsClosed (S : Set H) ∧
      (∀ x ∈ Sᗮ, ‖T x‖ ≤ (η / 2) * ‖x‖) ∧ IsClosed (T '' (S : Set H))) :
    IsCardinalCompactOperator α T := by
  classical
  apply (isCardinalCompactOperator_iff_image_closedBall (α := α) T.toLinearMap).mpr
  apply Metric.cardinalTotallyBounded_image_of_uniform_approximation
    (α := α) (s := Metric.closedBall (0 : H) 1) (f := T)
  intro η hη
  obtain ⟨S, hS, hsmall, hTS⟩ := hcut η hη
  letI : CompleteSpace S := hS.completeSpace_coe
  let M : Submodule 𝕜 K := S.map T.toLinearMap
  have hM : IsClosed (M : Set K) := hTS
  have hMT : M ≤ T.range := by
    rintro y ⟨x, hxS, rfl⟩
    exact ⟨x, rfl⟩
  let g : H →L[𝕜] K := T.comp S.starProjection
  let p₀ : H →ₗ[𝕜] M :=
    { toFun := fun x => ⟨g x, S.starProjection x,
        (S.orthogonalProjectionOnto x).property, rfl⟩
      map_add' := by intro x y; apply Subtype.ext; exact map_add g x y
      map_smul' := by intro c x; apply Subtype.ext; exact map_smul g c x }
  let p : H →L[𝕜] M := p₀.mkContinuous ‖g‖ (fun x => g.le_opNorm x)
  have hpbounded : Bornology.IsBounded (p '' Metric.closedBall (0 : H) 1) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨‖p‖, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    have hx1 : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    exact (p.le_opNorm x).trans (by nlinarith [norm_nonneg p])
  have hn := T.cardinalTotallyBounded_of_forall_closed_submodule_hilbertBasis
    hα hdim M hM hMT hpbounded
  have hi := hn.image (f := M.subtypeL) M.subtypeL.uniformContinuous
  have heq : M.subtypeL '' (p '' Metric.closedBall (0 : H) 1) =
      g '' Metric.closedBall (0 : H) 1 := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨p x, ⟨x, hx, rfl⟩, rfl⟩
  rw [heq] at hi
  refine ⟨g, hi, ?_⟩
  intro x hx
  have hx1 : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hrS : x - S.starProjection x ∈ Sᗮ :=
    Submodule.sub_starProjection_mem_orthogonal x
  have hrnorm : ‖x - S.starProjection x‖ ≤ ‖x‖ := by
    simpa only [Submodule.starProjection_orthogonal_val] using
      Sᗮ.norm_starProjection_apply_le x
  calc
    dist (T x) (g x) = ‖T (x - S.starProjection x)‖ := by
      simp only [dist_eq_norm, map_sub, g, ContinuousLinearMap.comp_apply]
    _ ≤ (η / 2) * ‖x - S.starProjection x‖ := hsmall _ hrS
    _ ≤ η := by nlinarith [norm_nonneg (x - S.starProjection x)]

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {H : Type uH} [NormedAddCommGroup H] [hH : CompleteSpace H]
variable {K : Type uK} [NormedAddCommGroup K] [hK : CompleteSpace K]

include hH hK in
/-- Real Hilbert-space range characterization with no cutoff or open-mapping
assumption left over. The range is literal, not its norm closure. -/
theorem isCardinalCompactOperator_iff_forall_closed_submodule_real
    [InnerProductSpace ℝ H] [InnerProductSpace ℝ K]
    (T : H →L[ℝ] K) {α : Cardinal.{uA}} (hα : Cardinal.aleph0 ≤ α) :
    IsCardinalCompactOperator α T ↔
      ∀ M : Submodule ℝ K, IsClosed (M : Set K) → M ≤ T.range →
        ∀ (ι : Type uK) (b : HilbertBasis ι ℝ M),
          Cardinal.lift.{uA} (#ι) < Cardinal.lift.{uK} α := by
  constructor
  · intro hT M hM hMT ι b
    exact T.hilbertBasis_lift_mk_lt_of_isCardinalCompactOperator hT M hM hMT b
  · intro hdim
    apply T.isCardinalCompactOperator_of_closed_submodule_hilbertBasis_of_cutoff hα hdim
    intro η hη
    obtain ⟨S, hS, -, hu, -, him⟩ := T.exists_closed_submodule_two_threshold_cutoff_real (ε := η) hη
    exact ⟨S, hS, hu, him⟩

include hH hK in
/-- Complex Hilbert-space range characterization. Separate basis universes are
available through `hilbertBasis_lift_mk_lt_of_isCardinalCompactOperator`. -/
theorem isCardinalCompactOperator_iff_forall_closed_submodule_complex
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    (T : H →L[ℂ] K) {α : Cardinal.{uA}} (hα : Cardinal.aleph0 ≤ α) :
    IsCardinalCompactOperator α T ↔
      ∀ M : Submodule ℂ K, IsClosed (M : Set K) → M ≤ T.range →
        ∀ (ι : Type uK) (b : HilbertBasis ι ℂ M),
          Cardinal.lift.{uA} (#ι) < Cardinal.lift.{uK} α := by
  constructor
  · intro hT M hM hMT ι b
    exact T.hilbertBasis_lift_mk_lt_of_isCardinalCompactOperator hT M hM hMT b
  · intro hdim
    apply T.isCardinalCompactOperator_of_closed_submodule_hilbertBasis_of_cutoff hα hdim
    intro η hη
    obtain ⟨S, hS, -, hu, -, him⟩ := T.exists_closed_submodule_two_threshold_cutoff_complex (ε := η) hη
    exact ⟨S, hS, hu, him⟩

end ContinuousLinearMap
