/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Topology.MetricSpace.CardinalTotallyBounded
import MathlibAnnex.Analysis.Normed.Operator.CompactIdeal
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Cardinal-compact operators defined by bounded images

The predicate uses the existing internal-center metric net condition on EVERY
bounded set. It does not use the dimension of an operator range or its closure.
The carrier and operator norm are inherited from continuous linear maps.
Completeness is needed for the converse comparison with `IsCompactOperator`,
not for cardinal nets, operations, or norm closedness.

The algebraic closure results assume an infinite cardinal bound. Bounds zero
and one are treated separately; even the zero map does not satisfy them on a
nonempty domain. No countable union of small nets is taken.
-/

set_option autoImplicit false
noncomputable section
open Set Metric Bornology
open scoped Cardinal Topology

universe u v w z

/-- A map is cardinal compact if every bounded set has an image admitting
internal epsilon nets with strictly fewer than `α` centers. -/
def IsCardinalCompactOperator {E : Type u} {F : Type v}
    [PseudoMetricSpace E] [PseudoMetricSpace F] (α : Cardinal.{w}) (f : E → F) : Prop :=
  ∀ s : Set E, Bornology.IsBounded s → Metric.CardinalTotallyBounded α (f '' s)

section MetricMaps

variable {E : Type u} {F : Type v} {G : Type z}
variable [PseudoMetricSpace E] [PseudoMetricSpace F] [PseudoMetricSpace G]
variable {α β : Cardinal.{w}} {f : E → F}

/-- Increasing the allowed number of centers preserves cardinal compactness. -/
theorem IsCardinalCompactOperator.mono_cardinal (hf : IsCardinalCompactOperator α f)
    (hαβ : α ≤ β) : IsCardinalCompactOperator β f :=
  fun s hs => (hf s hs).mono_cardinal hαβ

/-- A uniformly continuous postcomposition preserves the same bound. -/
theorem IsCardinalCompactOperator.uniformContinuous_comp
    (hf : IsCardinalCompactOperator α f) {g : F → G} (hg : UniformContinuous g) :
    IsCardinalCompactOperator α (g ∘ f) := by
  intro s hs
  simpa only [Set.image_image, Function.comp_def] using (hf s hs).image hg

/-- Precomposition only needs to send bounded sets to bounded sets. -/
theorem IsCardinalCompactOperator.comp_of_isBounded_image
    (hf : IsCardinalCompactOperator α f) {g : G → E}
    (hg : ∀ s : Set G, Bornology.IsBounded s → Bornology.IsBounded (g '' s)) :
    IsCardinalCompactOperator α (f ∘ g) := by
  intro s hs
  simpa only [Set.image_image, Function.comp_def] using hf (g '' s) (hg s hs)

/-- Constants are allowed as soon as one center is strictly below the bound. -/
theorem isCardinalCompactOperator_const (hα : 1 < α) (y : F) :
    IsCardinalCompactOperator α (fun _ : E => y) := by
  intro s hs
  apply (Metric.cardinalTotallyBounded_singleton hα y).subset
  rintro _ ⟨x, hx, rfl⟩
  exact Set.mem_singleton y

/-- Bound zero is impossible, even if the domain is empty. -/
theorem not_isCardinalCompactOperator_zero_cardinal (f : E → F) :
    ¬ IsCardinalCompactOperator (0 : Cardinal.{w}) f := by
  intro hf
  exact Metric.not_cardinalTotallyBounded_zero _ (hf ∅ isBounded_empty)

/-- On a nonempty domain, a bound of one cannot cover the image of a singleton. -/
theorem not_isCardinalCompactOperator_one [Nonempty E] (f : E → F) :
    ¬ IsCardinalCompactOperator (1 : Cardinal.{w}) f := by
  intro hf
  let x : E := Classical.arbitrary E
  have hne : (f '' ({x} : Set E)).Nonempty := ⟨f x, x, Set.mem_singleton x, rfl⟩
  exact Metric.not_cardinalTotallyBounded_one hne (hf {x} isBounded_singleton)

end MetricMaps

section AdditiveMaps

variable {E : Type u} [PseudoMetricSpace E]
variable {F : Type v} [NormedAddCommGroup F]
variable {α : Cardinal.{w}} {f g : E → F}

/-- Zero is included for infinite bounds. No completeness is needed. -/
theorem isCardinalCompactOperator_zero (hα : Cardinal.aleph0 ≤ α) :
    IsCardinalCompactOperator α (0 : E → F) :=
  isCardinalCompactOperator_const (Cardinal.one_lt_aleph0.trans_le hα) 0

/-- Negation is a uniformly continuous postcomposition. -/
theorem IsCardinalCompactOperator.neg (hf : IsCardinalCompactOperator α f) :
    IsCardinalCompactOperator α (-f) := by
  change IsCardinalCompactOperator α (fun x => -f x)
  simpa only [Function.comp_def, Pi.neg_apply] using
    hf.uniformContinuous_comp (g := fun y : F => -y) uniformContinuous_id.neg

/-- Addition uses a product of two nets and the uniformly continuous addition map. -/
theorem IsCardinalCompactOperator.add (hf : IsCardinalCompactOperator α f)
    (hg : IsCardinalCompactOperator α g) (hα : Cardinal.aleph0 ≤ α) :
    IsCardinalCompactOperator α (f + g) := by
  intro s hs
  have hprod := (hf s hs).prod (hg s hs) hα
  have hsum : Metric.CardinalTotallyBounded α
      ((fun p : F × F => p.1 + p.2) '' ((f '' s) ×ˢ (g '' s))) :=
    hprod.image (uniformContinuous_fst.add uniformContinuous_snd)
  apply hsum.subset
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨(f x, g x), ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩, rfl⟩

/-- Subtraction has the same cardinal bound. -/
theorem IsCardinalCompactOperator.sub (hf : IsCardinalCompactOperator α f)
    (hg : IsCardinalCompactOperator α g) (hα : Cardinal.aleph0 ≤ α) :
    IsCardinalCompactOperator α (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg hα

end AdditiveMaps

section ScalarMaps

variable {E : Type u} [PseudoMetricSpace E]
variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {α : Cardinal.{w}} {f : E → F}

/-- Scalar multiplication is permitted even for scalar zero; the hypothesis
already supplies an admissible net bound. -/
theorem IsCardinalCompactOperator.smul (hf : IsCardinalCompactOperator α f) (c : 𝕜) :
    IsCardinalCompactOperator α (c • f) := by
  change IsCardinalCompactOperator α (fun x => c • f x)
  let m : F →L[𝕜] F := c • ContinuousLinearMap.id 𝕜 F
  simpa only [Function.comp_def, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.smul_apply, m] using
      hf.uniformContinuous_comp m.uniformContinuous

/-- Nonzero scalar multiplication also reflects the predicate. -/
theorem isCardinalCompactOperator_smul_iff {c : 𝕜} (hc : c ≠ 0) :
    IsCardinalCompactOperator α (c • f) ↔ IsCardinalCompactOperator α f := by
  constructor
  · intro h
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h.smul c⁻¹
  · exact fun h => h.smul c

end ScalarMaps

section SemilinearUnitBall

variable {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace 𝕜₁ E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]
variable {σ : 𝕜₁ →+* 𝕜₂} {α : Cardinal.{w}}

/-- The bounded-image condition is determined by the closed unit ball.
This characterization is algebraic semilinear: continuity of `f` is not needed. -/
theorem isCardinalCompactOperator_iff_image_closedBall (f : E →ₛₗ[σ] F) :
    IsCardinalCompactOperator α f ↔
      Metric.CardinalTotallyBounded α (f '' Metric.closedBall 0 1) := by
  constructor
  · intro hf
    exact hf _ isBounded_closedBall
  · intro hball s hs
    obtain ⟨R, hR, hbound⟩ := hs.exists_pos_norm_le
    obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜₁ R
    have hcpos : 0 < ‖c‖ := hR.trans hc
    have hc0 : c ≠ 0 := norm_pos_iff.mp hcpos
    let m : F →L[𝕜₂] F := (σ c) • ContinuousLinearMap.id 𝕜₂ F
    apply (hball.image m.uniformContinuous).subset
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨f (c⁻¹ • x), ⟨c⁻¹ • x, ?_, rfl⟩, ?_⟩
    · have hdiv : ‖x‖ / ‖c‖ ≤ 1 :=
        (div_le_one hcpos).mpr ((hbound x hx).trans hc.le)
      simpa only [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv,
        div_eq_inv_mul] using hdiv
    · change σ c • f (c⁻¹ • x) = f x
      rw [map_smulₛₗ, smul_smul, ← map_mul, mul_inv_cancel₀ hc0, map_one, one_smul]

/-- Ordinary compactness implies the aleph-zero bounded-image condition without
requiring completeness of the target. -/
theorem IsCompactOperator.isCardinalCompactOperator {f : E →ₛₗ[σ] F}
    (hf : IsCompactOperator f) :
    IsCardinalCompactOperator (Cardinal.aleph0 : Cardinal.{w}) f := by
  intro s hs
  obtain ⟨K, hK, hsub⟩ := hf.image_subset_compact_of_bounded hs
  exact Metric.cardinalTotallyBounded_aleph0_iff.mpr (hK.totallyBounded.subset hsub)

/-- A complete target converts totally bounded images into relatively compact images.
Completeness occurs only in this converse comparison. -/
theorem isCardinalCompactOperator_aleph0_iff [CompleteSpace F] (f : E →ₛₗ[σ] F) :
    IsCardinalCompactOperator (Cardinal.aleph0 : Cardinal.{w}) f ↔ IsCompactOperator f := by
  constructor
  · intro hf
    have hb : TotallyBounded (f '' Metric.closedBall 0 1) :=
      Metric.cardinalTotallyBounded_aleph0_iff.mp (hf _ isBounded_closedBall)
    apply (isCompactOperator_iff_isCompact_closure_image_closedBall f zero_lt_one).mpr
    exact hb.closure.isCompact_of_isComplete isClosed_closure.isComplete
  · exact fun hf => hf.isCardinalCompactOperator

end SemilinearUnitBall

section ContinuousSemilinear

variable {𝕜₁ 𝕜₂ 𝕜₃ : Type*}
variable [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
variable [NontriviallyNormedField 𝕜₃]
variable {E : Type u} {F : Type v} {G : Type z}
variable [NormedAddCommGroup E] [NormedSpace 𝕜₁ E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜₃ G]
variable {σ : 𝕜₁ →+* 𝕜₂} {τ : 𝕜₂ →+* 𝕜₃} {υ : 𝕜₁ →+* 𝕜₃}
variable [RingHomCompTriple σ τ υ]
variable {α : Cardinal.{w}}

/-- Postcomposition by an actual bounded semilinear map. -/
theorem IsCardinalCompactOperator.clm_comp [RingHomIsometric τ] {f : E →SL[σ] F}
    (hf : IsCardinalCompactOperator α f) (g : F →SL[τ] G) :
    IsCardinalCompactOperator α (g.comp f : E →SL[υ] G) :=
  hf.uniformContinuous_comp g.lipschitz.uniformContinuous

/-- Precomposition uses the bounded-image property of the actual continuous map. -/
theorem IsCardinalCompactOperator.comp_clm [RingHomIsometric σ] {g : F →SL[τ] G}
    (hg : IsCardinalCompactOperator α g) (f : E →SL[σ] F) :
    IsCardinalCompactOperator α (g.comp f : E →SL[υ] G) :=
  hg.comp_of_isBounded_image (fun s hs => f.lipschitz.isBounded_image hs)

end ContinuousSemilinear

section NormClosure

variable {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace 𝕜₁ E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]
variable {σ : 𝕜₁ →+* 𝕜₂} [hσ : RingHomIsometric σ] {α : Cardinal.{w}}

include hσ in
/-- The cardinal-compact maps form an operator-norm closed set for EVERY bound.
At each radius choose one nearby operator, then recenter its net in the limit
image. Neither target completeness nor regularity of `α` is used. -/
theorem isClosed_setOf_isCardinalCompactOperator :
    IsClosed {T : E →SL[σ] F | IsCardinalCompactOperator α T} := by
  apply isClosed_of_closure_subset
  intro T hT s hs
  apply Metric.cardinalTotallyBounded_image_of_uniform_approximation
  intro η hη
  obtain ⟨R, hR, hbound⟩ := hs.exists_pos_norm_le
  have hsmall : 0 < η / (R + 1) := div_pos hη (by positivity)
  obtain ⟨A, hA, hTA⟩ := Metric.mem_closure_iff.mp hT (η / (R + 1)) hsmall
  refine ⟨A, hA s hs, ?_⟩
  intro x hx
  have hop : ‖T - A‖ < η / (R + 1) := by simpa only [dist_eq_norm, norm_sub_rev] using hTA
  have hmul : ‖T - A‖ * (R + 1) < η := (lt_div_iff₀ (by positivity)).mp hop
  calc
    dist (T x) (A x) = ‖(T - A) x‖ := by
      rw [dist_eq_norm, ContinuousLinearMap.sub_apply]
    _ ≤ ‖T - A‖ * ‖x‖ := (T - A).le_opNorm x
    _ ≤ ‖T - A‖ * R := mul_le_mul_of_nonneg_left (hbound x hx) (norm_nonneg _)
    _ ≤ η := by nlinarith [norm_nonneg (T - A)]

include hσ in
/-- Consequently all norm limits, not just sequential limits, stay cardinal compact. -/
theorem IsCardinalCompactOperator.of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {T : ι → E →SL[σ] F} {S : E →SL[σ] F}
    (hT : ∀ i, IsCardinalCompactOperator α (T i)) (hlim : Filter.Tendsto T l (𝓝 S)) :
    IsCardinalCompactOperator α S :=
  isClosed_setOf_isCardinalCompactOperator.mem_of_tendsto hlim
    (Filter.Eventually.of_forall hT)

end NormClosure

namespace ContinuousLinearMap

section Submodule

variable {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace 𝕜₁ E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]
variable (α : Cardinal.{w}) (σ : 𝕜₁ →+* 𝕜₂) [hσ : RingHomIsometric σ]

/-- Cardinal-compact operators as an actual submodule of bounded semilinear maps. -/
def cardinalCompactOperator (hα : Cardinal.aleph0 ≤ α) : Submodule 𝕜₂ (E →SL[σ] F) where
  carrier := {T | IsCardinalCompactOperator α T}
  zero_mem' := isCardinalCompactOperator_zero hα
  add_mem' := fun hT hS => hT.add hS hα
  smul_mem' := fun c {T} hT => hT.smul c

@[simp]
theorem mem_cardinalCompactOperator (hα : Cardinal.aleph0 ≤ α) (T : E →SL[σ] F) :
    T ∈ cardinalCompactOperator (E := E) (F := F) α σ hα ↔
      IsCardinalCompactOperator α T := Iff.rfl

/-- The submodule uses the original operator norm, not a cardinal-dependent norm. -/
theorem norm_cardinalCompactOperator (hα : Cardinal.aleph0 ≤ α)
    (T : cardinalCompactOperator (E := E) (F := F) α σ hα) :
    ‖T‖ = ‖(T : E →SL[σ] F)‖ := rfl

include hσ in
/-- Closedness of the actual submodule does not assume a complete target. -/
theorem isClosed_cardinalCompactOperator (hα : Cardinal.aleph0 ≤ α) :
    IsClosed (cardinalCompactOperator (E := E) (F := F) α σ hα : Set (E →SL[σ] F)) :=
  isClosed_setOf_isCardinalCompactOperator

/-- Only the complete-target comparison identifies this submodule with ordinary compacts. -/
theorem cardinalCompactOperator_aleph0_eq [CompleteSpace F] :
    cardinalCompactOperator (E := E) (F := F) (Cardinal.aleph0 : Cardinal.{w}) σ le_rfl =
      compactOperator σ E F := by
  ext T
  exact isCardinalCompactOperator_aleph0_iff T.toLinearMap

end Submodule

section Ideal

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A closed two-sided operator ideal for any infinite cardinal bound. -/
def cardinalCompactOperatorIdeal (α : Cardinal.{w}) (hα : Cardinal.aleph0 ≤ α) :
    TwoSidedIdeal (E →L[𝕜] E) :=
  TwoSidedIdeal.mk' {T | IsCardinalCompactOperator α T}
    (isCardinalCompactOperator_zero hα)
    (fun {T S} hT hS => hT.add hS hα)
    (fun {T} hT => hT.neg)
    (fun {T S} hS => hS.clm_comp T)
    (fun {T S} hT => hT.comp_clm S)

@[simp]
theorem mem_cardinalCompactOperatorIdeal (α : Cardinal.{w}) (hα : Cardinal.aleph0 ≤ α)
    (T : E →L[𝕜] E) :
    T ∈ cardinalCompactOperatorIdeal (𝕜 := 𝕜) (E := E) α hα ↔
      IsCardinalCompactOperator α T := by
  simp only [cardinalCompactOperatorIdeal, TwoSidedIdeal.mem_mk', Set.mem_setOf_eq]

/-- The ideal and submodule have exactly the same carrier. -/
theorem coe_cardinalCompactOperatorIdeal (α : Cardinal.{w}) (hα : Cardinal.aleph0 ≤ α) :
    (cardinalCompactOperatorIdeal (𝕜 := 𝕜) (E := E) α hα : Set (E →L[𝕜] E)) =
      (cardinalCompactOperator (E := E) (F := E) α (RingHom.id 𝕜) hα :
        Set (E →L[𝕜] E)) := by
  ext T
  exact mem_cardinalCompactOperatorIdeal α hα T

/-- Norm closedness of the literal ideal carrier. -/
theorem isClosed_cardinalCompactOperatorIdeal (α : Cardinal.{w})
    (hα : Cardinal.aleph0 ≤ α) :
    IsClosed (cardinalCompactOperatorIdeal (𝕜 := 𝕜) (E := E) α hα : Set (E →L[𝕜] E)) := by
  simpa only [cardinalCompactOperatorIdeal, TwoSidedIdeal.coe_mk'] using
    (isClosed_setOf_isCardinalCompactOperator (σ := RingHom.id 𝕜) (α := α)
      (E := E) (F := E))

/-- Inclusion of actual ideals under a larger cardinal bound. -/
theorem cardinalCompactOperatorIdeal_mono {α β : Cardinal.{w}}
    (hα : Cardinal.aleph0 ≤ α) (hβ : Cardinal.aleph0 ≤ β) (hαβ : α ≤ β) :
    cardinalCompactOperatorIdeal (𝕜 := 𝕜) (E := E) α hα ≤
      cardinalCompactOperatorIdeal (𝕜 := 𝕜) (E := E) β hβ := by
  intro T hT
  exact (mem_cardinalCompactOperatorIdeal β hβ T).mpr
    (((mem_cardinalCompactOperatorIdeal α hα T).mp hT).mono_cardinal hαβ)

/-- In real or complex Banach spaces the aleph-zero ideal is the previously
constructed compact ideal, with no new compact predicate. -/
theorem cardinalCompactOperatorIdeal_aleph0_eq
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] :
    cardinalCompactOperatorIdeal (𝕜 := 𝕜) (E := E)
      (Cardinal.aleph0 : Cardinal.{w}) le_rfl = compactOperatorIdeal 𝕜 E := by
  apply SetLike.coe_injective
  ext T
  exact (mem_cardinalCompactOperatorIdeal _ le_rfl T).trans
    ((isCardinalCompactOperator_aleph0_iff T.toLinearMap).trans
      (mem_compactOperatorIdeal T).symm)

end Ideal
end ContinuousLinearMap
