/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.HilbertBasisCardinality
import MathlibAnnex.Analysis.Normed.Operator.CardinalCompact
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.NhdsWithin
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Tactic

/-!
# Hilbert basis cardinality and internal nets in bounded balls

For an infinite basis, finite rational/Gaussian-rational coefficient families give
one dense set of cardinality at most the basis index cardinal. This argument never
unites countably many independently small cardinal bounds. A finite basis is handled
by compactness of bounded closed sets in finite dimension, not by total boundedness
of the whole vector space. All cardinal comparisons use actual Hilbert basis indices.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Bornology
open scoped BigOperators Cardinal Topology

universe uF uI uH uA
namespace HilbertBasis

variable {𝕜 : Type uF} [RCLike 𝕜]
variable {ι : Type uI} {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- A finite-support rational coefficient family evaluated in the given Hilbert basis. -/
def rationalSpanSum (b : HilbertBasis ι 𝕜 H)
    (a : Σ s : Finset ι, s → ℚ × ℚ) : H :=
  ∑ i : a.1, (((a.2 i).1 : 𝕜) + ((a.2 i).2 : 𝕜) * RCLike.I) • b i

/-- Arbitrary coefficients on one finite support lie in the closure of rational sums. -/
theorem sum_mem_closure_range_rationalSpanSum (b : HilbertBasis ι 𝕜 H)
    (s : Finset ι) (a : s → 𝕜) :
    (∑ i : s, a i • b i) ∈ closure (Set.range b.rationalSpanSum) := by
  classical
  let F : (s → 𝕜) → H := fun c => ∑ i : s, c i • b i
  have hF : Continuous F := by fun_prop
  let r : ℚ × ℚ → 𝕜 := fun q => (q.1 : 𝕜) + (q.2 : 𝕜) * RCLike.I
  have hrat : DenseRange r := by
    let L : ℝ × ℝ → 𝕜 := fun p => (p.1 : 𝕜) + (p.2 : 𝕜) * RCLike.I
    have hL : Continuous L := by fun_prop
    have hsurj : Function.Surjective L := by
      intro z
      exact ⟨(RCLike.re z, RCLike.im z), RCLike.re_add_im z⟩
    have hd : DenseRange (Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)) :=
      Rat.denseRange_cast.prodMap Rat.denseRange_cast
    simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, RCLike.ofReal_ratCast, L, r]
      using hsurj.denseRange.comp hd hL
  have hd : DenseRange (fun q : s → ℚ × ℚ => fun i => r (q i)) :=
    DenseRange.piMap fun _ => hrat
  have hc : IsClosed {c : s → 𝕜 | F c ∈ closure (Set.range b.rationalSpanSum)} :=
    isClosed_closure.preimage hF
  have hsub : Set.range (fun q : s → ℚ × ℚ => fun i => r (q i)) ⊆
      {c : s → 𝕜 | F c ∈ closure (Set.range b.rationalSpanSum)} := by
    rintro c ⟨q, rfl⟩
    exact subset_closure ⟨⟨s, q⟩, rfl⟩
  exact (closure_minimal hsub hc) (hd a)

/-- Density follows from finite coefficient approximation and the actual Hilbert expansion. -/
theorem denseRange_rationalSpanSum (b : HilbertBasis ι 𝕜 H) :
    DenseRange b.rationalSpanSum := by
  classical
  intro x
  apply isClosed_closure.mem_of_tendsto (b.hasSum_repr x)
  apply Filter.Eventually.of_forall
  intro s
  have h := b.sum_mem_closure_range_rationalSpanSum s (fun i => b.repr x i)
  change (∑ i : s, b.repr x (i : ι) • b (i : ι)) ∈ closure (Set.range b.rationalSpanSum) at h
  rw [Finset.sum_coe_sort s (fun i : ι => b.repr x i • b i)] at h
  exact h

/-- Coding the countable coefficients for each finite support gives a single cardinal bound. -/
theorem lift_mk_range_rationalSpanSum_le (b : HilbertBasis ι 𝕜 H) [Infinite ι] :
    Cardinal.lift.{uI} (#(Set.range b.rationalSpanSum)) ≤
      Cardinal.lift.{uH} (#ι) := by
  classical
  have hcode : ∀ s : Finset ι, ∃ c : (s → ℚ × ℚ) → ℕ, Function.Injective c := by
    intro s
    exact Countable.exists_injective_nat (s → ℚ × ℚ)
  choose code hcode using hcode
  let enc : (Σ s : Finset ι, s → ℚ × ℚ) → Finset ι × ℕ :=
    fun a => (a.1, code a.1 a.2)
  have henc : Function.Injective enc := by
    rintro ⟨s, p⟩ ⟨t, q⟩ h
    have hst : s = t := congrArg Prod.fst h
    subst t
    have hpq : p = q := hcode s (congrArg Prod.snd h)
    subst q
    rfl
  have hindex : #(Σ s : Finset ι, s → ℚ × ℚ) ≤ #ι := by
    calc
      Cardinal.mk (Σ s : Finset ι, s → ℚ × ℚ) ≤ #(Finset ι × ℕ) :=
        Cardinal.mk_le_of_injective henc
      _ = #ι := by simp only [Cardinal.mk_prod, Cardinal.lift_uzero,
        Cardinal.mk_nat, Cardinal.mk_finset_of_infinite,
        Cardinal.lift_aleph0, Cardinal.mk_mul_aleph0_eq, Cardinal.lift_id]
  let q : (Σ s : Finset ι, s → ℚ × ℚ) → Set.range b.rationalSpanSum :=
    fun a => ⟨b.rationalSpanSum a, Set.mem_range_self a⟩
  have hq : Function.Surjective q := by
    rintro ⟨x, a, rfl⟩
    exact ⟨a, rfl⟩
  exact (Cardinal.lift_mk_le'.mpr
    ⟨Function.Embedding.ofSurjective q hq⟩).trans (Cardinal.lift_le.mpr hindex)

/-- A net of radius one quarter on the unit ball separates all distinct basis vectors. -/
theorem lift_mk_lt_of_cardinalTotallyBounded_closedBall
    (b : HilbertBasis ι 𝕜 H) {α : Cardinal.{uA}}
    (hball : Metric.CardinalTotallyBounded α (Metric.closedBall (0 : H) 1)) :
    Cardinal.lift.{uA} (#ι) < Cardinal.lift.{uI} α := by
  classical
  obtain ⟨c, -, hc, hcover⟩ := hball (1 / 4) (by norm_num)
  have hb : ∀ i : ι, b i ∈ Metric.closedBall (0 : H) 1 := by
    intro i
    simpa only [Metric.mem_closedBall, dist_zero_right, b.orthonormal.1 i] using
      (le_refl (1 : ℝ))
  have hp : ∀ i : ι, ∃ z : c, dist (b i) (z : H) < 1 / 4 := by
    intro i
    obtain ⟨z, hzc, hiz⟩ := hcover (b i) (hb i)
    exact ⟨⟨z, hzc⟩, hiz⟩
  choose pick hpick using hp
  have hinj : Function.Injective pick := by
    intro i j hij
    by_contra hne
    have hinner : inner 𝕜 (b i) (b i - b j) = 1 := by
      rw [inner_sub_right, b.orthonormal.2 hne,
        inner_self_eq_one_of_norm_eq_one (b.orthonormal.1 i), sub_zero]
    have hsep : 1 ≤ dist (b i) (b j) := by
      have h := norm_inner_le_norm (𝕜 := 𝕜) (b i) (b i - b j)
      simpa only [hinner, norm_one, b.orthonormal.1 i, one_mul,
        dist_eq_norm] using h
    have hnear : dist (b i) (b j) < 1 / 2 := by
      calc
        dist (b i) (b j) ≤ dist (b i) (pick i : H) + dist (pick i : H) (b j) :=
          dist_triangle _ _ _
        _ < 1 / 4 + 1 / 4 := add_lt_add (hpick i) (by
          simpa only [hij, dist_comm] using hpick j)
        _ = 1 / 2 := by norm_num
    linarith
  have hsize : Cardinal.lift.{uH} (#ι) ≤ Cardinal.lift.{uI} (#c) :=
    Cardinal.lift_mk_le'.mpr ⟨⟨pick, hinj⟩⟩
  have hs := Cardinal.lift_le.{uA}.mpr hsize
  have ht := Cardinal.lift_lt.{max uH uA, uI}.mpr hc
  simp only [Cardinal.lift_lift] at hs ht
  have hr : Cardinal.lift.{uH} (Cardinal.lift.{uA} (#ι)) <
      Cardinal.lift.{uH} (Cardinal.lift.{uI} α) := by
    simpa only [Cardinal.lift_lift] using hs.trans_lt ht
  exact Cardinal.lift_lt.mp hr

/-- Strictly small Hilbert dimension gives nets for bounded subsets. The finite
basis case uses bounded-set compactness, whereas the infinite case uses rational sums. -/
theorem cardinalTotallyBounded_of_isBounded (b : HilbertBasis ι 𝕜 H)
    {α : Cardinal.{uA}} (hα : Cardinal.aleph0 ≤ α)
    (hb : Cardinal.lift.{uA} (#ι) < Cardinal.lift.{uI} α)
    {s : Set H} (hs : Bornology.IsBounded s) :
    Metric.CardinalTotallyBounded α s := by
  classical
  rcases finite_or_infinite ι with hi | hi
  · letI : Finite ι := hi
    letI : Fintype ι := Fintype.ofFinite ι
    letI : FiniteDimensional 𝕜 H := Module.Finite.of_basis b.toOrthonormalBasis.toBasis
    letI : ProperSpace H := FiniteDimensional.proper_rclike 𝕜 H
    obtain ⟨R, hR⟩ := hs.exists_norm_le
    have hsub : s ⊆ Metric.closedBall (0 : H) R := by
      intro x hx
      simpa only [Metric.mem_closedBall, dist_zero_right] using hR x hx
    exact Metric.cardinalTotallyBounded_of_totallyBounded
      ((isCompact_closedBall (0 : H) R).totallyBounded.subset hsub) hα
  · letI : Infinite ι := hi
    have hc := b.lift_mk_range_rationalSpanSum_le
    have hc' := Cardinal.lift_le.{uA}.mpr hc
    have hb' := Cardinal.lift_lt.{max uA uI, uH}.mpr hb
    simp only [Cardinal.lift_lift] at hc' hb'
    have hcommon : Cardinal.lift.{uI} (Cardinal.lift.{uA} (#(Set.range b.rationalSpanSum))) <
        Cardinal.lift.{uI} (Cardinal.lift.{uH} α) := by
      simpa only [Cardinal.lift_lift] using hc'.trans_lt hb'
    exact Metric.cardinalTotallyBounded_of_dense b.denseRange_rationalSpanSum
      (Cardinal.lift_lt.mp hcommon) s

/-- The closed unit ball detects precisely the actual Hilbert-basis index cardinal. -/
theorem cardinalTotallyBounded_closedBall_iff (b : HilbertBasis ι 𝕜 H)
    {α : Cardinal.{uA}} (hα : Cardinal.aleph0 ≤ α) :
    Metric.CardinalTotallyBounded α (Metric.closedBall (0 : H) 1) ↔
      Cardinal.lift.{uA} (#ι) < Cardinal.lift.{uI} α :=
  ⟨b.lift_mk_lt_of_cardinalTotallyBounded_closedBall,
    fun hb => b.cardinalTotallyBounded_of_isBounded hα hb isBounded_closedBall⟩

end HilbertBasis
