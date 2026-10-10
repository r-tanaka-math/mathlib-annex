/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Tactic

/-!
# Cardinal bounds on internal epsilon nets

For every positive radius, the centers lie in the set itself and have cardinality
strictly below the given cardinal. The ambient space and the cardinal may live in
different universes. The image theorem also allows a separate target universe.
This is a metric covering predicate, not a dimension of the closure of an operator
range. No regularity of the cardinal and no countable-union closure is assumed.
-/

set_option autoImplicit false
noncomputable section
open Set Cardinal
open scoped Cardinal

universe u v w
namespace Metric

variable {X : Type u} {Y : Type w}
variable [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- Internal epsilon nets with fewer than `alpha` centers, at every positive radius.
The explicit lifts compare the center and bound cardinals in a common universe. -/
def CardinalTotallyBounded (α : Cardinal.{v}) (s : Set X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : Set X, c ⊆ s ∧
    Cardinal.lift.{v} (#c) < Cardinal.lift.{u} α ∧
    ∀ x ∈ s, ∃ y ∈ c, dist x y < ε

/-- Relaxing the cardinal bound preserves the covering condition. -/
theorem CardinalTotallyBounded.mono_cardinal {α β : Cardinal.{v}} {s : Set X}
    (hs : CardinalTotallyBounded α s) (hαβ : α ≤ β) :
    CardinalTotallyBounded β s := by
  intro ε hε
  obtain ⟨c, hcs, hc, hcover⟩ := hs ε hε
  exact ⟨c, hcs, hc.trans_le (Cardinal.lift_le.mpr hαβ), hcover⟩

/-- The empty set has internal nets for every nonzero cardinal bound. -/
theorem cardinalTotallyBounded_empty {α : Cardinal.{v}} (hα : 0 < α) :
    CardinalTotallyBounded α (∅ : Set X) := by
  intro ε hε
  refine ⟨∅, Set.Subset.rfl, ?_, by simp⟩
  simpa using
    (Cardinal.lift_lt.mpr hα : Cardinal.lift.{u} (0 : Cardinal.{v}) < Cardinal.lift.{u} α)

/-- No set, including the empty set, has a net with fewer than zero centers. -/
theorem not_cardinalTotallyBounded_zero (s : Set X) :
    ¬ CardinalTotallyBounded (0 : Cardinal.{v}) s := by
  intro hs
  obtain ⟨c, -, hc, -⟩ := hs 1 zero_lt_one
  simpa using hc

/-- Subsets inherit the condition by recentering each occupied ball inside the subset.
The old net uses radius epsilon/2, so recentering preserves the strict final radius. -/
theorem CardinalTotallyBounded.subset {α : Cardinal.{v}} {s t : Set X}
    (ht : CardinalTotallyBounded α t) (hst : s ⊆ t) :
    CardinalTotallyBounded α s := by
  classical
  intro ε hε
  obtain ⟨c, hct, hc, hcover⟩ := ht (ε / 2) (half_pos hε)
  let occupied : Set c := {y | ∃ x ∈ s, dist x (y : X) < ε / 2}
  have hchoose : ∀ y : occupied, ∃ x ∈ s, dist x (y.1 : X) < ε / 2 :=
    fun y => y.property
  choose z hzs hzd using hchoose
  have hrange : #(Set.range z) ≤ #occupied := by
    apply Cardinal.mk_le_of_surjective
      (f := fun y : occupied => (⟨z y, Set.mem_range_self y⟩ : Set.range z))
    rintro ⟨x, y, rfl⟩
    exact ⟨y, rfl⟩
  have hsize : #(Set.range z) ≤ #c :=
    hrange.trans (Cardinal.mk_subtype_le (fun y : c => y ∈ occupied))
  refine ⟨Set.range z, ?_, (Cardinal.lift_le.mpr hsize).trans_lt hc, ?_⟩
  · rintro x ⟨y, rfl⟩
    exact hzs y
  · intro x hx
    obtain ⟨y, hyc, hxy⟩ := hcover x (hst hx)
    let o : occupied := ⟨⟨y, hyc⟩, x, hx, hxy⟩
    refine ⟨z o, Set.mem_range_self o, ?_⟩
    calc
      dist x (z o) ≤ dist x y + dist y (z o) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hxy (by
        simpa only [dist_comm] using hzd o)
      _ = ε := add_halves ε

/-- A uniformly continuous image retains the same cardinal bound, even when its
ambient type lies in a different universe. Surjective center mapping can only decrease size. -/
theorem CardinalTotallyBounded.image {α : Cardinal.{v}} {s : Set X}
    (hs : CardinalTotallyBounded α s) {f : X → Y} (hf : UniformContinuous f) :
    CardinalTotallyBounded α (f '' s) := by
  classical
  intro ε hε
  obtain ⟨η, hη, hcontrol⟩ := Metric.uniformContinuous_iff.mp hf ε hε
  obtain ⟨c, hcs, hc, hcover⟩ := hs η hη
  let fc : c → (f '' c) := fun x => ⟨f x, x, x.property, rfl⟩
  have hfc : Function.Surjective fc := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hsize : Cardinal.lift.{u} (#(f '' c)) ≤ Cardinal.lift.{w} (#c) :=
    Cardinal.lift_mk_le'.mpr ⟨Function.Embedding.ofSurjective fc hfc⟩
  have hsize' : Cardinal.lift.{v} (Cardinal.lift.{u} (#(f '' c))) ≤
      Cardinal.lift.{v} (Cardinal.lift.{w} (#c)) := Cardinal.lift_le.mpr hsize
  have hc' : Cardinal.lift.{w} (Cardinal.lift.{v} (#c)) <
      Cardinal.lift.{w} (Cardinal.lift.{u} α) := Cardinal.lift_lt.mpr hc
  simp only [Cardinal.lift_lift] at hsize' hc'
  have hcommon : Cardinal.lift.{u} (Cardinal.lift.{v} (#(f '' c))) <
      Cardinal.lift.{u} (Cardinal.lift.{w} α) := by
    simpa only [Cardinal.lift_lift] using hsize'.trans_lt hc'
  refine ⟨f '' c, Set.image_mono hcs, Cardinal.lift_lt.mp hcommon, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨z, hzc, hxz⟩ := hcover x hx
  exact ⟨f z, ⟨z, hzc, rfl⟩, hcontrol hxz⟩

/-- The aleph-zero specialization is exactly the existing uniform notion of total
boundedness. Centers are internal in the forward construction as well. -/
theorem cardinalTotallyBounded_aleph0_iff {s : Set X} :
    CardinalTotallyBounded (Cardinal.aleph0 : Cardinal.{v}) s ↔ TotallyBounded s := by
  constructor
  · intro hs
    apply Metric.totallyBounded_iff.mpr
    intro ε hε
    obtain ⟨c, -, hc, hcover⟩ := hs ε hε
    have hcsmall : #c < Cardinal.aleph0 := by
      simpa only [Cardinal.lift_aleph0, Cardinal.lift_lt_aleph0] using hc
    have hcfin : c.Finite := Cardinal.lt_aleph0_iff_set_finite.mp hcsmall
    refine ⟨c, hcfin, ?_⟩
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover x hx
    exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, hxy⟩⟩
  · intro hs ε hε
    obtain ⟨c, hcs, hcfin, hcover⟩ := Metric.finite_approx_of_totallyBounded hs ε hε
    have hcsmall : #c < Cardinal.aleph0 := Cardinal.lt_aleph0_iff_set_finite.mpr hcfin
    refine ⟨c, hcs, ?_, ?_⟩
    · simpa only [Cardinal.lift_aleph0, Cardinal.lift_lt_aleph0] using hcsmall
    · intro x hx
      obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hcover hx)
      obtain ⟨hyc, hxy⟩ := Set.mem_iUnion.mp hy
      exact ⟨y, hyc, hxy⟩

/-- Totally bounded sets satisfy every infinite cardinal net bound. -/
theorem cardinalTotallyBounded_of_totallyBounded {α : Cardinal.{v}} {s : Set X}
    (hs : TotallyBounded s) (hα : Cardinal.aleph0 ≤ α) :
    CardinalTotallyBounded α s :=
  (cardinalTotallyBounded_aleph0_iff.mpr hs).mono_cardinal hα

end Metric

/-! ## Finite products, unions and one-approximation recentering -/

namespace Metric

variable {X : Type u} {Y : Type w}
variable [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- A singleton admits an internal net precisely when its one center is permitted. -/
theorem cardinalTotallyBounded_singleton {α : Cardinal.{v}} (hα : 1 < α) (x : X) :
    CardinalTotallyBounded α ({x} : Set X) := by
  intro ε hε
  refine ⟨{x}, Set.Subset.rfl, ?_, ?_⟩
  · simpa using (Cardinal.lift_lt.mpr hα :
      Cardinal.lift.{u} (1 : Cardinal.{v}) < Cardinal.lift.{u} α)
  · intro y hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    exact ⟨x, Set.mem_singleton x, by simpa using hε⟩

/-- With bound one, a nonempty set cannot be covered even at one positive radius. -/
theorem not_cardinalTotallyBounded_one {s : Set X} (hs : s.Nonempty) :
    ¬ CardinalTotallyBounded (1 : Cardinal.{v}) s := by
  intro h
  obtain ⟨x, hx⟩ := hs
  obtain ⟨c, -, hc, hcover⟩ := h 1 zero_lt_one
  obtain ⟨y, hy, -⟩ := hcover x hx
  letI : Nonempty c := ⟨⟨y, hy⟩⟩
  have hone : (1 : Cardinal.{u}) ≤ #c :=
    Cardinal.one_le_iff_ne_zero.mpr (Cardinal.mk_ne_zero c)
  have hone' : (1 : Cardinal.{max u v}) ≤ Cardinal.lift.{v} (#c) := by
    simpa only [Cardinal.lift_one] using Cardinal.lift_le.{v}.mpr hone
  exact (not_lt_of_ge hone') (by simpa using hc)

/-- Binary unions use cardinal addition, not a countable union or a regularity assumption. -/
theorem CardinalTotallyBounded.union {α : Cardinal.{v}} {s t : Set X}
    (hs : CardinalTotallyBounded α s) (ht : CardinalTotallyBounded α t)
    (hα : Cardinal.aleph0 ≤ α) : CardinalTotallyBounded α (s ∪ t) := by
  classical
  intro ε hε
  obtain ⟨c, hcs, hc, hsc⟩ := hs ε hε
  obtain ⟨d, hdt, hd, htd⟩ := ht ε hε
  let f : c ⊕ d → (c ∪ d : Set X) := Sum.elim
    (fun x => ⟨x, Or.inl x.property⟩) (fun y => ⟨y, Or.inr y.property⟩)
  have hf : Function.Surjective f := by
    rintro ⟨x, hx | hx⟩
    · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
    · exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩
  have hsize : #(c ∪ d : Set X) ≤ #(c ⊕ d) :=
    Cardinal.mk_le_of_surjective hf
  have hsum : Cardinal.lift.{v} (#(c ⊕ d)) < Cardinal.lift.{u} α := by
    simp only [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_add]
    exact Cardinal.add_lt_of_lt
      (by simpa using Cardinal.lift_le.{u}.mpr hα) hc hd
  refine ⟨c ∪ d, Set.union_subset_union hcs hdt,
    (Cardinal.lift_le.mpr hsize).trans_lt hsum, ?_⟩
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨y, hy, hxy⟩ := hsc x hx
    exact ⟨y, Or.inl hy, hxy⟩
  · obtain ⟨y, hy, hxy⟩ := htd x hx
    exact ⟨y, Or.inr hy, hxy⟩

/-- Finite unions retain the strict bound for every infinite cardinal, including singular ones. -/
theorem cardinalTotallyBounded_biUnion_finset {α : Cardinal.{v}} {ι : Type*}
    (s : Finset ι) (t : ι → Set X) (hα : Cardinal.aleph0 ≤ α)
    (ht : ∀ i ∈ s, CardinalTotallyBounded α (t i)) :
    CardinalTotallyBounded α (⋃ i ∈ s, t i) := by
  classical
  revert ht
  induction s using Finset.induction_on with
  | empty =>
    intro ht
    simpa using cardinalTotallyBounded_empty (X := X)
      (Cardinal.aleph0_pos.trans_le hα)
  | @insert i s hi ih =>
    intro ht
    have hti := ht i (Finset.mem_insert_self i s)
    have hts := ih (fun j hj => ht j (Finset.mem_insert_of_mem hj))
    have heq : (⋃ j ∈ insert i s, t j) = t i ∪ (⋃ j ∈ s, t j) := by
      ext x
      simp only [Set.mem_iUnion, Finset.mem_insert, Set.mem_union]
      aesop
    rw [heq]
    exact hti.union hts hα

/-- Product nets with the usual product metric. The two spaces and the cardinal
may have three different universes; cardinal multiplication is taken after lifting. -/
theorem CardinalTotallyBounded.prod {α : Cardinal.{v}} {s : Set X} {t : Set Y}
    (hs : CardinalTotallyBounded α s) (ht : CardinalTotallyBounded α t)
    (hα : Cardinal.aleph0 ≤ α) : CardinalTotallyBounded α (s ×ˢ t) := by
  classical
  intro ε hε
  obtain ⟨c, hcs, hc, hsc⟩ := hs ε hε
  obtain ⟨d, hdt, hd, htd⟩ := ht ε hε
  let e : (c ×ˢ d : Set (X × Y)) ≃ c × d :=
    { toFun := fun z => (⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2⟩)
      invFun := fun z => ⟨(z.1.1, z.2.1), z.1.2, z.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hsize : Cardinal.lift.{v} (#(c ×ˢ d : Set (X × Y))) <
      Cardinal.lift.{max u w} α := by
    rw [Cardinal.mk_congr e, Cardinal.mk_prod, Cardinal.lift_mul]
    apply Cardinal.mul_lt_of_lt
    · simpa only [Cardinal.lift_aleph0] using
        Cardinal.lift_le.{max u w}.mpr hα
    · simpa only [Cardinal.lift_lift] using Cardinal.lift_lt.{max u v, w}.mpr hc
    · simpa only [Cardinal.lift_lift] using Cardinal.lift_lt.{max w v, u}.mpr hd
  refine ⟨c ×ˢ d, fun z hz => ⟨hcs hz.1, hdt hz.2⟩, hsize, ?_⟩
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  obtain ⟨z, hz, hxz⟩ := hsc x hx
  obtain ⟨w, hw, hyw⟩ := htd y hy
  exact ⟨(z, w), ⟨hz, hw⟩, by
    simpa only [Prod.dist_eq, max_lt_iff] using And.intro hxz hyw⟩

/-- Uniform approximation on a set preserves the cardinal net bound. At each
radius only ONE approximant and ONE net are used. The centers are moved to the
limit image by choosing actual preimages of the approximant's internal centers. -/
theorem cardinalTotallyBounded_image_of_uniform_approximation
    {α : Cardinal.{v}} {ι : Type*} {s : Set ι} {f : ι → X}
    (h : ∀ η : ℝ, 0 < η → ∃ g : ι → X,
      CardinalTotallyBounded α (g '' s) ∧ ∀ x ∈ s, dist (f x) (g x) ≤ η) :
    CardinalTotallyBounded α (f '' s) := by
  classical
  intro ε hε
  have hη : 0 < ε / 4 := by positivity
  obtain ⟨g, hg, hfg⟩ := h (ε / 4) hη
  obtain ⟨c, hcs, hc, hcover⟩ := hg (ε / 4) hη
  have hpre : ∀ y : c, ∃ x ∈ s, g x = (y : X) := fun y => hcs y.property
  choose z hzs hgz using hpre
  let centers : Set X := Set.range (fun y : c => f (z y))
  have hsize : #centers ≤ #c := by
    apply Cardinal.mk_le_of_surjective
      (f := fun y : c => (⟨f (z y), Set.mem_range_self y⟩ : centers))
    rintro ⟨x, y, rfl⟩
    exact ⟨y, rfl⟩
  refine ⟨centers, ?_, (Cardinal.lift_le.mpr hsize).trans_lt hc, ?_⟩
  · rintro x ⟨y, rfl⟩
    exact ⟨z y, hzs y, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hcover (g x) ⟨x, hx, rfl⟩
    let j : c := ⟨y, hy⟩
    have hyz : dist y (f (z j)) ≤ ε / 4 := by
      change dist (j : X) (f (z j)) ≤ ε / 4
      rw [← hgz j, dist_comm]
      exact hfg (z j) (hzs j)
    refine ⟨f (z j), Set.mem_range_self j, ?_⟩
    calc
      dist (f x) (f (z j)) ≤ dist (f x) (g x) + dist (g x) (f (z j)) :=
        dist_triangle _ _ _
      _ ≤ dist (f x) (g x) + (dist (g x) y + dist y (f (z j))) := by
        gcongr; exact dist_triangle _ _ _
      _ < ε := by linarith [hfg x hx]

end Metric

namespace Metric

universe uD uA
variable {X : Type uD} [PseudoMetricSpace X]

/-- A dense set with a strict cardinal bound supplies internal nets for every subset.
Each occupied ball is recentered in the subset; the center count does not increase. -/
theorem cardinalTotallyBounded_of_dense {α : Cardinal.{uA}} {d : Set X}
    (hd : Dense d) (hcard : Cardinal.lift.{uA} (#d) < Cardinal.lift.{uD} α)
    (s : Set X) : CardinalTotallyBounded α s := by
  classical
  intro ε hε
  let occupied : Set d := {y | ∃ x ∈ s, dist x (y : X) < ε / 2}
  have hpick : ∀ y : occupied, ∃ x ∈ s, dist x (y.1 : X) < ε / 2 :=
    fun y => y.property
  choose pick hpicks hpickd using hpick
  have hsize : #(Set.range pick) ≤ #d := by
    have hr : #(Set.range pick) ≤ #occupied := by
      apply Cardinal.mk_le_of_surjective
        (f := fun y : occupied => (⟨pick y, Set.mem_range_self y⟩ : Set.range pick))
      rintro ⟨x, y, rfl⟩
      exact ⟨y, rfl⟩
    exact hr.trans (Cardinal.mk_subtype_le (fun y : d => y ∈ occupied))
  refine ⟨Set.range pick, ?_, (Cardinal.lift_le.mpr hsize).trans_lt hcard, ?_⟩
  · rintro x ⟨y, rfl⟩
    exact hpicks y
  · intro x hx
    obtain ⟨y, hyd, hxy⟩ := Metric.mem_closure_iff.mp (hd x) (ε / 2) (half_pos hε)
    have hxy' : dist x y < ε / 2 := by simpa only [dist_comm] using hxy
    let o : occupied := ⟨⟨y, hyd⟩, x, hx, hxy'⟩
    refine ⟨pick o, Set.mem_range_self o, ?_⟩
    calc
      dist x (pick o) ≤ dist x y + dist y (pick o) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hxy' (by
        simpa only [dist_comm] using hpickd o)
      _ = ε := add_halves ε

end Metric
