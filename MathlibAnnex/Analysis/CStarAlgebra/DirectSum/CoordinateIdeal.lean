/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.C0DirectSum
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Coordinate ideals in dependent c₀-direct sums

For a dependent c₀-sum, the image of one coordinate embedding is exposed as an
actual algebraic two-sided ideal.  Its complementary ideal is the kernel of the
coordinate evaluation.  Every element splits exactly into its coordinate part
and its complementary part, different coordinate ideals have zero products,
and finite coordinate truncations converge in norm.

The construction uses the existing `C0DirectSum`; no second direct-sum type is
introduced.  No countability assumption is placed on the index set.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open Filter Set Topology
open scoped BigOperators CStarAlgebra ENNReal

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uι uA uK

namespace C0DirectSum

variable {ι : Type uι} (A : ι → Type uA)
variable [∀ i, NonUnitalCStarAlgebra (A i)]

/-- The actual ideal supported at one coordinate. -/
def coordinateIdeal (i : ι) : TwoSidedIdeal (C0DirectSum A) :=
  TwoSidedIdeal.mk'
    {x | ∀ j, j ≠ i → eval A j x = 0}
    (by intro j hji; simp)
    (by
      intro x y hx hy j hji
      simp only [map_add, hx j hji, hy j hji, add_zero])
    (by
      intro x hx j hji
      simp only [map_neg, hx j hji, neg_zero])
    (by
      intro x y hy j hji
      simp only [map_mul, hy j hji, mul_zero])
    (by
      intro x y hx j hji
      simp only [map_mul, hx j hji, zero_mul])

@[simp]
theorem mem_coordinateIdeal (i : ι) (x : C0DirectSum A) :
    x ∈ coordinateIdeal A i ↔ ∀ j, j ≠ i → eval A j x = 0 := by
  simp [coordinateIdeal]

/-- The complementary ideal consists exactly of families whose `i`-th
coordinate is zero. -/
def complementIdeal (i : ι) : TwoSidedIdeal (C0DirectSum A) :=
  TwoSidedIdeal.ker (eval A i)

@[simp]
theorem mem_complementIdeal (i : ι) (x : C0DirectSum A) :
    x ∈ complementIdeal A i ↔ eval A i x = 0 := by
  exact TwoSidedIdeal.mem_ker (eval A i) (x := x)

/-- Delete one coordinate, retaining an element of the same c₀-sum. -/
def erase (i : ι) (x : C0DirectSum A) : C0DirectSum A :=
  x - single A i (eval A i x)

@[simp]
theorem eval_erase_same (i : ι) (x : C0DirectSum A) :
    eval A i (erase A i x) = 0 := by
  simp only [erase, map_sub, eval_single_same, sub_self]

@[simp]
theorem eval_erase_of_ne {i j : ι} (hji : j ≠ i) (x : C0DirectSum A) :
    eval A j (erase A i x) = eval A j x := by
  rw [erase, map_sub, eval_single_of_ne A hji, sub_zero]

/-- Exact coordinate/complement decomposition. -/
theorem single_add_erase (i : ι) (x : C0DirectSum A) :
    single A i (eval A i x) + erase A i x = x := by
  simp [erase]

/-- Equivalent orientation of the exact decomposition. -/
theorem eq_single_add_erase (i : ι) (x : C0DirectSum A) :
    x = single A i (eval A i x) + erase A i x :=
  (single_add_erase A i x).symm

@[simp]
theorem erase_mem_complementIdeal (i : ι) (x : C0DirectSum A) :
    erase A i x ∈ complementIdeal A i := by
  rw [mem_complementIdeal]
  exact eval_erase_same A i x

@[simp]
theorem single_mem_coordinateIdeal (i : ι) (a : A i) :
    single A i a ∈ coordinateIdeal A i := by
  rw [mem_coordinateIdeal]
  intro j hji
  exact eval_single_of_ne A hji a

/-- Membership in the coordinate ideal is exactly equality with the coordinate
single selected by evaluation. -/
theorem mem_coordinateIdeal_iff_eq_single_eval (i : ι) (x : C0DirectSum A) :
    x ∈ coordinateIdeal A i ↔ x = single A i (eval A i x) := by
  constructor
  · intro hx
    apply Subtype.ext
    ext j
    by_cases hji : j = i
    · subst j
      change eval A i x = eval A i (single A i (eval A i x))
      rw [eval_single_same]
    · have hj := (mem_coordinateIdeal A i x).1 hx j hji
      change eval A j x = eval A j (single A i (eval A i x))
      rw [eval_single_of_ne A hji]
      exact hj
  · intro hx
    rw [hx]
    exact single_mem_coordinateIdeal A i (eval A i x)

/-- The coordinate ideal is precisely the image of the coordinate embedding. -/
theorem mem_coordinateIdeal_iff_exists_single (i : ι) (x : C0DirectSum A) :
    x ∈ coordinateIdeal A i ↔ ∃ a : A i, single A i a = x := by
  constructor
  · intro hx
    exact ⟨eval A i x, (mem_coordinateIdeal_iff_eq_single_eval A i x).1 hx |>.symm⟩
  · rintro ⟨a, rfl⟩
    exact single_mem_coordinateIdeal A i a

/-- The coordinate ideal and its complement have zero intersection. -/
theorem coordinateIdeal_inf_complementIdeal (i : ι) :
    coordinateIdeal A i ⊓ complementIdeal A i = ⊥ := by
  apply TwoSidedIdeal.ext
  intro x
  constructor
  · intro hx
    have hcoord : x = single A i (eval A i x) :=
      (mem_coordinateIdeal_iff_eq_single_eval A i x).1 hx.1
    have hzero : eval A i x = 0 := (mem_complementIdeal A i x).1 hx.2
    rw [hcoord, hzero]
    simp
  · intro hx
    change x = 0 at hx
    rw [hx]
    exact (coordinateIdeal A i ⊓ complementIdeal A i).zero_mem

/-- Different coordinate ideals multiply to zero in this order. -/
theorem mul_eq_zero_of_mem_coordinateIdeal_of_mem_coordinateIdeal
    {i j : ι} (hij : i ≠ j) {x y : C0DirectSum A}
    (hx : x ∈ coordinateIdeal A i) (hy : y ∈ coordinateIdeal A j) :
    x * y = 0 := by
  apply Subtype.ext
  ext k
  change eval A k (x * y) = 0
  rw [map_mul]
  by_cases hki : k = i
  · subst k
    rw [(mem_coordinateIdeal A j y).1 hy i hij]
    simp
  · rw [(mem_coordinateIdeal A i x).1 hx k hki]
    simp

/-- Different coordinate ideals also multiply to zero in the reverse order. -/
theorem mul_eq_zero_of_mem_coordinateIdeal_of_mem_coordinateIdeal_rev
    {i j : ι} (hij : i ≠ j) {x y : C0DirectSum A}
    (hx : x ∈ coordinateIdeal A i) (hy : y ∈ coordinateIdeal A j) :
    y * x = 0 := by
  exact mul_eq_zero_of_mem_coordinateIdeal_of_mem_coordinateIdeal A hij.symm hy hx

/-- Finite truncation is literally the finite sum of coordinate singles. -/
theorem truncate_eq_sum_single (s : Finset ι) (x : C0DirectSum A) :
    truncate A s x = ∑ i ∈ s, single A i (eval A i x) := rfl

/-- The directed net of finite coordinate truncations converges in norm. -/
theorem tendsto_truncate (x : C0DirectSum A) :
    Tendsto (fun s : Finset ι => truncate A s x) atTop (𝓝 x) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨s₀, hs₀⟩ := exists_finset_norm_sub_truncate_lt A x (half_pos hε)
  refine Filter.eventually_atTop.2 ⟨s₀, ?_⟩
  intro s hss
  have hoff : ∀ i, i ∉ s → ‖eval A i x‖ ≤ ε / 2 := by
    intro i hi
    have hi₀ : i ∉ s₀ := by
      intro hi₀
      exact hi (hss hi₀)
    have hcoord := norm_eval_le A i (x - truncate A s₀ x)
    have heval : eval A i (x - truncate A s₀ x) = eval A i x := by
      rw [map_sub, eval_truncate, if_neg hi₀, sub_zero]
    rw [heval] at hcoord
    exact hcoord.trans (le_of_lt hs₀)
  have hnorm := norm_sub_truncate_le A s x (half_pos hε).le hoff
  have hlt : ‖x - truncate A s x‖ < ε :=
    hnorm.trans_lt (half_lt_self hε)
  simpa only [dist_eq_norm, norm_sub_rev] using hlt


end C0DirectSum

end MathlibAnnex.Analysis.CStarAlgebra
