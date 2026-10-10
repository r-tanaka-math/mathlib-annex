/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module
public import Mathlib.Analysis.CStarAlgebra.lpSpace
public import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
public import Mathlib.Topology.Sequences
public import Mathlib.Tactic

@[expose] public section

/-!
# Dependent c₀-direct sums

Mathlib already supplies the dependent bounded product `lp A ∞`, with its
pointwise nonunital C-star structure.  This file defines the actual dependent
c₀-direct sum as the norm-closed star subalgebra of families vanishing at
infinity.  No countability or separability assumption is imposed on the index
set or on the fibres.

The file also supplies coordinate evaluations, coordinate embeddings, finite
truncations, and the exact supremum norm formula.  The algebraic direct sum,
the bounded product, and the c₀-direct sum remain separate objects throughout.
-/

set_option autoImplicit false
noncomputable section

open Filter Set Topology
open scoped BigOperators CStarAlgebra ENNReal

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uι uA uH

namespace C0DirectSum

variable {ι : Type uι} (A : ι → Type uA)
variable [∀ i, NonUnitalCStarAlgebra (A i)]

/-- A bounded dependent family vanishes at infinity when every positive
superlevel set of coordinate norms is finite. -/
def VanishesAtInfinity (x : lp A ∞) : Prop :=
  ∀ ε : ℝ, 0 < ε → Set.Finite {i : ι | ε ≤ ‖x i‖}

@[simp]
theorem vanishesAtInfinity_zero : VanishesAtInfinity A 0 := by
  intro ε hε
  simpa [VanishesAtInfinity, not_le_of_gt hε] using
    (Set.finite_empty : Set.Finite (∅ : Set ι))

theorem VanishesAtInfinity.neg {x : lp A ∞} (hx : VanishesAtInfinity A x) :
    VanishesAtInfinity A (-x) := by
  simpa [VanishesAtInfinity] using hx

@[simp]
theorem vanishesAtInfinity_neg_iff {x : lp A ∞} :
    VanishesAtInfinity A (-x) ↔ VanishesAtInfinity A x :=
  ⟨fun h => by simpa only [neg_neg] using h.neg (A := A), fun h => h.neg (A := A)⟩

theorem VanishesAtInfinity.add {x y : lp A ∞}
    (hx : VanishesAtInfinity A x) (hy : VanishesAtInfinity A y) :
    VanishesAtInfinity A (x + y) := by
  intro ε hε
  have hx' := hx (ε / 2) (half_pos hε)
  have hy' := hy (ε / 2) (half_pos hε)
  refine (hx'.union hy').subset ?_
  intro i hi
  simp only [Set.mem_union, Set.mem_setOf_eq]
  by_contra hsmall
  push_neg at hsmall
  change ε ≤ ‖x i + y i‖ at hi
  have htri : ‖x i + y i‖ ≤ ‖x i‖ + ‖y i‖ := norm_add_le _ _
  linarith

theorem VanishesAtInfinity.sub {x y : lp A ∞}
    (hx : VanishesAtInfinity A x) (hy : VanishesAtInfinity A y) :
    VanishesAtInfinity A (x - y) := by
  simpa only [sub_eq_add_neg] using hx.add (A := A) (hy.neg (A := A))

theorem VanishesAtInfinity.smul (c : ℂ) {x : lp A ∞}
    (hx : VanishesAtInfinity A x) : VanishesAtInfinity A (c • x) := by
  by_cases hc : c = 0
  · subst c
    simpa using vanishesAtInfinity_zero (A := A)
  intro ε hε
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hfinite := hx (ε / ‖c‖) (div_pos hε hcpos)
  refine hfinite.subset ?_
  intro i hi
  change ε / ‖c‖ ≤ ‖x i‖
  change ε ≤ ‖c • x i‖ at hi
  rw [norm_smul] at hi
  exact (div_le_iff₀ hcpos).2 (by simpa [mul_comm] using hi)

theorem VanishesAtInfinity.mul {x y : lp A ∞}
    (hx : VanishesAtInfinity A x) (hy : VanishesAtInfinity A y) :
    VanishesAtInfinity A (x * y) := by
  intro ε hε
  let δ : ℝ := Real.sqrt ε
  have hδ : 0 < δ := Real.sqrt_pos.2 hε
  have hδsq : δ * δ = ε := by
    dsimp [δ]
    exact Real.mul_self_sqrt hε.le
  have hx' := hx δ hδ
  have hy' := hy δ hδ
  refine (hx'.union hy').subset ?_
  intro i hi
  simp only [Set.mem_union, Set.mem_setOf_eq]
  by_contra hsmall
  push_neg at hsmall
  change ε ≤ ‖x i * y i‖ at hi
  have hmul : ‖x i * y i‖ ≤ ‖x i‖ * ‖y i‖ := norm_mul_le _ _
  have hprod : ‖x i‖ * ‖y i‖ < δ * δ := calc
    ‖x i‖ * ‖y i‖ ≤ ‖x i‖ * δ :=
      mul_le_mul_of_nonneg_left hsmall.2.le (norm_nonneg _)
    _ < δ * δ := mul_lt_mul_of_pos_right hsmall.1 hδ
  linarith

theorem VanishesAtInfinity.star {x : lp A ∞}
    (hx : VanishesAtInfinity A x) : VanishesAtInfinity A (star x) := by
  simpa [VanishesAtInfinity] using hx

@[simp]
theorem vanishesAtInfinity_star_iff {x : lp A ∞} :
    VanishesAtInfinity A (star x) ↔ VanishesAtInfinity A x :=
  ⟨fun h => by simpa only [star_star] using h.star (A := A), fun h => h.star (A := A)⟩

/-- Finitely supported bounded families, before norm closure. -/
def finiteSupportStarSubalgebra : NonUnitalStarSubalgebra ℂ (lp A ∞) where
  carrier := {x | Set.Finite {i : ι | x i ≠ 0}}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    refine (hx.union hy).subset ?_
    intro i hi
    change x i + y i ≠ 0 at hi
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_contra h
    push_neg at h
    exact hi (by simp [h.1, h.2])
  mul_mem' := by
    intro x y hx hy
    refine hx.subset ?_
    intro i hi
    change x i ≠ 0
    intro hxi
    apply hi
    simp [hxi]
  smul_mem' := by
    intro c x hx
    refine hx.subset ?_
    intro i hi
    change x i ≠ 0
    intro hxi
    apply hi
    simp [hxi]
  star_mem' := by
    intro x hx
    refine hx.subset ?_
    intro i hi
    change x i ≠ 0
    intro hxi
    apply hi
    simp [hxi]

@[simp]
theorem mem_finiteSupportStarSubalgebra (x : lp A ∞) :
    x ∈ finiteSupportStarSubalgebra A ↔ Set.Finite {i : ι | x i ≠ 0} :=
  Iff.rfl

/-- The dependent c₀-direct sum as a concrete star subalgebra of the bounded
product. -/
def starSubalgebra : NonUnitalStarSubalgebra ℂ (lp A ∞) where
  carrier := {x | VanishesAtInfinity A x}
  zero_mem' := vanishesAtInfinity_zero A
  add_mem' := fun hx hy => hx.add (A := A) hy
  mul_mem' := fun hx hy => hx.mul (A := A) hy
  smul_mem' := fun c _ hx => hx.smul (A := A) c
  star_mem' := fun hx => hx.star (A := A)

@[simp]
theorem mem_starSubalgebra (x : lp A ∞) :
    x ∈ starSubalgebra A ↔ VanishesAtInfinity A x := Iff.rfl

/-- Vanishing at infinity is closed in the supremum norm. -/
theorem isClosed_setOf_vanishesAtInfinity :
    IsClosed {x : lp A ∞ | VanishesAtInfinity A x} := by
  rw [← isOpen_compl_iff]
  refine Metric.isOpen_iff.mpr ?_
  intro x hx
  change ¬ VanishesAtInfinity A x at hx
  unfold VanishesAtInfinity at hx
  push_neg at hx
  obtain ⟨ε, hε, hinfinite⟩ := hx
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro y hy
  change ¬ VanishesAtInfinity A y
  intro hy0
  have hfinite := hy0 (ε / 2) (half_pos hε)
  apply hinfinite
  refine hfinite.subset ?_
  intro i hi
  change ε / 2 ≤ ‖y i‖
  change ε ≤ ‖x i‖ at hi
  have hcoord : ‖x i - y i‖ ≤ ‖x - y‖ := by
    simpa only [lp.coeFn_sub, Pi.sub_apply] using
      lp.norm_apply_le_norm (by simp) (x - y) i
  have hdist : ‖x - y‖ < ε / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hy
  have hreverse : ‖x i‖ - ‖y i‖ ≤ ‖x i - y i‖ := by
    exact norm_sub_norm_le (x i) (y i)
  linarith

/-- The c₀-direct sum is norm closed in the bounded product. -/
theorem isClosed_starSubalgebra : IsClosed (starSubalgebra A : Set (lp A ∞)) :=
  isClosed_setOf_vanishesAtInfinity A

end C0DirectSum

/-- The actual dependent c₀-direct sum.  It is a subtype of `lp A ∞`, not an
unrestricted product and not an algebraic direct sum. -/
abbrev C0DirectSum {ι : Type uι} (A : ι → Type uA)
    [∀ i, NonUnitalCStarAlgebra (A i)] :=
  C0DirectSum.starSubalgebra A

namespace C0DirectSum

variable {ι : Type uι} (A : ι → Type uA)
variable [∀ i, NonUnitalCStarAlgebra (A i)]

instance nonUnitalCStarAlgebra : NonUnitalCStarAlgebra (C0DirectSum A) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra _
    (h_closed := isClosed_starSubalgebra A)

/-- Coordinate evaluation on the dependent c₀-direct sum. -/
def eval (i : ι) : C0DirectSum A →⋆ₙₐ[ℂ] A i where
  toFun := fun x => x.1 i
  map_zero' := rfl
  map_add' := fun _ _ => rfl
  map_mul' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  map_star' := fun _ => rfl

@[simp]
theorem eval_apply (i : ι) (x : C0DirectSum A) : eval A i x = x.1 i := rfl

open scoped Classical

/-- A single nonzero coordinate is a c₀-family. -/
theorem vanishesAtInfinity_single (i : ι) (a : A i) :
    VanishesAtInfinity A (lp.single ∞ i a) := by
  intro ε hε
  refine (Set.finite_singleton i).subset ?_
  intro j hj
  simp only [Set.mem_singleton_iff]
  by_contra hji
  have hz : (lp.single ∞ i a : lp A ∞) j = 0 := by
    simp [lp.single_apply, hji, Ne.symm hji]
  change ε ≤ ‖(lp.single ∞ i a : lp A ∞) j‖ at hj
  rw [hz, norm_zero] at hj
  exact (not_lt_of_ge hj) hε

/-- The coordinate embedding into the dependent c₀-direct sum. -/
def single (i : ι) : A i →⋆ₙₐ[ℂ] C0DirectSum A where
  toFun := fun a => ⟨lp.single ∞ i a, vanishesAtInfinity_single A i a⟩
  map_zero' := by
    apply Subtype.ext
    ext j
    simp [lp.single_apply]
  map_add' := by
    intro a b
    apply Subtype.ext
    ext j
    simp [lp.single_apply]
  map_mul' := by
    intro a b
    apply Subtype.ext
    ext j
    by_cases hji : j = i
    · subst j
      simp [lp.single_apply]
    · simp [lp.single_apply, hji, Ne.symm hji]
  map_smul' := by
    intro c a
    apply Subtype.ext
    ext j
    simp [lp.single_apply]
  map_star' := by
    intro a
    apply Subtype.ext
    ext j
    by_cases hji : j = i
    · subst j
      simp [lp.single_apply]
    · simp [lp.single_apply, hji, Ne.symm hji]

@[simp]
theorem eval_single_same (i : ι) (a : A i) : eval A i (single A i a) = a := by
  change (lp.single ∞ i a : lp A ∞) i = a
  simp [lp.single_apply]

@[simp]
theorem eval_single_of_ne {i j : ι} (h : j ≠ i) (a : A i) :
    eval A j (single A i a) = 0 := by
  change (lp.single ∞ i a : lp A ∞) j = 0
  simp [lp.single_apply, h, Ne.symm h]

/-- Every coordinate evaluation is onto. -/
theorem eval_surjective (i : ι) : Function.Surjective (eval A i) := by
  intro a
  exact ⟨single A i a, eval_single_same A i a⟩

/-- Every coordinate embedding is injective. -/
theorem single_injective (i : ι) : Function.Injective (single A i) := by
  intro a b h
  have := congrArg (fun x : C0DirectSum A => eval A i x) h
  simpa only [eval_single_same] using this

/-- Coordinate evaluation is contractive for the inherited supremum norm. -/
theorem norm_eval_le (i : ι) (x : C0DirectSum A) : ‖eval A i x‖ ≤ ‖x‖ := by
  change ‖x.1 i‖ ≤ ‖x.1‖
  exact lp.norm_apply_le_norm (by simp) x.1 i

/-- A coordinate embedding is an isometry. -/
@[simp]
theorem norm_single (i : ι) (a : A i) : ‖single A i a‖ = ‖a‖ := by
  change ‖(lp.single ∞ i a : lp A ∞)‖ = ‖a‖
  exact lp.norm_single (by simp) i a

/-- The c₀ norm is literally the supremum of the coordinate norms. -/
theorem norm_eq_ciSup (x : C0DirectSum A) : ‖x‖ = ⨆ i, ‖eval A i x‖ := by
  change ‖x.1‖ = ⨆ i, ‖x.1 i‖
  exact lp.norm_eq_ciSup x.1

/-- Finite coordinate truncation inside the actual c₀-direct sum. -/
def truncate (s : Finset ι) (x : C0DirectSum A) : C0DirectSum A :=
  ∑ i ∈ s, single A i (eval A i x)

@[simp]
theorem eval_truncate (s : Finset ι) (x : C0DirectSum A) (j : ι) :
    eval A j (truncate A s x) = if j ∈ s then eval A j x else 0 := by
  classical
  simp only [truncate, map_sum, Finset.sum_apply]
  by_cases hj : j ∈ s
  · rw [Finset.sum_eq_single j]
    · simpa only [if_pos hj] using eval_single_same A j (eval A j x)
    · intro i hi hij
      exact eval_single_of_ne A (Ne.symm hij) (eval A i x)
    · exact fun h => (h hj).elim
  · have hne : ∀ i ∈ s, j ≠ i := by
      intro i hi hji
      exact hj (hji ▸ hi)
    rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro i hi
    exact eval_single_of_ne A (hne i hi) (eval A i x)

/-- A finite truncation has finite support, independently of the support of the
original element. -/
theorem finite_support_truncate (s : Finset ι) (x : C0DirectSum A) :
    Set.Finite {j : ι | eval A j (truncate A s x) ≠ 0} := by
  classical
  refine s.finite_toSet.subset ?_
  intro j hj
  by_contra hjs
  change j ∉ s at hjs
  have heval := eval_truncate A s x j
  rw [if_neg hjs] at heval
  exact hj heval

/-- A uniform coordinate estimate off `s` controls the norm of the truncation
remainder. -/
theorem norm_sub_truncate_le (s : Finset ι) (x : C0DirectSum A) {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ i, i ∉ s → ‖eval A i x‖ ≤ ε) :
    ‖x - truncate A s x‖ ≤ ε := by
  change ‖(x - truncate A s x).1‖ ≤ ε
  refine lp.norm_le_of_forall_le hε ?_
  intro i
  change ‖eval A i x - eval A i (truncate A s x)‖ ≤ ε
  rw [eval_truncate]
  by_cases hi : i ∈ s
  · simpa [hi] using hε
  · simpa [hi] using h i hi

/-- Finite truncations converge in norm to every c₀-family. -/
theorem exists_finset_norm_sub_truncate_lt (x : C0DirectSum A) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ι, ‖x - truncate A s x‖ < ε := by
  classical
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := half_pos hε
  have hfinite : Set.Finite {i : ι | δ ≤ ‖eval A i x‖} := by
    simpa only [eval_apply] using x.2 δ hδ
  let s : Finset ι := hfinite.toFinset
  refine ⟨s, (norm_sub_truncate_le A s x hδ.le ?_).trans_lt (half_lt_self hε)⟩
  intro i hi
  have hnot : ¬ δ ≤ ‖eval A i x‖ := by
    intro hlarge
    apply hi
    exact hfinite.mem_toFinset.2 hlarge
  exact le_of_lt (lt_of_not_ge hnot)


end C0DirectSum

end MathlibAnnex.Analysis.CStarAlgebra
