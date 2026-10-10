/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic

/-!
# Continuous biorthogonal sequences with prescribed small dual norms

Only the successive finite spans are finite dimensional. The ambient space need
not be complete or separable. No Schauder basis is chosen. Each extension first
subtracts the old finite-rank interpolation, applies Hahn--Banach to a nonzero
residual, and subtracts the old dual coordinates. Reciprocal rescaling preserves
biorthogonality while imposing an arbitrary positive bound on the new functional.

The private finite-stage subtype stores a finite invariant constructed below;
it is not a hypothesis containing the existence of the desired infinite sequence.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open scoped Classical

namespace NormedSpace

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Extend a finite biorthogonal family while making the new dual norm as small
as prescribed. The old functionals and vectors are not changed. -/
theorem exists_biorthogonal_extension (hX : ¬ FiniteDimensional 𝕜 X)
    {ι : Type*} [Fintype ι] (x : ι → X) (f : ι → StrongDual 𝕜 X)
    (h : ∀ i j, f i (x j) = if i = j then 1 else 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : X, ∃ g : StrongDual 𝕜 X,
      (∀ i, f i v = 0) ∧ (∀ i, g (x i) = 0) ∧ g v = 1 ∧ ‖g‖ ≤ ε := by
  classical
  let M : Submodule 𝕜 X := Submodule.span 𝕜 (Set.range x)
  haveI : FiniteDimensional 𝕜 M :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range x)
  have hM : M ≠ ⊤ := by
    intro heq
    haveI : FiniteDimensional 𝕜 (⊤ : Submodule 𝕜 X) := by
      rw [← heq]
      infer_instance
    exact hX (Module.Finite.of_surjective
      (Submodule.topEquiv : (⊤ : Submodule 𝕜 X) ≃ₗ[𝕜] X).toLinearMap
      Submodule.topEquiv.surjective)
  obtain ⟨z, hz⟩ : ∃ z : X, z ∉ M := by
    by_contra hn
    push_neg at hn
    exact hM (top_unique (fun z _ => hn z))
  let v : X := z - ∑ i, f i z • x i
  have hfv : ∀ i, f i v = 0 := by
    intro i
    simp [v, map_sum, map_smul, h, mul_ite]
  have hv : v ≠ 0 := by
    intro hv
    apply hz
    have hz' : z = ∑ i, f i z • x i := sub_eq_zero.mp hv
    rw [hz']
    exact Submodule.sum_mem M fun i _ =>
      M.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
  obtain ⟨g, hg, hgv⟩ := exists_dual_vector 𝕜 v (norm_ne_zero_iff.2 hv)
  let k : StrongDual 𝕜 X := g - ∑ i, g (x i) • f i
  have hkx : ∀ i, k (x i) = 0 := by
    intro i
    simp [k, h, mul_ite]
  have hkv : k v = (‖v‖ : 𝕜) := by
    simp [k, hfv, hgv]
  let l : StrongDual 𝕜 X := (‖v‖ : 𝕜)⁻¹ • k
  have hlv : l v = 1 := by
    have hn : (‖v‖ : 𝕜) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hv)
    simp [l, hkv, hn]
  have hlx : ∀ i, l (x i) = 0 := by intro i; simp [l, hkx]
  let r : ℝ := ε / (‖l‖ + 1)
  have hr : 0 < r := div_pos hε (by positivity)
  have hrk : (r : 𝕜) ≠ 0 := by exact_mod_cast hr.ne'
  refine ⟨(r : 𝕜)⁻¹ • v, (r : 𝕜) • l, ?_, ?_, ?_, ?_⟩
  · intro i; simp [map_smul, hfv]
  · intro i; simp [hlx]
  · simp [map_smul, hlv, hrk]
  · rw [norm_smul, RCLike.norm_ofReal, abs_of_pos hr]
    dsimp [r]
    calc
      ε / (‖l‖ + 1) * ‖l‖ ≤ ε / (‖l‖ + 1) * (‖l‖ + 1) := by
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one)
          (div_nonneg hε.le (by positivity))
      _ = ε := div_mul_cancel₀ _ (by positivity)

/-- A finite invariant, with no infinite-family existence assertion. -/
private def BiorthogonalStage (ε : ℕ → ℝ) (n : ℕ) :=
  {s : (ℕ → X) × (ℕ → StrongDual 𝕜 X) //
    ∀ i, i < n → ‖s.2 i‖ ≤ ε i ∧
      ∀ j, j < n → s.2 i (s.1 j) = if i = j then 1 else 0}

private def biorthogonalNext (hX : ¬ FiniteDimensional 𝕜 X)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (n : ℕ)
    (s : BiorthogonalStage (𝕜 := 𝕜) (X := X) ε n) :
    BiorthogonalStage (𝕜 := 𝕜) (X := X) ε (n + 1) := by
  classical
  let x : Fin n → X := fun i => s.val.1 i
  let f : Fin n → StrongDual 𝕜 X := fun i => s.val.2 i
  have hf : ∀ i j, f i (x j) = if i = j then 1 else 0 := by
    intro i j
    simpa [f, x, Fin.ext_iff] using (s.property i i.isLt).2 j j.isLt
  let hex := exists_biorthogonal_extension hX x f (by
    intro i j
    by_cases hij : i = j <;> simpa [hij] using hf i j) (hε n)
  let v : X := Classical.choose hex
  let g : StrongDual 𝕜 X := Classical.choose (Classical.choose_spec hex)
  have hg := Classical.choose_spec (Classical.choose_spec hex)
  have hfv := hg.1
  have hgx := hg.2.1
  have hgv := hg.2.2.1
  have hgn := hg.2.2.2
  change (∀ i, f i v = 0) at hfv
  change (∀ i, g (x i) = 0) at hgx
  change g v = 1 at hgv
  change ‖g‖ ≤ ε n at hgn
  refine ⟨(Function.update s.val.1 n v, Function.update s.val.2 n g), ?_⟩
  intro i hi
  by_cases hin : i = n
  · subst i
    refine ⟨by simpa using hgn, ?_⟩
    intro j hj
    by_cases hjn : j = n
    · subst j; simpa using hgv
    · have hj' : j < n := by omega
      simpa [Function.update_of_ne hjn, hjn, Ne.symm hjn, x] using hgx ⟨j, hj'⟩
  · have hi' : i < n := by omega
    refine ⟨by simpa [Function.update_of_ne hin] using (s.property i hi').1, ?_⟩
    intro j hj
    by_cases hjn : j = n
    · subst j
      simpa [Function.update_of_ne hin, hin, f] using hfv ⟨i, hi'⟩
    · have hj' : j < n := by omega
      simpa [Function.update_of_ne hin, Function.update_of_ne hjn]
        using (s.property i hi').2 j hj'

private theorem biorthogonalNext_agrees (hX : ¬ FiniteDimensional 𝕜 X)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (n : ℕ)
    (s : BiorthogonalStage (𝕜 := 𝕜) (X := X) ε n) {i : ℕ} (hi : i < n) :
    ((biorthogonalNext hX ε hε n s).val.1 i,
      (biorthogonalNext hX ε hε n s).val.2 i) = (s.val.1 i, s.val.2 i) := by
  classical
  simp only [biorthogonalNext, id_eq, Function.update_of_ne (ne_of_lt hi)]

private def biorthogonalStages (hX : ¬ FiniteDimensional 𝕜 X)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    (n : ℕ) → BiorthogonalStage (𝕜 := 𝕜) (X := X) ε n
  | 0 => ⟨(fun _ => 0, fun _ => 0), by intro i hi; omega⟩
  | n + 1 => biorthogonalNext hX ε hε n (biorthogonalStages hX ε hε n)

private theorem biorthogonalStages_agrees (hX : ¬ FiniteDimensional 𝕜 X)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) {n m i : ℕ}
    (hnm : n ≤ m) (hi : i < n) :
    ((biorthogonalStages hX ε hε m).val.1 i,
      (biorthogonalStages hX ε hε m).val.2 i) =
    ((biorthogonalStages hX ε hε n).val.1 i,
      (biorthogonalStages hX ε hε n).val.2 i) := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    exact (biorthogonalNext_agrees hX ε hε m _ (lt_of_lt_of_le hi hnm)).trans ih

/-- Every infinite-dimensional real or complex normed space has a continuous
biorthogonal sequence with any prescribed positive dual-norm bounds. -/
theorem exists_biorthogonal_sequence (hX : ¬ FiniteDimensional 𝕜 X)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∃ x : ℕ → X, ∃ f : ℕ → StrongDual 𝕜 X,
      (∀ i j, f i (x j) = if i = j then 1 else 0) ∧ (∀ i, ‖f i‖ ≤ ε i) := by
  classical
  let s := biorthogonalStages hX ε hε
  let x : ℕ → X := fun i => (s (i + 1)).val.1 i
  let f : ℕ → StrongDual 𝕜 X := fun i => (s (i + 1)).val.2 i
  refine ⟨x, f, ?_, ?_⟩
  · intro i j
    let N := max (i + 1) (j + 1)
    have hi : i < N := lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_left _ _)
    have hj : j < N := lt_of_lt_of_le (Nat.lt_succ_self j) (le_max_right _ _)
    have hfi : (s N).val.2 i = f i :=
      congrArg Prod.snd (biorthogonalStages_agrees hX ε hε (n := i + 1) (m := N) (i := i) (le_max_left _ _) (Nat.lt_succ_self i))
    have hxj : (s N).val.1 j = x j :=
      congrArg Prod.fst (biorthogonalStages_agrees hX ε hε (n := j + 1) (m := N) (i := j) (le_max_right _ _) (Nat.lt_succ_self j))
    simpa only [hfi, hxj] using ((s N).property i hi).2 j hj
  · intro i
    exact ((s (i + 1)).property i (Nat.lt_succ_self i)).1

/-- Convenient summable bounds; the first index is zero, and its bound is 1/2. -/
theorem exists_biorthogonal_sequence_norm_le_geometric (hX : ¬ FiniteDimensional 𝕜 X) :
    ∃ x : ℕ → X, ∃ f : ℕ → StrongDual 𝕜 X,
      (∀ i j, f i (x j) = if i = j then 1 else 0) ∧
      (∀ i, ‖f i‖ ≤ (1 / 2 : ℝ) ^ (i + 1)) :=
  exists_biorthogonal_sequence hX (fun i => (1 / 2 : ℝ) ^ (i + 1))
    (fun i => pow_pos (by norm_num) _)

/-- Unit-ball coefficients give a norm-convergent series in the actual strong
continuous dual. Completeness of the ambient vector space is not needed. -/
theorem summable_smul_of_norm_le_geometric (f : ℕ → StrongDual 𝕜 X)
    (hf : ∀ n, ‖f n‖ ≤ (1 / 2 : ℝ) ^ (n + 1))
    (d : ℕ → 𝕜) (hd : ∀ n, ‖d n‖ ≤ 1) : Summable (fun n => d n • f n) := by
  have hg : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
    simpa only [pow_succ] using
      (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_right (1 / 2)
  apply Summable.of_norm_bounded hg
  intro n
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_right (hd n) (norm_nonneg _)).trans (by simpa using hf n)

/-- Evaluation of the convergent strong-dual series is the prescribed coefficient,
including index zero. This is not a formal sum or a discontinuous algebraic dual. -/
theorem tsum_smul_apply_of_biorthogonal (x : ℕ → X) (f : ℕ → StrongDual 𝕜 X)
    (h : ∀ i j, f i (x j) = if i = j then 1 else 0)
    (d : ℕ → 𝕜) (hs : Summable (fun n => d n • f n)) (j : ℕ) :
    (∑' n, d n • f n) (x j) = d j := by
  classical
  let ev₀ : StrongDual 𝕜 X →ₗ[𝕜] 𝕜 :=
    { toFun := fun g => g (x j)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let ev : StrongDual 𝕜 X →L[𝕜] 𝕜 := ev₀.mkContinuous ‖x j‖ (by
    intro g
    change ‖g (x j)‖ ≤ ‖x j‖ * ‖g‖
    simpa only [mul_comm] using g.le_opNorm (x j))
  change ev (∑' n, d n • f n) = d j
  rw [ev.map_tsum hs]
  simp [ev, ev₀, h, smul_eq_mul, mul_ite]

end NormedSpace
