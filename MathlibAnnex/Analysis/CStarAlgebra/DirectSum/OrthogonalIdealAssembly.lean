/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.C0DirectSum
public import MathlibAnnex.Analysis.CStarAlgebra.Ideal.ClosedStarIdeal
public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Assembly of orthogonal closed C-star ideals as a c₀-direct sum

Let `J i` be an arbitrary family of concrete norm-closed two-sided star ideals
in a nonunital complex C-star algebra `A`.  If different ideals annihilate one
another, the ambient sum of a finitely supported family has norm equal to the
maximum of its coordinate norms.  Consequently the finite-support summation
map extends uniquely to an isometric nonunital star-algebra homomorphism from
the actual completed dependent `C0DirectSum` into `A`.

The range of this homomorphism is exactly the norm closure of the ambient
finite ideal sums.  A star-algebra equivalence with `A` is therefore obtained
from the explicit boundary hypothesis that these finite sums are norm dense.
This file does not construct the ideal family and does not prove that density
hypothesis for a particular ambient algebra.

No countability, separability, finiteness, or nonzero-fibre assumption is made.
The empty index type and zero ideals are included.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Function Set Topology
open scoped BigOperators CStarAlgebra ENNReal NNReal

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uι uA

variable {ι : Type uι} {A : Type uA} [NonUnitalCStarAlgebra A]

namespace ClosedStarIdeal

/-- The actual C-star algebra carried by one member of a family of closed
star ideals. -/
abbrev Fiber (J : ι → ClosedStarIdeal A) (i : ι) : Type uA :=
  (J i).toNonUnitalStarSubalgebra

/-- Different members of a family of concrete closed star ideals annihilate
one another in the ambient algebra.  Since the quantification is ordered, the
same hypothesis also supplies the reverse product after swapping the indices.
-/
def PairwiseOrthogonal (J : ι → ClosedStarIdeal A) : Prop :=
  ∀ ⦃i j : ι⦄, i ≠ j → ∀ (x : Fiber J i) (y : Fiber J j),
    (x : A) * (y : A) = 0

variable (J : ι → ClosedStarIdeal A)

/-- The set of actual finite ambient sums with one term from each selected
ideal.  Repetitions are unnecessary because every ideal is additively closed.
-/
def finiteSums : Set A :=
  {a | ∃ (s : Finset ι) (x : ∀ i, Fiber J i),
    a = ∑ i ∈ s, (x i : A)}

@[simp]
theorem zero_mem_finiteSums : (0 : A) ∈ finiteSums J := by
  classical
  refine ⟨∅, fun i => 0, ?_⟩
  simp

/-- A two-term C-star norm computation used in the finite orthogonal-sum
induction.  The four displayed cross terms are exactly what remains after
expanding `(a + b)⁎(a + b)` and the product of its two diagonal summands. -/
private theorem norm_add_eq_max_of_star_cross_eq_zero
    {a b : A}
    (hsab : star a * b = 0) (hsba : star b * a = 0)
    (hasb : a * star b = 0) (hbsa : b * star a = 0) :
    ‖a + b‖ = max ‖a‖ ‖b‖ := by
  let p : A := star a * a
  let q : A := star b * b
  have hpq : p * q = 0 := by
    dsimp [p, q]
    calc
      (star a * a) * (star b * b) = star a * (a * star b) * b := by
        simp only [mul_assoc]
      _ = 0 := by rw [hasb]; simp
  have hqp : q * p = 0 := by
    dsimp [p, q]
    calc
      (star b * b) * (star a * a) = star b * (b * star a) * a := by
        simp only [mul_assoc]
      _ = 0 := by rw [hbsa]; simp
  have hpq_comm : Commute p q := by
    change p * q = q * p
    rw [hpq, hqp]
  have hp_normal : IsStarNormal p := by
    dsimp [p]
    exact (IsSelfAdjoint.star_mul_self a).isStarNormal
  have hq_normal : IsStarNormal q := by
    dsimp [q]
    exact (IsSelfAdjoint.star_mul_self b).isStarNormal
  have hdiag : star (a + b) * (a + b) = p + q := by
    dsimp [p, q]
    simp only [star_add, add_mul, mul_add]
    rw [hsab, hsba]
    abel
  have hsq : ‖a + b‖ ^ 2 = max (‖a‖ ^ 2) (‖b‖ ^ 2) := by
    calc
      ‖a + b‖ ^ 2 = ‖star (a + b) * (a + b)‖ := by
        simpa only [pow_two] using
          (CStarRing.norm_star_mul_self (x := a + b)).symm
      _ = ‖p + q‖ := by rw [hdiag]
      _ = max ‖p‖ ‖q‖ :=
        hp_normal.norm_add_eq_max hq_normal hpq_comm hpq
      _ = max (‖a‖ ^ 2) (‖b‖ ^ 2) := by
        dsimp [p, q]
        simp only [CStarRing.norm_star_mul_self, pow_two]
  have hmaxsq : max (‖a‖ ^ 2) (‖b‖ ^ 2) = (max ‖a‖ ‖b‖) ^ 2 := by
    rcases le_total ‖a‖ ‖b‖ with hab | hba
    · have hs : ‖a‖ ^ 2 ≤ ‖b‖ ^ 2 := by
        nlinarith [norm_nonneg a, norm_nonneg b]
      simp [max_eq_right hab, max_eq_right hs]
    · have hs : ‖b‖ ^ 2 ≤ ‖a‖ ^ 2 := by
        nlinarith [norm_nonneg a, norm_nonneg b]
      simp [max_eq_left hba, max_eq_left hs]
  rw [hmaxsq] at hsq
  have hmax_nonneg : 0 ≤ max ‖a‖ ‖b‖ :=
    (norm_nonneg a).trans (le_max_left _ _)
  nlinarith [norm_nonneg (a + b), hmax_nonneg]

/-- The ambient norm of an actual finite sum from pairwise orthogonal ideals is
the supremum of the finitely many coordinate norms. -/
theorem nnnorm_sum_eq_sup (hJ : PairwiseOrthogonal J)
    (s : Finset ι) (x : ∀ i, Fiber J i) :
    ‖∑ i ∈ s, (x i : A)‖₊ = s.sup fun i => ‖x i‖₊ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert j s hj ih =>
      have hsab : star (x j : A) * ∑ i ∈ s, (x i : A) = 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_eq_zero
        intro i hi
        have hji : j ≠ i := fun h => hj (h.symm ▸ hi)
        simpa using hJ hji (star (x j)) (x i)
      have hsba : star (∑ i ∈ s, (x i : A)) * (x j : A) = 0 := by
        rw [star_sum, Finset.sum_mul]
        apply Finset.sum_eq_zero
        intro i hi
        have hij : i ≠ j := fun h => hj (h ▸ hi)
        simpa using hJ hij (star (x i)) (x j)
      have hasb : (x j : A) * star (∑ i ∈ s, (x i : A)) = 0 := by
        rw [star_sum, Finset.mul_sum]
        apply Finset.sum_eq_zero
        intro i hi
        have hji : j ≠ i := fun h => hj (h.symm ▸ hi)
        simpa using hJ hji (x j) (star (x i))
      have hbsa : (∑ i ∈ s, (x i : A)) * star (x j : A) = 0 := by
        rw [Finset.sum_mul]
        apply Finset.sum_eq_zero
        intro i hi
        have hij : i ≠ j := fun h => hj (h ▸ hi)
        simpa using hJ hij (x i) (star (x j))
      have ih' : ‖∑ i ∈ s, (x i : A)‖ =
          ((s.sup fun i => ‖x i‖₊ : ℝ≥0) : ℝ) := by
        simpa only [coe_nnnorm] using congrArg (fun t : ℝ≥0 => (t : ℝ)) ih
      apply NNReal.eq
      change ‖∑ i ∈ insert j s, (x i : A)‖ = ((insert j s).sup fun i => ‖x i‖₊ : ℝ≥0)
      rw [Finset.sum_insert hj,
        norm_add_eq_max_of_star_cross_eq_zero hsab hsba hasb hbsa,
        Finset.sup_insert, NNReal.coe_max, ih']
      rfl

/-- Real-norm form of `nnnorm_sum_eq_sup`. -/
theorem norm_sum_eq_sup (hJ : PairwiseOrthogonal J)
    (s : Finset ι) (x : ∀ i, Fiber J i) :
    ‖∑ i ∈ s, (x i : A)‖ = ((s.sup fun i => ‖x i‖₊ : ℝ≥0) : ℝ) := by
  simpa only [coe_nnnorm] using congrArg (fun t : ℝ≥0 => (t : ℝ)) (nnnorm_sum_eq_sup J hJ s x)

/-- Every finitely supported bounded family belongs to the actual completed
c₀-direct sum. -/
private theorem vanishesAtInfinity_of_finite_support
    {x : lp (Fiber J) ∞} (hx : Set.Finite {i : ι | x i ≠ 0}) :
    C0DirectSum.VanishesAtInfinity (Fiber J) x := by
  intro ε hε
  refine hx.subset ?_
  intro i hi
  change ε ≤ ‖x i‖ at hi
  change x i ≠ 0
  intro hxi
  rw [hxi, norm_zero] at hi
  exact (not_lt_of_ge hi) hε

/-- The finitely supported star subalgebra embeds into the actual completed
c₀-direct sum without changing its underlying bounded family. -/
def finiteSupportInclusion :
    C0DirectSum.finiteSupportStarSubalgebra (Fiber J) →⋆ₙₐ[ℂ]
      C0DirectSum (Fiber J) where
  toFun x := ⟨x.1, by exact vanishesAtInfinity_of_finite_support J x.2⟩
  map_zero' := by apply Subtype.ext; rfl
  map_add' := by intro x y; apply Subtype.ext; rfl
  map_mul' := by intro x y; apply Subtype.ext; rfl
  map_smul' := by intro c x; apply Subtype.ext; rfl
  map_star' := by intro x; apply Subtype.ext; rfl

@[simp]
theorem coe_finiteSupportInclusion
    (x : C0DirectSum.finiteSupportStarSubalgebra (Fiber J)) :
    (finiteSupportInclusion J x : lp (Fiber J) ∞) = x.1 := rfl

@[simp]
theorem norm_finiteSupportInclusion
    (x : C0DirectSum.finiteSupportStarSubalgebra (Fiber J)) :
    ‖finiteSupportInclusion J x‖ = ‖x‖ := rfl

/-- The finite-support inclusion has dense range in the actual c₀-direct sum.
This statement is valid for arbitrary index types. -/
theorem denseRange_finiteSupportInclusion :
    DenseRange (finiteSupportInclusion J) := by
  classical
  refine Metric.denseRange_iff.mpr ?_
  intro x ε hε
  obtain ⟨s, hs⟩ := C0DirectSum.exists_finset_norm_sub_truncate_lt
    (Fiber J) x hε
  let y : C0DirectSum.finiteSupportStarSubalgebra (Fiber J) :=
    ⟨(C0DirectSum.truncate (Fiber J) s x).1, by
      change Set.Finite {i | (C0DirectSum.truncate (Fiber J) s x).1 i ≠ 0}
      exact C0DirectSum.finite_support_truncate (Fiber J) s x⟩
  have hy : finiteSupportInclusion J y = C0DirectSum.truncate (Fiber J) s x := rfl
  refine ⟨y, ?_⟩
  simpa only [hy, dist_eq_norm, norm_sub_rev] using hs

/-- The exact finite support of a bounded family, viewed as a finset. -/
private def supportFinset
    (x : C0DirectSum.finiteSupportStarSubalgebra (Fiber J)) : Finset ι :=
  x.2.toFinset

@[simp]
private theorem mem_supportFinset
    (x : C0DirectSum.finiteSupportStarSubalgebra (Fiber J)) (i : ι) :
    i ∈ supportFinset J x ↔ x.1 i ≠ 0 := by
  classical
  exact x.2.mem_toFinset

/-- The ambient sum of one finitely supported family. -/
private def finiteSupportSumValue
    (x : C0DirectSum.finiteSupportStarSubalgebra (Fiber J)) : A :=
  ∑ i ∈ supportFinset J x, (x.1 i : A)

/-- The support finset in `finiteSupportSumValue` may be replaced by any
larger finset on which the family is zero off its exact support. -/
private theorem finiteSupportSumValue_eq_sum_of_support_subset
    (x : C0DirectSum.finiteSupportStarSubalgebra (Fiber J))
    (s : Finset ι) (hxs : supportFinset J x ⊆ s) :
    finiteSupportSumValue J x = ∑ i ∈ s, (x.1 i : A) := by
  classical
  unfold finiteSupportSumValue
  rw [Finset.sum_subset hxs]
  intro i hi his
  have hzero : x.1 i = 0 := by
    by_contra hne
    exact his ((mem_supportFinset J x i).2 hne)
  simp [hzero]

/-- The norm of a finitely supported bounded family is the supremum over its
exact finite support. -/
private theorem nnnorm_eq_support_sup
    (x : C0DirectSum.finiteSupportStarSubalgebra (Fiber J)) :
    ‖x‖₊ = (supportFinset J x).sup fun i => ‖x.1 i‖₊ := by
  classical
  apply le_antisymm
  · apply NNReal.coe_le_coe.mp
    change ‖x.1‖ ≤ (((supportFinset J x).sup fun i => ‖x.1 i‖₊ : ℝ≥0) : ℝ)
    refine lp.norm_le_of_forall_le (NNReal.coe_nonneg ((supportFinset J x).sup fun i => ‖x.1 i‖₊)) ?_
    intro i
    by_cases hi : x.1 i = 0
    · simp [hi]
    · change (‖x.1 i‖₊ : ℝ) ≤ _
      exact NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun i => ‖x.1 i‖₊) ((mem_supportFinset J x i).2 hi))
  · apply Finset.sup_le
    intro i hi
    apply NNReal.coe_le_coe.mp
    exact lp.norm_apply_le_norm (by simp) x.1 i

/-- Finite-support summation into the ambient algebra.  Orthogonality is used
only for multiplication; additivity, scalar compatibility, and star
compatibility are the ordinary finite-sum identities. -/
def finiteSupportSum (hJ : PairwiseOrthogonal J) :
    C0DirectSum.finiteSupportStarSubalgebra (Fiber J) →⋆ₙₐ[ℂ] A where
  toFun x := ∑ i ∈ x.2.toFinset, (x.1 i : A)
  map_zero' := by
    change finiteSupportSumValue J 0 = 0
    simp [finiteSupportSumValue, supportFinset]
  map_add' := by
    intro x y
    change finiteSupportSumValue J (x + y) = finiteSupportSumValue J x + finiteSupportSumValue J y
    classical
    let s := supportFinset J x ∪ supportFinset J y
    have hxs : supportFinset J x ⊆ s := Finset.subset_union_left
    have hys : supportFinset J y ⊆ s := Finset.subset_union_right
    have hxys : supportFinset J (x + y) ⊆ s := by
      intro i hi
      have hxyne : x.1 i + y.1 i ≠ 0 :=
        (mem_supportFinset J (x + y) i).1 hi
      by_contra his
      have hxi : x.1 i = 0 := by
        by_contra hxne
        exact his (Finset.mem_union_left _ ((mem_supportFinset J x i).2 hxne))
      have hyi : y.1 i = 0 := by
        by_contra hyne
        exact his (Finset.mem_union_right _ ((mem_supportFinset J y i).2 hyne))
      exact hxyne (by simp [hxi, hyi])
    rw [finiteSupportSumValue_eq_sum_of_support_subset J (x + y) s hxys,
      finiteSupportSumValue_eq_sum_of_support_subset J x s hxs,
      finiteSupportSumValue_eq_sum_of_support_subset J y s hys]
    change (∑ i ∈ s, ((x.1 i : A) + (y.1 i : A))) =
      (∑ i ∈ s, (x.1 i : A)) + ∑ i ∈ s, (y.1 i : A)
    rw [Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    change finiteSupportSumValue J (c • x) = c • finiteSupportSumValue J x
    classical
    have hsub : supportFinset J (c • x) ⊆ supportFinset J x := by
      intro i hi
      have hne : c • x.1 i ≠ 0 := (mem_supportFinset J (c • x) i).1 hi
      by_contra hxi
      have hzero : x.1 i = 0 := by
        by_contra hxne
        exact hxi ((mem_supportFinset J x i).2 hxne)
      exact hne (by simp only [hzero, smul_zero])
    rw [finiteSupportSumValue_eq_sum_of_support_subset J (c • x)
        (supportFinset J x) hsub]
    change (∑ i ∈ supportFinset J x, c • (x.1 i : A)) =
      c • (∑ i ∈ supportFinset J x, (x.1 i : A))
    rw [Finset.smul_sum]
  map_star' := by
    intro x
    change finiteSupportSumValue J (star x) = star (finiteSupportSumValue J x)
    classical
    have hsub : supportFinset J (star x) ⊆ supportFinset J x := by
      intro i hi
      have hne : star (x.1 i) ≠ 0 := (mem_supportFinset J (star x) i).1 hi
      by_contra hxi
      have hzero : x.1 i = 0 := by
        by_contra hxne
        exact hxi ((mem_supportFinset J x i).2 hxne)
      exact hne (by simp only [hzero, star_zero])
    rw [finiteSupportSumValue_eq_sum_of_support_subset J (star x)
        (supportFinset J x) hsub]
    change (∑ i ∈ supportFinset J x, star (x.1 i : A)) =
      star (∑ i ∈ supportFinset J x, (x.1 i : A))
    rw [star_sum]
  map_mul' := by
    intro x y
    change finiteSupportSumValue J (x * y) = finiteSupportSumValue J x * finiteSupportSumValue J y
    classical
    let s := supportFinset J x ∪ supportFinset J y
    have hxs : supportFinset J x ⊆ s := Finset.subset_union_left
    have hys : supportFinset J y ⊆ s := Finset.subset_union_right
    have hxys : supportFinset J (x * y) ⊆ s := by
      intro i hi
      have hne : x.1 i * y.1 i ≠ 0 :=
        (mem_supportFinset J (x * y) i).1 hi
      by_contra his
      have hxi : x.1 i = 0 := by
        by_contra hxne
        exact his (Finset.mem_union_left _ ((mem_supportFinset J x i).2 hxne))
      exact hne (by simp [hxi])
    rw [finiteSupportSumValue_eq_sum_of_support_subset J (x * y) s hxys,
      finiteSupportSumValue_eq_sum_of_support_subset J x s hxs,
      finiteSupportSumValue_eq_sum_of_support_subset J y s hys]
    change (∑ i ∈ s, ((x.1 i : A) * (y.1 i : A))) =
      (∑ i ∈ s, (x.1 i : A)) * ∑ i ∈ s, (y.1 i : A)
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    rw [Finset.sum_eq_single i]
    · intro j hj hji
      simpa using hJ hji.symm (x.1 i) (y.1 j)
    · exact fun hnot => (hnot hi).elim

@[simp]
theorem finiteSupportSum_apply (hJ : PairwiseOrthogonal J)
    (x : C0DirectSum.finiteSupportStarSubalgebra (Fiber J)) :
    finiteSupportSum J hJ x = ∑ i ∈ x.2.toFinset, (x.1 i : A) := rfl

private theorem nnnorm_finiteSupportSum (hJ : PairwiseOrthogonal J)
    (x : C0DirectSum.finiteSupportStarSubalgebra (Fiber J)) :
    ‖finiteSupportSum J hJ x‖₊ = ‖x‖₊ := by
  change ‖finiteSupportSumValue J x‖₊ = ‖x‖₊
  rw [finiteSupportSumValue, nnnorm_sum_eq_sup J hJ]
  exact (nnnorm_eq_support_sup J x).symm

@[simp]
theorem norm_finiteSupportSum (hJ : PairwiseOrthogonal J)
    (x : C0DirectSum.finiteSupportStarSubalgebra (Fiber J)) :
    ‖finiteSupportSum J hJ x‖ = ‖x‖ := by
  simpa only [coe_nnnorm] using congrArg (fun t : ℝ≥0 => (t : ℝ)) (nnnorm_finiteSupportSum J hJ x)

/-- The underlying continuous linear extension of finite-support summation to
the completed c₀-direct sum. -/
private def c0SumLinearMap (hJ : PairwiseOrthogonal J) :
    C0DirectSum (Fiber J) →L[ℂ] A :=
  ({ toFun := finiteSupportSum J hJ, map_add' := map_add _, map_smul' := fun c x => by exact map_smul (finiteSupportSum J hJ) c x } : C0DirectSum.finiteSupportStarSubalgebra (Fiber J) →ₗ[ℂ] A).extendOfNorm
    ({ toFun := finiteSupportInclusion J, map_add' := map_add _, map_smul' := fun c x => by exact map_smul (finiteSupportInclusion J) c x } : C0DirectSum.finiteSupportStarSubalgebra (Fiber J) →ₗ[ℂ] C0DirectSum (Fiber J))

@[simp]
private theorem c0SumLinearMap_finiteSupportInclusion
    (hJ : PairwiseOrthogonal J)
    (x : C0DirectSum.finiteSupportStarSubalgebra (Fiber J)) :
    c0SumLinearMap J hJ (finiteSupportInclusion J x) =
      finiteSupportSum J hJ x := by
  apply LinearMap.extendOfNorm_eq
    (f := ({ toFun := finiteSupportSum J hJ, map_add' := map_add _, map_smul' := fun c x => by exact map_smul (finiteSupportSum J hJ) c x } : C0DirectSum.finiteSupportStarSubalgebra (Fiber J) →ₗ[ℂ] A))
    (e := ({ toFun := finiteSupportInclusion J, map_add' := map_add _, map_smul' := fun c x => by exact map_smul (finiteSupportInclusion J) c x } : C0DirectSum.finiteSupportStarSubalgebra (Fiber J) →ₗ[ℂ] C0DirectSum (Fiber J)))
    (denseRange_finiteSupportInclusion J)
  refine ⟨1, ?_⟩
  intro y
  change ‖finiteSupportSum J hJ y‖ ≤ 1 * ‖finiteSupportInclusion J y‖
  rw [one_mul, norm_finiteSupportSum, norm_finiteSupportInclusion]

/-- The extension remains norm preserving on the completed c₀-direct sum. -/
private theorem norm_c0SumLinearMap (hJ : PairwiseOrthogonal J)
    (x : C0DirectSum (Fiber J)) :
    ‖c0SumLinearMap J hJ x‖ = ‖x‖ := by
  have hdense : DenseRange (finiteSupportInclusion J) :=
    denseRange_finiteSupportInclusion J
  have hclosed : IsClosed {z : C0DirectSum (Fiber J) |
      ‖c0SumLinearMap J hJ z‖ = ‖z‖} :=
    isClosed_eq (continuous_norm.comp (c0SumLinearMap J hJ).continuous) continuous_norm
  refine DenseRange.induction_on hdense x hclosed ?_
  intro y
  rw [c0SumLinearMap_finiteSupportInclusion, norm_finiteSupportSum,
    norm_finiteSupportInclusion]

/-- The isometric nonunital star-algebra homomorphism from the actual completed
c₀-direct sum of a pairwise orthogonal ideal family into the ambient algebra.
-/
def c0SumHom (hJ : PairwiseOrthogonal J) :
    C0DirectSum (Fiber J) →⋆ₙₐ[ℂ] A where
  toFun := ({ toFun := finiteSupportSum J hJ, map_add' := map_add _, map_smul' := fun c x => by exact map_smul (finiteSupportSum J hJ) c x } : C0DirectSum.finiteSupportStarSubalgebra (Fiber J) →ₗ[ℂ] A).extendOfNorm ({ toFun := finiteSupportInclusion J, map_add' := map_add _, map_smul' := fun c x => by exact map_smul (finiteSupportInclusion J) c x } : C0DirectSum.finiteSupportStarSubalgebra (Fiber J) →ₗ[ℂ] C0DirectSum (Fiber J))
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' := by
    intro x y
    change c0SumLinearMap J hJ (x * y) = c0SumLinearMap J hJ x * c0SumLinearMap J hJ y
    have hdense : DenseRange (finiteSupportInclusion J) :=
      denseRange_finiteSupportInclusion J
    refine DenseRange.induction_on₂ hdense ?_ ?_ x y
    · exact isClosed_eq
        ((c0SumLinearMap J hJ).continuous.comp continuous_mul)
        (((c0SumLinearMap J hJ).continuous.comp continuous_fst).mul
          ((c0SumLinearMap J hJ).continuous.comp continuous_snd))
    · intro u v
      rw [← map_mul (finiteSupportInclusion J),
        c0SumLinearMap_finiteSupportInclusion,
        c0SumLinearMap_finiteSupportInclusion,
        c0SumLinearMap_finiteSupportInclusion]
      exact map_mul (finiteSupportSum J hJ) u v
  map_star' := by
    intro x
    change c0SumLinearMap J hJ (star x) = star (c0SumLinearMap J hJ x)
    have hdense : DenseRange (finiteSupportInclusion J) :=
      denseRange_finiteSupportInclusion J
    refine DenseRange.induction_on hdense x ?_ ?_
    · exact isClosed_eq
        ((c0SumLinearMap J hJ).continuous.comp continuous_star)
        (continuous_star.comp (c0SumLinearMap J hJ).continuous)
    · intro y
      rw [← map_star (finiteSupportInclusion J),
        c0SumLinearMap_finiteSupportInclusion,
        c0SumLinearMap_finiteSupportInclusion]
      exact map_star (finiteSupportSum J hJ) y

@[simp]
theorem norm_c0SumHom (hJ : PairwiseOrthogonal J)
    (x : C0DirectSum (Fiber J)) :
    ‖c0SumHom J hJ x‖ = ‖x‖ :=
  norm_c0SumLinearMap J hJ x

/-- The completed orthogonal-ideal assembly map is an isometry. -/
theorem isometry_c0SumHom (hJ : PairwiseOrthogonal J) :
    Isometry (c0SumHom J hJ) := by
  rw [AddMonoidHomClass.isometry_iff_norm]
  exact norm_c0SumHom J hJ

/-- The completed orthogonal-ideal assembly map is injective. -/
theorem c0SumHom_injective (hJ : PairwiseOrthogonal J) :
    Function.Injective (c0SumHom J hJ) :=
  (isometry_c0SumHom J hJ).injective

/-- A single c₀-coordinate is sent to the corresponding ambient ideal element.
-/
@[simp]
theorem c0SumHom_single (hJ : PairwiseOrthogonal J) (i : ι) (x : Fiber J i) :
    c0SumHom J hJ (C0DirectSum.single (Fiber J) i x) = (x : A) := by
  classical
  let y : C0DirectSum.finiteSupportStarSubalgebra (Fiber J) :=
    ⟨(C0DirectSum.single (Fiber J) i x).1, by
      refine Set.finite_singleton i |>.subset ?_
      intro j hj
      simp only [Set.mem_singleton_iff]
      by_contra hji
      have hz : C0DirectSum.eval (Fiber J) j
          (C0DirectSum.single (Fiber J) i x) = 0 :=
        C0DirectSum.eval_single_of_ne (Fiber J) hji x
      exact hj (by simpa only [C0DirectSum.eval_apply] using hz)⟩
  have hy : finiteSupportInclusion J y = C0DirectSum.single (Fiber J) i x := rfl
  rw [← hy]
  change c0SumLinearMap J hJ (finiteSupportInclusion J y) = (x : A)
  rw [c0SumLinearMap_finiteSupportInclusion]
  change finiteSupportSumValue J y = (x : A)
  rw [finiteSupportSumValue_eq_sum_of_support_subset J y {i}]
  · rw [Finset.sum_singleton]
    change (C0DirectSum.eval (Fiber J) i
      (C0DirectSum.single (Fiber J) i x) : A) = (x : A)
    exact congrArg (fun z : Fiber J i => (z : A))
      (C0DirectSum.eval_single_same (Fiber J) i x)
  · intro j hj
    have hjne : y.1 j ≠ 0 := (mem_supportFinset J y j).1 hj
    by_contra hji
    have hji' : j ≠ i := by simpa using hji
    have hz : y.1 j = 0 := by
      change C0DirectSum.eval (Fiber J) j
        (C0DirectSum.single (Fiber J) i x) = 0
      exact C0DirectSum.eval_single_of_ne (Fiber J) hji' x
    exact hjne hz

/-- Finite coordinate truncations are sent to the corresponding actual ambient
finite sums. -/
@[simp]
theorem c0SumHom_truncate (hJ : PairwiseOrthogonal J)
    (s : Finset ι) (x : C0DirectSum (Fiber J)) :
    c0SumHom J hJ (C0DirectSum.truncate (Fiber J) s x) =
      ∑ i ∈ s, (C0DirectSum.eval (Fiber J) i x : A) := by
  simp only [C0DirectSum.truncate, map_sum, c0SumHom_single]

/-- Every actual finite ideal sum lies in the range of the completed c₀
assembly map. -/
theorem finiteSums_subset_range_c0SumHom (hJ : PairwiseOrthogonal J) :
    finiteSums J ⊆ Set.range (c0SumHom J hJ) := by
  classical
  rintro a ⟨s, x, rfl⟩
  refine ⟨∑ i ∈ s, C0DirectSum.single (Fiber J) i (x i), ?_⟩
  simp

/-- The range of the completed c₀ assembly map is exactly the norm closure of
the actual finite ideal sums. -/
theorem range_c0SumHom_eq_closure_finiteSums (hJ : PairwiseOrthogonal J) :
    Set.range (c0SumHom J hJ) = closure (finiteSums J) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    refine Metric.mem_closure_iff.mpr ?_
    intro ε hε
    obtain ⟨s, hs⟩ := C0DirectSum.exists_finset_norm_sub_truncate_lt
      (Fiber J) x hε
    refine ⟨c0SumHom J hJ (C0DirectSum.truncate (Fiber J) s x), ?_, ?_⟩
    · refine ⟨s, fun i => C0DirectSum.eval (Fiber J) i x, ?_⟩
      exact c0SumHom_truncate J hJ s x
    · rw [dist_eq_norm, ← map_sub (c0SumHom J hJ), norm_c0SumHom]
      exact hs
  · apply closure_minimal (finiteSums_subset_range_c0SumHom J hJ)
    exact (isometry_c0SumHom J hJ).isClosedEmbedding.isClosed_range

/-- Explicit norm density of the actual finite ideal sums is precisely the
boundary hypothesis needed for surjectivity of the assembly map. -/
theorem c0SumHom_surjective (hJ : PairwiseOrthogonal J)
    (hdense : Dense (finiteSums J)) :
    Function.Surjective (c0SumHom J hJ) := by
  intro a
  have ha : a ∈ closure (finiteSums J) := by
    rw [hdense.closure_eq]
    exact Set.mem_univ a
  rw [← range_c0SumHom_eq_closure_finiteSums J hJ] at ha
  exact ha

/-- The C-star equivalence obtained from a pairwise orthogonal ideal family and
the explicit hypothesis that its actual finite ambient sums are norm dense.
The theorem does not produce either the family or the density proof. -/
def c0SumEquivOfDense (hJ : PairwiseOrthogonal J)
    (hdense : Dense (finiteSums J)) :
    C0DirectSum (Fiber J) ≃⋆ₐ[ℂ] A :=
  { Equiv.ofBijective (c0SumHom J hJ)
      ⟨c0SumHom_injective J hJ, c0SumHom_surjective J hJ hdense⟩ with
    map_add' := map_add (c0SumHom J hJ)
    map_mul' := map_mul (c0SumHom J hJ)
    map_smul' := map_smul (c0SumHom J hJ)
    map_star' := map_star (c0SumHom J hJ) }

@[simp]
theorem c0SumEquivOfDense_apply (hJ : PairwiseOrthogonal J)
    (hdense : Dense (finiteSums J)) (x : C0DirectSum (Fiber J)) :
    c0SumEquivOfDense J hJ hdense x = c0SumHom J hJ x := rfl

@[simp]
theorem norm_c0SumEquivOfDense (hJ : PairwiseOrthogonal J)
    (hdense : Dense (finiteSums J)) (x : C0DirectSum (Fiber J)) :
    ‖c0SumEquivOfDense J hJ hdense x‖ = ‖x‖ :=
  norm_c0SumHom J hJ x

end ClosedStarIdeal

end MathlibAnnex.Analysis.CStarAlgebra
