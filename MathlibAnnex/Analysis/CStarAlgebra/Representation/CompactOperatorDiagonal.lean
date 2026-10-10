/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Hom
import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.CompactOperators
import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.CoordinateIdeal
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Atomic
import MathlibAnnex.Analysis.InnerProductSpace.HilbertSumCoordinates

/-!
# Diagonal representations of compact-operator families

The bounded product in this file is an `lp _ ∞` C-star algebra of operator
families.  Its representation space is the genuinely completed dependent
Hilbert sum `HilbertSum H = lp H 2`.  These two `lp` constructions are kept
separate throughout.

A bounded compact-operator family acts coordinatewise on the Hilbert sum.  The
construction is the existing arbitrary-index atomic representation, so
square-summability, boundedness, multiplication, and star-adjoint compatibility
come from the bounded diagonal map on `lp H 2`.  Restricting the source to the
actual dependent c₀-sum gives a faithful isometric representation.  Finite
coordinate truncations act compactly, and norm closure then proves that every
c₀-family acts by a compact operator.  Conversely, total boundedness of the
image of the unit ball forces the fibre norms of every compact diagonal action
to vanish at infinity.  Thus the compact part of the bounded block-diagonal
range is literally the c₀ block-diagonal range.  No countability, separability,
or common fibre hypothesis is used.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

open Filter Set Topology
open scoped BigOperators CStarAlgebra ENNReal lp

namespace MathlibAnnex.Analysis.CStarAlgebra

open MathlibAnnex.Analysis.InnerProductSpace

universe uι uH


private theorem rangeRestrictionOnto {X Y : Type*}
    [NonUnitalCStarAlgebra X] [NonUnitalCStarAlgebra Y]
    (f : X →⋆ₙₐ[ℂ] Y) : Function.Surjective (NonUnitalStarAlgHom.rangeRestrict f) := by
  intro y
  obtain ⟨x, hx⟩ := (NonUnitalStarAlgHom.mem_range f).1 y.property
  exact ⟨x, Subtype.ext hx⟩

private theorem equivalenceFromBijective_val {X Y : Type*} {P : Y → Prop}
    (f : X → Subtype P) (hf : Function.Bijective f) (x : X) :
    (Equiv.ofBijective f hf x).val = (f x).val := rfl


/-- The dependent bounded product of concrete compact-operator C-star
algebras.  This is an `lp _ ∞` algebra, not the Hilbert representation space. -/
abbrev CompactOperatorBoundedProduct {ι : Type uι} (H : ι → Type uH)
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)] :=
  lp (fun i => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i)) ∞

namespace CompactOperatorBoundedProduct

variable {ι : Type uι} (H : ι → Type uH)
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

private abbrev Fiber (i : ι) :=
  ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i)


/-- Evaluation of a bounded compact-operator family at one coordinate. -/
def coordinateEvaluation (i : ι) :
    CompactOperatorBoundedProduct H →⋆ₙₐ[ℂ] Fiber H i where
  toFun := fun x => x i
  map_zero' := rfl
  map_add' := fun _ _ => rfl
  map_mul' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  map_star' := fun _ => rfl

@[simp]
theorem coordinateEvaluation_apply (i : ι)
    (x : CompactOperatorBoundedProduct H) :
    coordinateEvaluation H i x = x i := rfl


/-- The concrete action of one coordinate of the bounded product. -/
def coordinateRepresentation (i : ι) :
    NonUnitalCStarRepresentation (CompactOperatorBoundedProduct H) (H i) :=
  (compactOperatorRepresentation (H i)).comp (coordinateEvaluation H i)

@[simp]
theorem coordinateRepresentation_apply (i : ι)
    (x : CompactOperatorBoundedProduct H) (v : H i) :
    coordinateRepresentation H i x v =
      ((x i : Fiber H i) : H i →L[ℂ] H i) v := rfl


/-- A bounded family of compact operators acts diagonally on the genuine
completed dependent Hilbert `lp 2` sum. -/
def diagonalRepresentation :
    NonUnitalCStarRepresentation (CompactOperatorBoundedProduct H)
      (HilbertSum H) :=
  (atomicRepresentation (fun i => (coordinateRepresentation H i).unitization)).toNonUnitalStarAlgHom.comp
      (Unitization.inrNonUnitalStarAlgHom ℂ (CompactOperatorBoundedProduct H))

@[simp]
theorem diagonalRepresentation_apply
    (x : CompactOperatorBoundedProduct H) (v : HilbertSum H) (i : ι) :
    diagonalRepresentation H x v i =
      ((x i : Fiber H i) : H i →L[ℂ] H i) (v i) := by
  simp [diagonalRepresentation, coordinateRepresentation,
    coordinateEvaluation, atomicRepresentation_apply, NonUnitalCStarRepresentation.unitization_inr]
  rfl

@[simp]
theorem diagonalRepresentation_add
    (x y : CompactOperatorBoundedProduct H) :
    diagonalRepresentation H (x + y) =
      diagonalRepresentation H x + diagonalRepresentation H y :=
  map_add (diagonalRepresentation H) x y

@[simp]
theorem diagonalRepresentation_smul (c : ℂ)
    (x : CompactOperatorBoundedProduct H) :
    diagonalRepresentation H (c • x) = c • diagonalRepresentation H x :=
  map_smul (diagonalRepresentation H) c x

@[simp]
theorem diagonalRepresentation_mul
    (x y : CompactOperatorBoundedProduct H) :
    diagonalRepresentation H (x * y) =
      diagonalRepresentation H x * diagonalRepresentation H y :=
  map_mul (diagonalRepresentation H) x y


/-- The source star is represented by the Hilbert-space adjoint. -/
theorem adjoint_diagonalRepresentation
    (x : CompactOperatorBoundedProduct H) :
    ContinuousLinearMap.adjoint (diagonalRepresentation H x) =
      diagonalRepresentation H (star x) := by
  simpa only [ContinuousLinearMap.star_eq_adjoint] using
    (map_star (diagonalRepresentation H) x).symm


/-- On a single Hilbert coordinate the diagonal action is the given fibre
operator, embedded back into that coordinate. -/
@[simp]
theorem diagonalRepresentation_coordinateEmbedding [DecidableEq ι]
    (x : CompactOperatorBoundedProduct H) (i : ι) (v : H i) :
    diagonalRepresentation H x (coordinateEmbedding i v) =
      coordinateEmbedding i (((x i : Fiber H i) : H i →L[ℂ] H i) v) := by
  classical
  apply lp.ext
  funext j
  by_cases hji : j = i
  · subst j
    simp [diagonalRepresentation_apply, coordinateEmbedding_apply, lp.coeFn_single]
  · simp [diagonalRepresentation_apply, coordinateEmbedding_apply, lp.coeFn_single,
      hji, Ne.symm hji]


/-- Coordinate projection commutes with the diagonal action in the expected
pointwise form. -/
@[simp]
theorem coordinateProjection_diagonalRepresentation [DecidableEq ι]
    (x : CompactOperatorBoundedProduct H) (v : HilbertSum H) (i : ι) :
    coordinateProjection i (diagonalRepresentation H x v) =
      ((x i : Fiber H i) : H i →L[ℂ] H i) (coordinateProjection i v) := by
  classical
  simp [coordinateProjection_apply, diagonalRepresentation_apply]


/-- The bounded-product diagonal representation remembers every coordinate. -/
theorem diagonalRepresentation_injective :
    Function.Injective (diagonalRepresentation H) := by
  classical
  intro x y hxy
  apply lp.ext
  funext i
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg
    (fun T : HilbertSum H →L[ℂ] HilbertSum H =>
      coordinateProjection i (T (coordinateEmbedding i v))) hxy
  simpa [coordinateProjection_diagonalRepresentation, coordinateEmbedding_apply,
    coordinateProjection_apply, lp.coeFn_single] using h


/-- Faithfulness upgrades the bounded-product diagonal representation to an
isometry. -/
theorem isometry_diagonalRepresentation :
    Isometry (diagonalRepresentation H) :=
  NonUnitalStarAlgHom.isometry (diagonalRepresentation H)
    (diagonalRepresentation_injective H)


/-- Contractivity of the diagonal action, before using faithfulness. -/
theorem norm_diagonalRepresentation_le
    (x : CompactOperatorBoundedProduct H) :
    ‖diagonalRepresentation H x‖ ≤ ‖x‖ :=
  NonUnitalStarAlgHom.norm_apply_le (diagonalRepresentation H) x


/-- The operator norm of a bounded diagonal family is its supremum-family
norm. -/
@[simp]
theorem norm_diagonalRepresentation
    (x : CompactOperatorBoundedProduct H) :
    ‖diagonalRepresentation H x‖ = ‖x‖ := by
  simpa only [map_zero, dist_zero_right] using
    (isometry_diagonalRepresentation H).dist_eq x 0


/-- If a bounded diagonal compact-operator family acts compactly on the
dependent Hilbert sum, then its fibre norms vanish at infinity.  The proof
uses no enumeration of the index type.  Otherwise one obtains infinitely many
unit-ball vectors, each supported in a different coordinate, whose images are
uniformly separated; this contradicts total boundedness of the image of the
unit ball under a compact operator. -/
theorem vanishesAtInfinity_of_isCompactOperator_diagonalRepresentation
    (x : CompactOperatorBoundedProduct H)
    (hx : IsCompactOperator (diagonalRepresentation H x)) :
    C0DirectSum.VanishesAtInfinity (fun i => Fiber H i) x := by
  classical
  intro ε hε
  let S : Set ι := {i | ε ≤ ‖x i‖}
  change S.Finite
  by_contra hS
  have hSinf : S.Infinite := hS
  letI : Infinite S := Set.Infinite.to_subtype hSinf
  have hv_exists (i : S) :
      ∃ v : H i.1, ‖v‖ < 1 ∧
        ε / 2 < ‖((x i.1 : Fiber H i.1) : H i.1 →L[ℂ] H i.1) v‖ := by
    have hhalf : ε / 2 < ‖x i.1‖ := by
      change ε / 2 < ‖x i.1‖
      have hi : ε ≤ ‖x i.1‖ := i.2
      linarith
    exact (((x i.1 : Fiber H i.1) : H i.1 →L[ℂ] H i.1).exists_lt_apply_of_lt_opNorm hhalf)
  choose v hvnorm hvlarge using hv_exists
  let y : S → HilbertSum H := fun i =>
    diagonalRepresentation H x (coordinateEmbedding i.1 (v i))
  obtain ⟨K, hK, himage⟩ := hx.image_closedBall_subset_compact (1 : ℝ)
  have hyK (i : S) : y i ∈ K := by
    apply himage
    refine ⟨coordinateEmbedding i.1 (v i), ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_coordinateEmbedding]
      exact (hvnorm i).le
    · rfl
  obtain ⟨t, _htK, htfinite, hKcover⟩ :=
    Metric.finite_approx_of_totallyBounded hK.totallyBounded
      (ε / 4) (by positivity)
  have hcenter_exists (i : S) :
      ∃ c : HilbertSum H, c ∈ t ∧ dist (y i) c < ε / 4 := by
    have hi := hKcover (hyK i)
    rcases Set.mem_iUnion.mp hi with ⟨c, hi⟩
    rcases Set.mem_iUnion.mp hi with ⟨hc, hic⟩
    exact ⟨c, hc, by simpa only [Metric.mem_ball] using hic⟩
  choose c hc_mem hc_dist using hcenter_exists
  obtain ⟨i, _hi, j, _hj, hij, hcij⟩ :=
    Set.Infinite.exists_ne_map_eq_of_mapsTo
      (f := c) Set.infinite_univ (fun k _ => hc_mem k) htfinite
  have hij_val : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
  have hj_dist : dist (c i) (y j) < ε / 4 := by
    rw [hcij]
    simpa only [dist_comm] using hc_dist j
  have hupper : dist (y i) (y j) < ε / 2 := by
    calc
      dist (y i) (y j) ≤ dist (y i) (c i) + dist (c i) (y j) :=
        dist_triangle _ _ _
      _ < ε / 4 + ε / 4 := add_lt_add (hc_dist i) hj_dist
      _ = ε / 2 := by ring
  have hcoord :
      (y i - y j) i.1 =
        ((x i.1 : Fiber H i.1) : H i.1 →L[ℂ] H i.1) (v i) := by
    simp [y, diagonalRepresentation_coordinateEmbedding,
      coordinateEmbedding_apply, lp.coeFn_single, hij_val, hij_val.symm]
  have hcoord_le :
      ‖((x i.1 : Fiber H i.1) : H i.1 →L[ℂ] H i.1) (v i)‖ ≤
        ‖y i - y j‖ := by
    rw [← hcoord]
    exact lp.norm_apply_le_norm (by norm_num) (y i - y j) i.1
  have hlower : ε / 2 < dist (y i) (y j) := by
    rw [dist_eq_norm]
    exact (hvlarge i).trans_le hcoord_le
  exact (not_lt_of_ge hlower.le) hupper

end CompactOperatorBoundedProduct

namespace CompactOperatorC0Sum

variable {ι : Type uι} (H : ι → Type uH)
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

private abbrev Fiber (i : ι) :=
  ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i)


/-- Inclusion of the actual c₀-sum into the bounded product. -/
def toBoundedProduct :
    CompactOperatorC0Sum H →⋆ₙₐ[ℂ] CompactOperatorBoundedProduct H :=
  NonUnitalStarSubalgebraClass.subtype (C0DirectSum.starSubalgebra (fun i => Fiber H i))

@[simp]
theorem toBoundedProduct_apply (x : CompactOperatorC0Sum H) :
    toBoundedProduct H x = x.1 := rfl


/-- The actual c₀-family representation on the genuine dependent Hilbert
`lp 2` sum. -/
def diagonalRepresentation :
    NonUnitalCStarRepresentation (CompactOperatorC0Sum H) (HilbertSum H) :=
  (CompactOperatorBoundedProduct.diagonalRepresentation H).comp
    (toBoundedProduct H)

@[simp]
theorem diagonalRepresentation_apply
    (x : CompactOperatorC0Sum H) (v : HilbertSum H) (i : ι) :
    diagonalRepresentation H x v i =
      ((C0DirectSum.eval (fun j => Fiber H j) i x : Fiber H i) :
        H i →L[ℂ] H i) (v i) := by
  simp [diagonalRepresentation, toBoundedProduct,
    CompactOperatorBoundedProduct.diagonalRepresentation_apply,
    C0DirectSum.eval_apply]


/-- The c₀ diagonal representation is faithful. -/
theorem diagonalRepresentation_injective :
    Function.Injective (diagonalRepresentation H) := by
  intro x y hxy
  apply Subtype.ext
  apply CompactOperatorBoundedProduct.diagonalRepresentation_injective H
  simpa [diagonalRepresentation, toBoundedProduct] using hxy


/-- The c₀ diagonal representation is isometric. -/
theorem isometry_diagonalRepresentation :
    Isometry (diagonalRepresentation H) :=
  NonUnitalStarAlgHom.isometry (diagonalRepresentation H)
    (diagonalRepresentation_injective H)

@[simp]
theorem norm_diagonalRepresentation (x : CompactOperatorC0Sum H) :
    ‖diagonalRepresentation H x‖ = ‖x‖ := by
  simpa only [map_zero, dist_zero_right] using
    (isometry_diagonalRepresentation H).dist_eq x 0


/-- A one-coordinate c₀-family acts as projection to the coordinate, followed
by the compact fibre operator and the coordinate embedding. -/
theorem diagonalRepresentation_single [DecidableEq ι] (i : ι) (T : Fiber H i) :
    diagonalRepresentation H
        (C0DirectSum.single (fun j => Fiber H j) i T) =
      (coordinateEmbedding i).comp
        (((T : H i →L[ℂ] H i)).comp (coordinateProjection i)) := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext j
  by_cases hji : j = i
  · subst j
    rw [diagonalRepresentation_apply, C0DirectSum.eval_single_same]
    simp [coordinateEmbedding_apply, coordinateProjection_apply, ContinuousLinearMap.comp_apply]
  · rw [diagonalRepresentation_apply, C0DirectSum.eval_single_of_ne _ hji]
    simp [coordinateEmbedding_apply, coordinateProjection_apply,
      ContinuousLinearMap.comp_apply, hji, Ne.symm hji]


/-- Every one-coordinate diagonal operator is compact. -/
theorem isCompactOperator_diagonalRepresentation_single
    (i : ι) (T : Fiber H i) :
    IsCompactOperator (diagonalRepresentation H
      (C0DirectSum.single (fun j => Fiber H j) i T)) := by
  classical
  rw [diagonalRepresentation_single]
  exact (T.property.comp_clm (coordinateProjection i)).clm_comp
    (coordinateEmbedding i)


/-- Every finite coordinate truncation acts by a compact operator. -/
theorem isCompactOperator_diagonalRepresentation_truncate
    (s : Finset ι) (x : CompactOperatorC0Sum H) :
    IsCompactOperator (diagonalRepresentation H
      (C0DirectSum.truncate (fun i => Fiber H i) s x)) := by
  classical
  rw [C0DirectSum.truncate_eq_sum_single]
  simp only [map_sum]
  change (∑ i ∈ s, diagonalRepresentation H
      (C0DirectSum.single (fun j => Fiber H j) i
        (C0DirectSum.eval (fun j => Fiber H j) i x))) ∈
    compactOperator (RingHom.id ℂ) (HilbertSum H) (HilbertSum H)
  exact sum_mem fun i _ =>
    isCompactOperator_diagonalRepresentation_single H i
      (C0DirectSum.eval (fun j => Fiber H j) i x)


set_option backward.isDefEq.respectTransparency false in
/-- Every actual c₀-family acts compactly on the dependent Hilbert sum.  The
proof is finite-coordinate approximation in source norm followed by
contractivity and norm-closedness of compact operators. -/
theorem isCompactOperator_diagonalRepresentation
    (x : CompactOperatorC0Sum H) :
    IsCompactOperator (diagonalRepresentation H x) := by
  change diagonalRepresentation H x ∈
    {T : HilbertSum H →L[ℂ] HilbertSum H | IsCompactOperator T}
  have hclosed : IsClosed
      {T : HilbertSum H →L[ℂ] HilbertSum H | IsCompactOperator T} :=
    isClosed_setOf_isCompactOperator
  rw [← hclosed.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨s, hs⟩ := C0DirectSum.exists_finset_norm_sub_truncate_lt
    (fun i => Fiber H i) x hε
  refine ⟨diagonalRepresentation H
      (C0DirectSum.truncate (fun i => Fiber H i) s x),
    isCompactOperator_diagonalRepresentation_truncate H s x, ?_⟩
  rw [(isometry_diagonalRepresentation H).dist_eq]
  simpa only [dist_eq_norm, norm_sub_rev] using hs


/-- The literal operator range of the c₀ diagonal representation consists of
compact operators. -/
theorem diagonalRepresentation_range_le_compactOperatorStarSubalgebra :
    (NonUnitalStarAlgHom.range (diagonalRepresentation H)) ≤
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (HilbertSum H) := by
  intro T hT
  obtain ⟨x, hx⟩ := (NonUnitalStarAlgHom.mem_range
    (diagonalRepresentation H)).1 hT
  rw [← hx]
  exact isCompactOperator_diagonalRepresentation H x


/-- The c₀ diagonal representation with codomain restricted to the concrete
compact-operator C-star algebra on the Hilbert sum. -/
def compactDiagonalRepresentation :
    CompactOperatorC0Sum H →⋆ₙₐ[ℂ]
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (HilbertSum H) :=
  NonUnitalStarAlgHom.codRestrict (diagonalRepresentation H)
    (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (HilbertSum H))
      (isCompactOperator_diagonalRepresentation H)

@[simp]
theorem compactDiagonalRepresentation_apply_coe
    (x : CompactOperatorC0Sum H) :
    ((compactDiagonalRepresentation H x :
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (HilbertSum H)) :
        HilbertSum H →L[ℂ] HilbertSum H) =
      diagonalRepresentation H x := rfl


set_option backward.isDefEq.respectTransparency false in
/-- Restriction to the literal operator range is onto by construction. -/
theorem diagonalRepresentation_rangeRestrict_surjective :
    Function.Surjective (NonUnitalStarAlgHom.rangeRestrict (diagonalRepresentation H)) := by
  exact rangeRestrictionOnto (diagonalRepresentation H)


/-- Restriction to the literal operator range is bijective because the
representation is faithful. -/
theorem diagonalRepresentation_rangeRestrict_bijective :
    Function.Bijective (NonUnitalStarAlgHom.rangeRestrict (diagonalRepresentation H)) := by
  constructor
  · intro x y hxy
    apply diagonalRepresentation_injective H
    exact congrArg Subtype.val hxy
  · exact diagonalRepresentation_rangeRestrict_surjective H


set_option backward.isDefEq.respectTransparency false in
/-- Actual nonunital C-star equivalence from the c₀-family algebra to its
literal Hilbert-operator range. -/
def diagonalEquivRange :
    CompactOperatorC0Sum H ≃⋆ₐ[ℂ] (NonUnitalStarAlgHom.range (diagonalRepresentation H)) :=
  { Equiv.ofBijective (NonUnitalStarAlgHom.rangeRestrict (diagonalRepresentation H))
      (diagonalRepresentation_rangeRestrict_bijective H) with
    map_add' := map_add (NonUnitalStarAlgHom.rangeRestrict (diagonalRepresentation H))
    map_mul' := map_mul (NonUnitalStarAlgHom.rangeRestrict (diagonalRepresentation H))
    map_smul' := map_smul (NonUnitalStarAlgHom.rangeRestrict (diagonalRepresentation H))
    map_star' := map_star (NonUnitalStarAlgHom.rangeRestrict (diagonalRepresentation H)) }


set_option backward.isDefEq.respectTransparency false in
theorem diagonalEquivRange_apply_coe (x : CompactOperatorC0Sum H) :
    ((diagonalEquivRange H x : (NonUnitalStarAlgHom.range (diagonalRepresentation H))) :
      HilbertSum H →L[ℂ] HilbertSum H) = diagonalRepresentation H x := by
  exact equivalenceFromBijective_val
    (NonUnitalStarAlgHom.rangeRestrict (diagonalRepresentation H))
    (diagonalRepresentation_rangeRestrict_bijective H) x


set_option backward.whnf.reducibleClassField false in
attribute [simp] diagonalEquivRange_apply_coe


end CompactOperatorC0Sum

namespace CompactOperatorBoundedProduct

variable {ι : Type uι} (H : ι → Type uH)
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]


/-- A bounded compact-operator family acts compactly on the dependent Hilbert
sum exactly when its fibre norms form a c₀-family. -/
theorem isCompactOperator_diagonalRepresentation_iff
    (x : CompactOperatorBoundedProduct H) :
    IsCompactOperator (diagonalRepresentation H x) ↔
      C0DirectSum.VanishesAtInfinity
        (fun i => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i)) x := by
  constructor
  · exact vanishesAtInfinity_of_isCompactOperator_diagonalRepresentation H x
  · intro hx
    simpa only [CompactOperatorC0Sum.diagonalRepresentation,
      NonUnitalStarAlgHom.comp_apply, CompactOperatorC0Sum.toBoundedProduct_apply] using
      (CompactOperatorC0Sum.isCompactOperator_diagonalRepresentation H
        (⟨x, hx⟩ : CompactOperatorC0Sum H))


set_option backward.whnf.reducibleClassField false in
/-- Inside the bounded block-diagonal range, the compact operators are
precisely the c₀ block-diagonal range.  This is an equality of literal
nonunital star subalgebras of operators; it does not identify the c₀ range
with the full compact-operator algebra. -/
theorem diagonalRepresentation_range_inf_compactOperatorStarSubalgebra :
    (NonUnitalStarAlgHom.range (diagonalRepresentation H)) ⊓
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (HilbertSum H) =
      (NonUnitalStarAlgHom.range (CompactOperatorC0Sum.diagonalRepresentation H)) := by
  ext T
  constructor
  · intro hT
    obtain ⟨x, hx⟩ := (NonUnitalStarAlgHom.mem_range
      (diagonalRepresentation H)).1 hT.1
    have hxcompact : IsCompactOperator (diagonalRepresentation H x) := by
      rw [hx]
      exact hT.2
    have hxc0 :=
      vanishesAtInfinity_of_isCompactOperator_diagonalRepresentation H x hxcompact
    apply (NonUnitalStarAlgHom.mem_range
      (CompactOperatorC0Sum.diagonalRepresentation H)).2
    refine ⟨(⟨x, hxc0⟩ : CompactOperatorC0Sum H), ?_⟩
    simpa only [CompactOperatorC0Sum.diagonalRepresentation,
      NonUnitalStarAlgHom.comp_apply, CompactOperatorC0Sum.toBoundedProduct_apply] using hx
  · intro hT
    constructor
    · obtain ⟨x, hx⟩ := (NonUnitalStarAlgHom.mem_range
        (CompactOperatorC0Sum.diagonalRepresentation H)).1 hT
      exact (NonUnitalStarAlgHom.mem_range (diagonalRepresentation H)).2
        ⟨x.1, by
          simpa only [CompactOperatorC0Sum.diagonalRepresentation,
            NonUnitalStarAlgHom.comp_apply, CompactOperatorC0Sum.toBoundedProduct_apply] using hx⟩
    · exact CompactOperatorC0Sum.diagonalRepresentation_range_le_compactOperatorStarSubalgebra H hT

end CompactOperatorBoundedProduct

end MathlibAnnex.Analysis.CStarAlgebra
