/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartProjectiveMap
import Mathlib.LinearAlgebra.Projectivization.Subspace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Relative closures of finite coordinate fibers

These are equalities for the whole relative closure in the existing normal
part. They are not consequences of the classification of `Linked` alone.
Finite kernel factorization produces an actual coefficient equality. The
existing WOT relation theorem moves this equality to all bounded operators
before rank-one tests recover the two vector lines. Fixed-target sums are
linear and fixed-source sums are conjugate-linear in the varying vector.
All finite index types, including the empty type, are allowed. No assumption
of finite dimension or separability of the Hilbert space is used.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators LinearAlgebra.Projectivization

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable [IsClosed (S : Set (H →L[ℂ] H))]
variable (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))

/-- A local bridge to the existing projective span, not a new span definition.
The proof uses the fixed order correspondence; it does not close vector spans. -/
private theorem mem_projective_span_range_iff {ι : Type*}
    (p : ι → ℙ ℂ H) (q : ℙ ℂ H) :
    q ∈ Projectivization.Subspace.span (Set.range p) ↔
      q.rep ∈ Submodule.span ℂ (Set.range fun i => (p i).rep) := by
  let W := Projectivization.Subspace.span (Set.range p)
  let Y := Submodule.span ℂ (Set.range fun i => (p i).rep)
  have hWY : W ≤ Y.projectivization := by
    apply Projectivization.Subspace.span_le_subspace_iff.mpr
    rintro _ ⟨i, rfl⟩
    rw [← (p i).mk_rep]
    exact (Submodule.mk_mem_projectivization_iff Y (p i).rep_nonzero).2
      (Submodule.subset_span (Set.mem_range_self i))
  have hYW : Y ≤ Projectivization.Subspace.submodule W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply (Projectivization.Subspace.mem_submodule_iff W (p i).rep_nonzero).2
    rw [Projectivization.mk_rep]
    change p i ∈ (Projectivization.Subspace.span (Set.range p) : Set (ℙ ℂ H))
    exact Projectivization.Subspace.subset_span (Set.range p) (Set.mem_range_self i)
  constructor
  · intro hq
    exact (Submodule.mk_mem_projectivization_iff Y q.rep_nonzero).mp
      (by simpa only [Projectivization.mk_rep] using hWY hq)
  · intro hq
    simpa only [Projectivization.mk_rep] using
      (Projectivization.Subspace.mem_submodule_iff W q.rep_nonzero).mp (hYW hq)

/-- Fixed source: the varying target belongs to the actual finite vector span.
The four nonzero conditions concern actual normal-point representatives only. -/
theorem mem_closure_range_normalPartPoint_fixed_source_iff
    {ι : Type*} [Fintype ι] (x : H) (y : ι → H) (z w : H)
    (hx : x ≠ 0) (hy : ∀ i, y i ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0) :
    normalPartPoint S hS z w hz hw ∈
        ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure
          (Set.range fun i => normalPartPoint S hS x (y i) hx (hy i)) ↔
      Submodule.span ℂ {z} = Submodule.span ℂ {x} ∧
        w ∈ Submodule.span ℂ (Set.range y) := by
  classical
  let pi := NonUnitalStarSubalgebraClass.subtype S
  constructor
  · intro h
    have hzero : ∀ a : S,
        (∀ i, NonUnitalCStarRepresentation.matrixCoefficient pi x (y i) a = 0) →
          NonUnitalCStarRepresentation.matrixCoefficient pi z w a = 0 := by
      intro a ha
      apply (mem_normalPart_closure_iff S _ _).mp h a
      rintro _ ⟨i, rfl⟩
      exact ha i
    obtain ⟨c, hc⟩ := (LinearMap.forall_eq_zero_imp_iff_exists_sum_smul
      (fun i => (NonUnitalCStarRepresentation.matrixCoefficient pi x (y i)).toLinearMap)
      (NonUnitalCStarRepresentation.matrixCoefficient pi z w).toLinearMap).mp hzero
    have hc' : NonUnitalCStarRepresentation.matrixCoefficient pi z w =
        ∑ i, c i • NonUnitalCStarRepresentation.matrixCoefficient pi x (y i) := by
      ext a
      simpa using LinearMap.congr_fun hc a
    let v : H := ∑ i, star (c i) • y i
    have hsum : (∑ i, c i • NonUnitalCStarRepresentation.matrixCoefficient pi x (y i)) =
        NonUnitalCStarRepresentation.matrixCoefficient pi x v := by
      ext a
      simp [v, NonUnitalCStarRepresentation.matrixCoefficient_apply,
        sum_inner, inner_smul_left]
    have heq := hc'.trans hsum
    have hv : v ≠ 0 := by
      intro hv
      have hh0 := (NonUnitalCStarRepresentation.matrixCoefficient_ne_zero_iff
        pi hS z w).2 ⟨hz, hw⟩
      apply hh0
      simpa only [hv, NonUnitalCStarRepresentation.matrixCoefficient_zero_right] using heq
    have hop := (NonUnitalCStarRepresentation.matrixCoefficient_eq_smul_iff_operator
      pi hS x v z w 1).mp (by simpa only [one_smul] using heq)
    have hlines := InnerProductSpace.span_eq_and_span_eq_of_matrixCoefficient_eq_smul
      hx hv hz hw hop
    have hvspan : v ∈ Submodule.span ℂ (Set.range y) :=
      Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self i)))
    have hvle : Submodule.span ℂ {v} ≤ Submodule.span ℂ (Set.range y) := by
      apply Submodule.span_le.mpr
      rintro _ rfl
      exact hvspan
    have hwv : w ∈ Submodule.span ℂ {v} := by
      rw [hlines.2]
      exact Submodule.subset_span (by simp)
    exact ⟨hlines.1.symm, hvle hwv⟩
  · rintro ⟨hzx, hwy⟩
    have hzx' : z ∈ Submodule.span ℂ {x} := by
      rw [← hzx]
      exact Submodule.subset_span (by simp)
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hzx'
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hwy
    apply (mem_normalPart_closure_iff S _ _).mpr
    intro a ha
    have hval (i : ι) : inner ℂ (y i) ((a : H →L[ℂ] H) x) = 0 :=
      ha _ (Set.mem_range_self i)
    change inner ℂ w ((a : H →L[ℂ] H) z) = 0
    rw [← ht, ← hc, map_smul, inner_smul_right, sum_inner]
    simp only [inner_smul_left, hval, mul_zero, Finset.sum_const_zero]

/-- Fixed target: the varying source is linear, so no conjugation is inserted
in the vector sum. Empty, repeated, and dependent finite families are included. -/
theorem mem_closure_range_normalPartPoint_fixed_target_iff
    {ι : Type*} [Fintype ι] (x : ι → H) (y : H) (z w : H)
    (hx : ∀ i, x i ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0) :
    normalPartPoint S hS z w hz hw ∈
        ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure
          (Set.range fun i => normalPartPoint S hS (x i) y (hx i) hy) ↔
      z ∈ Submodule.span ℂ (Set.range x) ∧
        Submodule.span ℂ {w} = Submodule.span ℂ {y} := by
  classical
  let pi := NonUnitalStarSubalgebraClass.subtype S
  constructor
  · intro h
    have hzero : ∀ a : S,
        (∀ i, NonUnitalCStarRepresentation.matrixCoefficient pi (x i) y a = 0) →
          NonUnitalCStarRepresentation.matrixCoefficient pi z w a = 0 := by
      intro a ha
      apply (mem_normalPart_closure_iff S _ _).mp h a
      rintro _ ⟨i, rfl⟩
      exact ha i
    obtain ⟨c, hc⟩ := (LinearMap.forall_eq_zero_imp_iff_exists_sum_smul
      (fun i => (NonUnitalCStarRepresentation.matrixCoefficient pi (x i) y).toLinearMap)
      (NonUnitalCStarRepresentation.matrixCoefficient pi z w).toLinearMap).mp hzero
    have hc' : NonUnitalCStarRepresentation.matrixCoefficient pi z w =
        ∑ i, c i • NonUnitalCStarRepresentation.matrixCoefficient pi (x i) y := by
      ext a
      simpa using LinearMap.congr_fun hc a
    let v : H := ∑ i, c i • x i
    have hsum : (∑ i, c i • NonUnitalCStarRepresentation.matrixCoefficient pi (x i) y) =
        NonUnitalCStarRepresentation.matrixCoefficient pi v y := by
      ext a
      simp [v, NonUnitalCStarRepresentation.matrixCoefficient_apply,
        inner_sum, inner_smul_right]
    have heq := hc'.trans hsum
    have hv : v ≠ 0 := by
      intro hv
      have hh0 := (NonUnitalCStarRepresentation.matrixCoefficient_ne_zero_iff
        pi hS z w).2 ⟨hz, hw⟩
      apply hh0
      simpa only [hv, NonUnitalCStarRepresentation.matrixCoefficient_zero_left] using heq
    have hop := (NonUnitalCStarRepresentation.matrixCoefficient_eq_smul_iff_operator
      pi hS v y z w 1).mp (by simpa only [one_smul] using heq)
    have hlines := InnerProductSpace.span_eq_and_span_eq_of_matrixCoefficient_eq_smul
      hv hy hz hw hop
    have hvspan : v ∈ Submodule.span ℂ (Set.range x) :=
      Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self i)))
    have hvle : Submodule.span ℂ {v} ≤ Submodule.span ℂ (Set.range x) := by
      apply Submodule.span_le.mpr
      rintro _ rfl
      exact hvspan
    have hzv : z ∈ Submodule.span ℂ {v} := by
      rw [hlines.1]
      exact Submodule.subset_span (by simp)
    exact ⟨hvle hzv, hlines.2.symm⟩
  · rintro ⟨hzx, hwy⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hzx
    have hwy' : w ∈ Submodule.span ℂ {y} := by
      rw [← hwy]
      exact Submodule.subset_span (by simp)
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hwy'
    apply (mem_normalPart_closure_iff S _ _).mpr
    intro a ha
    have hval (i : ι) : inner ℂ y ((a : H →L[ℂ] H) (x i)) = 0 :=
      ha _ (Set.mem_range_self i)
    change inner ℂ w ((a : H →L[ℂ] H) z) = 0
    rw [← ht, ← hc, inner_smul_left, map_sum, inner_sum]
    simp only [map_smul, inner_smul_right, hval, mul_zero, Finset.sum_const_zero]

/-- Every point of a fixed-source finite closure has the original source line
and a target in the actual Mathlib projective span. -/
theorem mem_closure_range_normalPartProjectivizationEquiv_fixed_source_iff
    {ι : Type*} [Fintype ι] (p : ℙ ℂ H) (q : ι → ℙ ℂ H)
    (r : (ℙ ℂ H) × (ℙ ℂ H)) :
    normalPartProjectivizationEquiv S hS r ∈
        ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure
          (Set.range fun i => normalPartProjectivizationEquiv S hS (p, q i)) ↔
      r.1 = p ∧ r.2 ∈ Projectivization.Subspace.span (Set.range q) := by
  change normalPartPoint S hS r.1.rep r.2.rep r.1.rep_nonzero r.2.rep_nonzero ∈
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure
      (Set.range fun i => normalPartPoint S hS p.rep (q i).rep
        p.rep_nonzero (q i).rep_nonzero) ↔ _
  rw [mem_closure_range_normalPartPoint_fixed_source_iff,
    mem_projective_span_range_iff]
  refine and_congr ?_ Iff.rfl
  constructor
  · intro h
    apply Projectivization.submodule_injective
    simpa only [Projectivization.submodule_eq] using h
  · rintro rfl
    rfl

/-- The symmetric formula keeps the varying source in the first factor. -/
theorem mem_closure_range_normalPartProjectivizationEquiv_fixed_target_iff
    {ι : Type*} [Fintype ι] (p : ι → ℙ ℂ H) (q : ℙ ℂ H)
    (r : (ℙ ℂ H) × (ℙ ℂ H)) :
    normalPartProjectivizationEquiv S hS r ∈
        ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure
          (Set.range fun i => normalPartProjectivizationEquiv S hS (p i, q)) ↔
      r.1 ∈ Projectivization.Subspace.span (Set.range p) ∧ r.2 = q := by
  change normalPartPoint S hS r.1.rep r.2.rep r.1.rep_nonzero r.2.rep_nonzero ∈
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure
      (Set.range fun i => normalPartPoint S hS (p i).rep q.rep
        (p i).rep_nonzero q.rep_nonzero) ↔ _
  rw [mem_closure_range_normalPartPoint_fixed_target_iff,
    mem_projective_span_range_iff]
  refine and_congr Iff.rfl ?_
  constructor
  · intro h
    apply Projectivization.submodule_injective
    simpa only [Projectivization.submodule_eq] using h
  · rintro rfl
    rfl

/-- Equality of the whole relative closure, including all new projective points. -/
theorem closure_range_normalPartProjectivizationEquiv_fixed_source
    {ι : Type*} [Fintype ι] (p : ℙ ℂ H) (q : ι → ℙ ℂ H) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure
        (Set.range fun i => normalPartProjectivizationEquiv S hS (p, q i)) =
      (fun r => normalPartProjectivizationEquiv S hS (p, r)) ''
        (Projectivization.Subspace.span (Set.range q) : Set (ℙ ℂ H)) := by
  ext I
  obtain ⟨r, rfl⟩ := (normalPartProjectivizationEquiv S hS).surjective I
  rw [mem_closure_range_normalPartProjectivizationEquiv_fixed_source_iff]
  constructor
  · rintro ⟨h, hr⟩
    exact ⟨r.2, hr, congrArg (normalPartProjectivizationEquiv S hS) (Prod.ext h.symm rfl)⟩
  · rintro ⟨z, hz, heq⟩
    have heq' := (normalPartProjectivizationEquiv S hS).injective heq
    exact ⟨(congrArg Prod.fst heq').symm, congrArg Prod.snd heq' ▸ hz⟩

/-- The fixed-target finite closure is the whole corresponding projective span. -/
theorem closure_range_normalPartProjectivizationEquiv_fixed_target
    {ι : Type*} [Fintype ι] (p : ι → ℙ ℂ H) (q : ℙ ℂ H) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure
        (Set.range fun i => normalPartProjectivizationEquiv S hS (p i, q)) =
      (fun r => normalPartProjectivizationEquiv S hS (r, q)) ''
        (Projectivization.Subspace.span (Set.range p) : Set (ℙ ℂ H)) := by
  ext I
  obtain ⟨r, rfl⟩ := (normalPartProjectivizationEquiv S hS).surjective I
  rw [mem_closure_range_normalPartProjectivizationEquiv_fixed_target_iff]
  constructor
  · rintro ⟨hr, h⟩
    exact ⟨r.1, hr, congrArg (normalPartProjectivizationEquiv S hS) (Prod.ext rfl h.symm)⟩
  · rintro ⟨z, hz, heq⟩
    have heq' := (normalPartProjectivizationEquiv S hS).injective heq
    exact ⟨congrArg Prod.fst heq' ▸ hz, (congrArg Prod.snd heq').symm⟩

/-- The set formulation; duplicate representatives never become extra points. -/
theorem closure_image_normalPartProjectivizationEquiv_fixed_source_of_finite
    (p : ℙ ℂ H) (s : Set (ℙ ℂ H)) (hs : s.Finite) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure
        ((fun q => normalPartProjectivizationEquiv S hS (p, q)) '' s) =
      (fun q => normalPartProjectivizationEquiv S hS (p, q)) ''
        (Projectivization.Subspace.span s : Set (ℙ ℂ H)) := by
  letI : Fintype s := hs.fintype
  have hr : Set.range (fun q : s => q.val) = s := by ext q; simp
  have hi : Set.range (fun q : s => normalPartProjectivizationEquiv S hS (p, q.val)) =
      (fun q => normalPartProjectivizationEquiv S hS (p, q)) '' s := by
    ext I
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q.val, q.property, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
  simpa only [hr, hi] using
    closure_range_normalPartProjectivizationEquiv_fixed_source S hS p (fun q : s => q.val)

/-- The finite set formula in the other coordinate. -/
theorem closure_image_normalPartProjectivizationEquiv_fixed_target_of_finite
    (s : Set (ℙ ℂ H)) (hs : s.Finite) (q : ℙ ℂ H) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure
        ((fun p => normalPartProjectivizationEquiv S hS (p, q)) '' s) =
      (fun p => normalPartProjectivizationEquiv S hS (p, q)) ''
        (Projectivization.Subspace.span s : Set (ℙ ℂ H)) := by
  letI : Fintype s := hs.fintype
  have hr : Set.range (fun p : s => p.val) = s := by ext p; simp
  have hi : Set.range (fun p : s => normalPartProjectivizationEquiv S hS (p.val, q)) =
      (fun p => normalPartProjectivizationEquiv S hS (p, q)) '' s := by
    ext I
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.val, p.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  simpa only [hr, hi] using
    closure_range_normalPartProjectivizationEquiv_fixed_target S hS (fun p : s => p.val) q

include hS

/-- The empty-family boundary is compatible with the actual bottom projective span. -/
theorem closure_empty_normalPart :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure ∅ = ∅ := by
  letI : Nontrivial H := NonUnitalCStarRepresentation.nontrivial_of_isNonzero
    (NonUnitalStarSubalgebraClass.subtype S) hS.1
  let p : ℙ ℂ H := Classical.choice inferInstance
  simpa only [Set.image_empty, Projectivization.Subspace.span_empty,
    Projectivization.Subspace.bot_coe] using
    closure_image_normalPartProjectivizationEquiv_fixed_source_of_finite S hS
      p ∅ Set.finite_empty

end MathlibAnnex.Analysis.CStarAlgebra
