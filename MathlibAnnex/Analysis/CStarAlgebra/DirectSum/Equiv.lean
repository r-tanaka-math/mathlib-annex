/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.C0DirectSum
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.LinearAlgebra.Pi

/-!
# Equivalences of dependent c₀-direct sums

An equivalence of index types together with fibrewise nonunital complex C-star
algebra equivalences induces an actual star-algebra equivalence of the dependent
c₀-direct sums.  The construction acts on the genuine `C0DirectSum`, not on the
unrestricted bounded product or on the algebraic direct sum.

The proof records the coordinate formulas, preservation and reflection of
vanishing at infinity, single-coordinate and finite-truncation formulas, norm
preservation, coordinate-kernel transport, and finite-support density.  No
countability, separability, or finiteness hypothesis is imposed on the index
sets or fibres.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped BigOperators CStarAlgebra ENNReal

namespace MathlibAnnex.Analysis.CStarAlgebra.C0DirectSum

universe uι uκ uA uB

variable {ι : Type uι} {κ : Type uκ}
variable (A : ι → Type uA) (B : κ → Type uB)
variable [∀ i, NonUnitalCStarAlgebra (A i)]
variable [∀ j, NonUnitalCStarAlgebra (B j)]
variable (e : ι ≃ κ) (E : ∀ i, A i ≃⋆ₐ[ℂ] B (e i))

/-- Reindex a dependent family whose `i`-th target fibre is `B (e i)`.
This is the exact dependent-function equivalence, not a choice of casts. -/
def reindexFamilyEquiv : (∀ i, B (e i)) ≃ (∀ j, B j) :=
  (Equiv.piCongrLeft' B e.symm).symm

@[simp]
theorem reindexFamilyEquiv_apply (x : ∀ i, B (e i)) (i : ι) :
    reindexFamilyEquiv B e x (e i) = x i := by
  change (Equiv.piCongrLeft B e) x (e i) = x i
  exact Equiv.piCongrLeft_apply_apply B e x i

@[simp]
theorem reindexFamilyEquiv_symm_apply (x : ∀ j, B j) (i : ι) :
    (reindexFamilyEquiv B e).symm x i = x (e i) := by
  change (Equiv.piCongrLeft B e).symm x i = x (e i)
  exact Equiv.piCongrLeft_symm_apply B e x i

/-- Fibre equivalences preserve the original C-star norms. -/
theorem norm_fiber_equiv_apply (i : ι) (a : A i) : ‖E i a‖ = ‖a‖ := by
  simpa only [StarAlgEquiv.toNonUnitalStarAlgHom_apply, map_zero, dist_zero_right] using
    (NonUnitalStarAlgHom.isometry (E i).toNonUnitalStarAlgHom (E i).injective).dist_eq a 0

/-- The inverse fibre equivalences preserve the original C-star norms. -/
theorem norm_fiber_equiv_symm_apply (i : ι) (b : B (e i)) :
    ‖(E i).symm b‖ = ‖b‖ := by
  simpa only [StarAlgEquiv.toNonUnitalStarAlgHom_apply, map_zero, dist_zero_right] using
    (NonUnitalStarAlgHom.isometry (E i).symm.toNonUnitalStarAlgHom
      (E i).symm.injective).dist_eq b 0

/-- Apply the fibre equivalences and reindex an actual bounded dependent
family. -/
def mapLp (x : lp A ∞) : lp B ∞ := by
  refine ⟨reindexFamilyEquiv B e (fun i => E i (x i)), memℓp_infty ?_⟩
  obtain ⟨C, hC⟩ := memℓp_infty_iff.mp x.2
  refine ⟨C, ?_⟩
  rintro r ⟨j, rfl⟩
  obtain ⟨i, rfl⟩ := e.surjective j
  change ‖reindexFamilyEquiv B e (fun i => E i (x i)) (e i)‖ ≤ C
  rw [reindexFamilyEquiv_apply, norm_fiber_equiv_apply]
  exact hC ⟨i, rfl⟩

/-- Apply the inverse fibre equivalences to an actual bounded dependent
family. -/
def unmapLp (y : lp B ∞) : lp A ∞ := by
  refine ⟨fun i => (E i).symm (y (e i)), memℓp_infty ?_⟩
  obtain ⟨C, hC⟩ := memℓp_infty_iff.mp y.2
  refine ⟨C, ?_⟩
  rintro r ⟨i, rfl⟩
  change ‖(E i).symm (y (e i))‖ ≤ C
  rw [norm_fiber_equiv_symm_apply]
  exact hC ⟨e i, rfl⟩

@[simp]
theorem mapLp_apply (x : lp A ∞) (i : ι) :
    mapLp A B e E x (e i) = E i (x i) := by
  simp [mapLp]

@[simp]
theorem unmapLp_apply (y : lp B ∞) (i : ι) :
    unmapLp A B e E y i = (E i).symm (y (e i)) := rfl

@[simp]
theorem unmapLp_mapLp (x : lp A ∞) :
    unmapLp A B e E (mapLp A B e E x) = x := by
  ext i
  simp

@[simp]
theorem mapLp_unmapLp (y : lp B ∞) :
    mapLp A B e E (unmapLp A B e E y) = y := by
  ext j
  obtain ⟨i, rfl⟩ := e.surjective j
  simp

/-- The superlevel set of the transported family is exactly the image of the
original superlevel set under the index equivalence. -/
theorem superlevel_mapLp (x : lp A ∞) (ε : ℝ) :
    {j : κ | ε ≤ ‖mapLp A B e E x j‖} =
      e '' {i : ι | ε ≤ ‖x i‖} := by
  ext j
  constructor
  · intro hj
    obtain ⟨i, rfl⟩ := e.surjective j
    refine ⟨i, ?_, rfl⟩
    simpa only [Set.mem_setOf_eq, mapLp_apply, norm_fiber_equiv_apply] using hj
  · rintro ⟨i, hi, rfl⟩
    simpa only [Set.mem_setOf_eq, mapLp_apply, norm_fiber_equiv_apply] using hi

/-- Vanishing at infinity is preserved and reflected by the actual bounded
family transport. -/
theorem vanishesAtInfinity_mapLp_iff (x : lp A ∞) :
    VanishesAtInfinity B (mapLp A B e E x) ↔ VanishesAtInfinity A x := by
  constructor
  · intro hx ε hε
    have hfinite := (hx ε hε).image e.symm
    refine hfinite.subset ?_
    intro i hi
    refine ⟨e i, ?_, e.symm_apply_apply i⟩
    simpa only [Set.mem_setOf_eq, mapLp_apply, norm_fiber_equiv_apply] using hi
  · intro hx ε hε
    rw [superlevel_mapLp]
    exact (hx ε hε).image e

/-- The actual nonunital star-algebra equivalence of dependent c₀-direct sums. -/
def equiv : C0DirectSum A ≃⋆ₐ[ℂ] C0DirectSum B where
  toFun x := ⟨mapLp A B e E x.1, (vanishesAtInfinity_mapLp_iff A B e E x.1).2 x.2⟩
  invFun y := ⟨unmapLp A B e E y.1, by
    apply (vanishesAtInfinity_mapLp_iff A B e E (unmapLp A B e E y.1)).1
    have hy : VanishesAtInfinity B y.1 := y.2
    simpa only [mapLp_unmapLp] using hy⟩
  left_inv x := by
    apply Subtype.ext
    exact unmapLp_mapLp A B e E x.1
  right_inv y := by
    apply Subtype.ext
    exact mapLp_unmapLp A B e E y.1
  map_add' x y := by
    apply Subtype.ext
    ext i
    obtain ⟨j, rfl⟩ := e.surjective i
    simp [mapLp_apply]
  map_mul' x y := by
    apply Subtype.ext
    ext i
    obtain ⟨j, rfl⟩ := e.surjective i
    simp [mapLp_apply]
  map_smul' c x := by
    apply Subtype.ext
    ext i
    obtain ⟨j, rfl⟩ := e.surjective i
    simp [mapLp_apply]
  map_star' x := by
    apply Subtype.ext
    ext i
    obtain ⟨j, rfl⟩ := e.surjective i
    change mapLp A B e E (star x.1) (e j) = star (mapLp A B e E x.1 (e j))
    rw [mapLp_apply, mapLp_apply]
    change E j (star (x.1 j)) = star (E j (x.1 j))
    exact map_star (E j) _

@[simp]
theorem equiv_coe (x : C0DirectSum A) :
    (equiv A B e E x).1 = mapLp A B e E x.1 := rfl

@[simp]
theorem equiv_symm_coe (y : C0DirectSum B) :
    ((equiv A B e E).symm y).1 = unmapLp A B e E y.1 := rfl

/-- Forward coordinate formula. -/
@[simp]
theorem eval_equiv_apply (x : C0DirectSum A) (i : ι) :
    eval B (e i) (equiv A B e E x) = E i (eval A i x) := by
  change mapLp A B e E x.1 (e i) = E i (x.1 i)
  exact mapLp_apply A B e E x.1 i

/-- Inverse coordinate formula. -/
@[simp]
theorem eval_equiv_symm_apply (y : C0DirectSum B) (i : ι) :
    eval A i ((equiv A B e E).symm y) = (E i).symm (eval B (e i) y) := by
  rfl

/-- The direct-sum equivalence is an isometry for the inherited supremum norms. -/
@[simp]
theorem norm_equiv_apply (x : C0DirectSum A) :
    ‖equiv A B e E x‖ = ‖x‖ := by
  simpa only [StarAlgEquiv.toNonUnitalStarAlgHom_apply, map_zero, dist_zero_right] using
    (NonUnitalStarAlgHom.isometry (equiv A B e E).toNonUnitalStarAlgHom
      (equiv A B e E).injective).dist_eq x 0

@[simp]
theorem norm_equiv_symm_apply (y : C0DirectSum B) :
    ‖(equiv A B e E).symm y‖ = ‖y‖ := by
  simpa only [StarAlgEquiv.toNonUnitalStarAlgHom_apply, map_zero, dist_zero_right] using
    (NonUnitalStarAlgHom.isometry (equiv A B e E).symm.toNonUnitalStarAlgHom
      (equiv A B e E).symm.injective).dist_eq y 0

/-- Single-coordinate families are transported to the corresponding reindexed
single-coordinate families. -/
@[simp]
theorem equiv_single (i : ι) (a : A i) :
    equiv A B e E (single A i a) = single B (e i) (E i a) := by
  apply Subtype.ext
  ext j
  obtain ⟨k, rfl⟩ := e.surjective j
  change eval B (e k) (equiv A B e E (single A i a)) =
    eval B (e k) (single B (e i) (E i a))
  rw [eval_equiv_apply]
  by_cases hki : k = i
  · subst k
    rw [eval_single_same, eval_single_same]
  · have hei : e k ≠ e i := fun h => hki (e.injective h)
    rw [eval_single_of_ne A hki, eval_single_of_ne B hei]
    simp

/-- Finite coordinate truncation commutes with the direct-sum equivalence. -/
@[simp]
theorem equiv_truncate (s : Finset ι) (x : C0DirectSum A) :
    equiv A B e E (truncate A s x) =
      truncate B (s.map e.toEmbedding) (equiv A B e E x) := by
  classical
  apply Subtype.ext
  ext j
  obtain ⟨i, rfl⟩ := e.surjective j
  change eval B (e i) (equiv A B e E (truncate A s x)) =
    eval B (e i) (truncate B (s.map e.toEmbedding) (equiv A B e E x))
  rw [eval_equiv_apply, eval_truncate, eval_truncate]
  by_cases hi : i ∈ s <;> simp [hi]

/-- Coordinate kernels are carried to the corresponding reindexed coordinate
kernels. -/
theorem eval_equiv_eq_zero_iff (x : C0DirectSum A) (i : ι) :
    eval B (e i) (equiv A B e E x) = 0 ↔ eval A i x = 0 := by
  rw [eval_equiv_apply]
  constructor
  · intro h
    have hinv := congrArg (E i).symm h
    simpa only [StarAlgEquiv.symm_apply_apply, map_zero] using hinv
  · intro h
    simpa only [h, map_zero]

/-- Exact image formula for the coordinate support of a transported family. -/
theorem support_equiv (x : C0DirectSum A) :
    {j : κ | eval B j (equiv A B e E x) ≠ 0} =
      e '' {i : ι | eval A i x ≠ 0} := by
  ext j
  constructor
  · intro hj
    obtain ⟨i, rfl⟩ := e.surjective j
    refine ⟨i, ?_, rfl⟩
    simpa only [Set.mem_setOf_eq, eval_equiv_eq_zero_iff, ne_eq]
      using hj
  · rintro ⟨i, hi, rfl⟩
    simpa only [Set.mem_setOf_eq, eval_equiv_eq_zero_iff, ne_eq]
      using hi

/-- Finite coordinate support is preserved and reflected. -/
theorem finite_support_equiv_iff (x : C0DirectSum A) :
    Set.Finite {j : κ | eval B j (equiv A B e E x) ≠ 0} ↔
      Set.Finite {i : ι | eval A i x ≠ 0} := by
  constructor
  · intro hfinite
    have himage := hfinite.image e.symm
    refine himage.subset ?_
    intro i hi
    refine ⟨e i, ?_, e.symm_apply_apply i⟩
    simpa only [Set.mem_setOf_eq, eval_equiv_eq_zero_iff, ne_eq] using hi
  · intro hfinite
    rw [support_equiv]
    exact hfinite.image e

/-- The usual finite-support approximation is transported by the same index
and fibre equivalences. -/
theorem exists_finset_norm_equiv_sub_truncate_lt
    (x : C0DirectSum A) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ι,
      ‖equiv A B e E x -
        truncate B (s.map e.toEmbedding) (equiv A B e E x)‖ < ε := by
  obtain ⟨s, hs⟩ := exists_finset_norm_sub_truncate_lt A x hε
  refine ⟨s, ?_⟩
  rw [← equiv_truncate, ← map_sub, norm_equiv_apply]
  exact hs

end MathlibAnnex.Analysis.CStarAlgebra.C0DirectSum
