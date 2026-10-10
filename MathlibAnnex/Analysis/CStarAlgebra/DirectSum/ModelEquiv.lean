/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.CompactEquiv

/-!
# Assembly of compact-operator c₀-sum models

This file supplies the algebraic assembly needed after two C-star algebras have
already been identified with actual dependent c₀-sums.  The final equivalence
is constructed from the two model equivalences, an index equivalence, and
fibrewise equivalences.  It is not assumed as an input.

For compact-operator fibres there are two endpoints: one accepts explicit
fibrewise compact-algebra star equivalences, and the other obtains them from
complex-linear Hilbert-space isometry equivalences.  This is the reusable
assembly portion of Paper 8.12.  Classification of all irreducible
representations and identification of a reduced atomic range remain separate
inputs and are not asserted here.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uι uκ uA uB uF uG uH uK

/-- Assemble two arbitrary dependent c₀-sum models from an index equivalence
and fibrewise C-star equivalences. -/
def c0DirectSumModelStarAlgEquiv
    {ι : Type uι} {κ : Type uκ}
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (F : ι → Type uF) (G : κ → Type uG)
    [∀ i, NonUnitalCStarAlgebra (F i)]
    [∀ j, NonUnitalCStarAlgebra (G j)]
    (EA : A ≃⋆ₐ[ℂ] C0DirectSum F)
    (EB : B ≃⋆ₐ[ℂ] C0DirectSum G)
    (e : ι ≃ κ) (E : ∀ i, F i ≃⋆ₐ[ℂ] G (e i)) : A ≃⋆ₐ[ℂ] B :=
  (EA.trans (C0DirectSum.equiv F G e E)).trans EB.symm

@[simp]
theorem c0DirectSumModelStarAlgEquiv_apply
    {ι : Type uι} {κ : Type uκ}
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (F : ι → Type uF) (G : κ → Type uG)
    [∀ i, NonUnitalCStarAlgebra (F i)]
    [∀ j, NonUnitalCStarAlgebra (G j)]
    (EA : A ≃⋆ₐ[ℂ] C0DirectSum F)
    (EB : B ≃⋆ₐ[ℂ] C0DirectSum G)
    (e : ι ≃ κ) (E : ∀ i, F i ≃⋆ₐ[ℂ] G (e i)) (a : A) :
    c0DirectSumModelStarAlgEquiv F G EA EB e E a =
      EB.symm (C0DirectSum.equiv F G e E (EA a)) := rfl

@[simp]
theorem c0DirectSumModelStarAlgEquiv_symm_apply
    {ι : Type uι} {κ : Type uκ}
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (F : ι → Type uF) (G : κ → Type uG)
    [∀ i, NonUnitalCStarAlgebra (F i)]
    [∀ j, NonUnitalCStarAlgebra (G j)]
    (EA : A ≃⋆ₐ[ℂ] C0DirectSum F)
    (EB : B ≃⋆ₐ[ℂ] C0DirectSum G)
    (e : ι ≃ κ) (E : ∀ i, F i ≃⋆ₐ[ℂ] G (e i)) (b : B) :
    (c0DirectSumModelStarAlgEquiv F G EA EB e E).symm b =
      EA.symm ((C0DirectSum.equiv F G e E).symm (EB b)) := rfl

/-- Coordinate formula for the assembled model equivalence. -/
@[simp]
theorem eval_c0DirectSumModelStarAlgEquiv
    {ι : Type uι} {κ : Type uκ}
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (F : ι → Type uF) (G : κ → Type uG)
    [∀ i, NonUnitalCStarAlgebra (F i)]
    [∀ j, NonUnitalCStarAlgebra (G j)]
    (EA : A ≃⋆ₐ[ℂ] C0DirectSum F)
    (EB : B ≃⋆ₐ[ℂ] C0DirectSum G)
    (e : ι ≃ κ) (E : ∀ i, F i ≃⋆ₐ[ℂ] G (e i)) (a : A) (i : ι) :
    C0DirectSum.eval G (e i)
        (EB (c0DirectSumModelStarAlgEquiv F G EA EB e E a)) =
      E i (C0DirectSum.eval F i (EA a)) := by
  rw [c0DirectSumModelStarAlgEquiv_apply, EB.apply_symm_apply,
    C0DirectSum.eval_equiv_apply]

/-- The assembled equivalence preserves the original C-star norms. -/
@[simp]
theorem norm_c0DirectSumModelStarAlgEquiv_apply
    {ι : Type uι} {κ : Type uκ}
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (F : ι → Type uF) (G : κ → Type uG)
    [∀ i, NonUnitalCStarAlgebra (F i)]
    [∀ j, NonUnitalCStarAlgebra (G j)]
    (EA : A ≃⋆ₐ[ℂ] C0DirectSum F)
    (EB : B ≃⋆ₐ[ℂ] C0DirectSum G)
    (e : ι ≃ κ) (E : ∀ i, F i ≃⋆ₐ[ℂ] G (e i)) (a : A) :
    ‖c0DirectSumModelStarAlgEquiv F G EA EB e E a‖ = ‖a‖ := by
  simpa only [StarAlgEquiv.toNonUnitalStarAlgHom_apply, map_zero, dist_zero_right] using
    (NonUnitalStarAlgHom.isometry
      (c0DirectSumModelStarAlgEquiv F G EA EB e E).toNonUnitalStarAlgHom
      (c0DirectSumModelStarAlgEquiv F G EA EB e E).injective).dist_eq a 0

section Compact

variable {ι : Type uι} {κ : Type uκ}
variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable (H : ι → Type uH) (K : κ → Type uK)
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]
variable [∀ j, NormedAddCommGroup (K j)] [∀ j, InnerProductSpace ℂ (K j)]
variable [∀ j, CompleteSpace (K j)]

private abbrev FiberH (i : ι) :=
  ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i)

private abbrev FiberK (j : κ) :=
  ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (K j)

/-- Assembly from explicit equivalences of the compact-operator fibres. -/
def compactDirectSumModelStarAlgEquivOfFiber
    (EA : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H)
    (EB : B ≃⋆ₐ[ℂ] CompactOperatorC0Sum K)
    (e : ι ≃ κ) (E : ∀ i, FiberH H i ≃⋆ₐ[ℂ] FiberK K (e i)) :
    A ≃⋆ₐ[ℂ] B :=
  c0DirectSumModelStarAlgEquiv
    (fun i => FiberH H i) (fun j => FiberK K j) EA EB e E

set_option backward.isDefEq.respectTransparency false in
/-- Assembly from complex-linear Hilbert-space isometry equivalences on the
fibres.  The compact fibre equivalences are constructed, not assumed. -/
def compactDirectSumModelStarAlgEquiv
    (EA : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H)
    (EB : B ≃⋆ₐ[ℂ] CompactOperatorC0Sum K)
    (e : ι ≃ κ) (U : ∀ i, H i ≃ₗᵢ[ℂ] K (e i)) : A ≃⋆ₐ[ℂ] B :=
  compactDirectSumModelStarAlgEquivOfFiber H K EA EB e
    (fun i => (U i).compactOperatorStarAlgEquiv)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem compactDirectSumModelStarAlgEquiv_apply
    (EA : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H)
    (EB : B ≃⋆ₐ[ℂ] CompactOperatorC0Sum K)
    (e : ι ≃ κ) (U : ∀ i, H i ≃ₗᵢ[ℂ] K (e i)) (a : A) :
    compactDirectSumModelStarAlgEquiv H K EA EB e U a =
      EB.symm (CompactOperatorC0Sum.equiv H K e U (EA a)) := by
  exact c0DirectSumModelStarAlgEquiv_apply
    (fun i => FiberH H i) (fun j => FiberK K j)
    EA EB e (fun i => (U i).compactOperatorStarAlgEquiv) a

set_option backward.isDefEq.respectTransparency false in
/-- Coordinate formula for the assembled compact-operator model. -/
@[simp]
theorem eval_compactDirectSumModelStarAlgEquiv
    (EA : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H)
    (EB : B ≃⋆ₐ[ℂ] CompactOperatorC0Sum K)
    (e : ι ≃ κ) (U : ∀ i, H i ≃ₗᵢ[ℂ] K (e i)) (a : A) (i : ι) :
    C0DirectSum.eval (fun j => FiberK K j) (e i)
        (EB (compactDirectSumModelStarAlgEquiv H K EA EB e U a)) =
      (U i).compactOperatorStarAlgEquiv
        (C0DirectSum.eval (fun j => FiberH H j) i (EA a)) := by
  exact eval_c0DirectSumModelStarAlgEquiv
    (fun j => FiberH H j) (fun j => FiberK K j)
    EA EB e (fun j => (U j).compactOperatorStarAlgEquiv) a i

/-- The explicit data yield the desired star-algebra equivalence; the final
equivalence is not an input. -/
theorem nonempty_starAlgEquiv_of_compact_direct_sum_models
    (EA : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H)
    (EB : B ≃⋆ₐ[ℂ] CompactOperatorC0Sum K)
    (e : ι ≃ κ) (U : ∀ i, H i ≃ₗᵢ[ℂ] K (e i)) :
    Nonempty (A ≃⋆ₐ[ℂ] B) :=
  ⟨compactDirectSumModelStarAlgEquiv H K EA EB e U⟩

end Compact

end MathlibAnnex.Analysis.CStarAlgebra
