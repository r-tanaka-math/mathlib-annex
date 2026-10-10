/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.Equiv
import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.CompactOperators
import MathlibAnnex.Analysis.InnerProductSpace.CompactOperatorEquiv

/-!
# Equivalences of c₀-sums of compact-operator algebras

A complex-linear Hilbert-space isometry equivalence transports compact
operators by the actual conjugation `T ↦ U T U⁻¹`.  Compactness is proved in
both directions by composition with bounded linear maps.  Fibrewise
conjugation, together with an equivalence of index types, then gives an actual
star-algebra equivalence of dependent c₀-sums of compact-operator algebras.

No separability, countability, or finite-dimensional hypothesis is used.
Conjugate-linear maps are not coerced to complex-linear homomorphisms here.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

open Set
open scoped CStarAlgebra ENNReal


namespace MathlibAnnex.Analysis.CStarAlgebra.CompactOperatorC0Sum

universe uι uκ uH uK

variable {ι : Type uι} {κ : Type uκ}
variable (H : ι → Type uH) (K : κ → Type uK)
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]
variable [∀ j, NormedAddCommGroup (K j)] [∀ j, InnerProductSpace ℂ (K j)]
variable [∀ j, CompleteSpace (K j)]
variable (e : ι ≃ κ) (U : ∀ i, H i ≃ₗᵢ[ℂ] K (e i))

private abbrev FiberH (i : ι) :=
  ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i)

private abbrev FiberK (j : κ) :=
  ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (K j)

/-- Reindex the compact fibres and conjugate each compact operator by the
specified complex-linear Hilbert-space isometry equivalence. -/
def equiv : CompactOperatorC0Sum H ≃⋆ₐ[ℂ] CompactOperatorC0Sum K :=
  C0DirectSum.equiv (fun i => FiberH H i) (fun j => FiberK K j) e
    (fun i => (U i).compactOperatorStarAlgEquiv)

/-- Forward coordinate formula in the compact-operator c₀ sum. -/
@[simp]
theorem eval_equiv_apply (x : CompactOperatorC0Sum H) (i : ι) :
    C0DirectSum.eval (fun j => FiberK K j) (e i) (equiv H K e U x) =
      (U i).compactOperatorStarAlgEquiv
        (C0DirectSum.eval (fun j => FiberH H j) i x) := by
  exact C0DirectSum.eval_equiv_apply
    (fun i => FiberH H i) (fun j => FiberK K j) e
      (fun i => (U i).compactOperatorStarAlgEquiv) x i

/-- Inverse coordinate formula in the compact-operator c₀ sum. -/
@[simp]
theorem eval_equiv_symm_apply (y : CompactOperatorC0Sum K) (i : ι) :
    C0DirectSum.eval (fun j => FiberH H j) i ((equiv H K e U).symm y) =
      ((U i).compactOperatorStarAlgEquiv).symm
        (C0DirectSum.eval (fun j => FiberK K j) (e i) y) := by
  exact C0DirectSum.eval_equiv_symm_apply
    (fun i => FiberH H i) (fun j => FiberK K j) e
      (fun i => (U i).compactOperatorStarAlgEquiv) y i

/-- Literal action of the transported coordinate compact operator. -/
@[simp]
theorem eval_equiv_apply_apply (x : CompactOperatorC0Sum H) (i : ι)
    (y : K (e i)) :
    (C0DirectSum.eval (fun j => FiberK K j) (e i) (equiv H K e U x) :
      K (e i) →L[ℂ] K (e i)) y =
      U i ((C0DirectSum.eval (fun j => FiberH H j) i x :
        H i →L[ℂ] H i) ((U i).symm y)) := by
  rw [eval_equiv_apply]
  rfl

/-- Compact single-coordinate families are transported to the corresponding
reindexed coordinate. -/
@[simp]
theorem equiv_single (i : ι) (T : FiberH H i) :
    equiv H K e U (C0DirectSum.single (fun j => FiberH H j) i T) =
      C0DirectSum.single (fun j => FiberK K j) (e i)
        ((U i).compactOperatorStarAlgEquiv T) := by
  exact C0DirectSum.equiv_single
    (fun i => FiberH H i) (fun j => FiberK K j) e
      (fun i => (U i).compactOperatorStarAlgEquiv) i T

/-- Compact finite truncation commutes with reindexing and fibrewise
conjugation. -/
@[simp]
theorem equiv_truncate (s : Finset ι) (x : CompactOperatorC0Sum H) :
    equiv H K e U (C0DirectSum.truncate (fun i => FiberH H i) s x) =
      C0DirectSum.truncate (fun j => FiberK K j) (s.map e.toEmbedding)
        (equiv H K e U x) := by
  exact C0DirectSum.equiv_truncate
    (fun i => FiberH H i) (fun j => FiberK K j) e
      (fun i => (U i).compactOperatorStarAlgEquiv) s x

/-- The compact c₀ equivalence preserves the original supremum norm. -/
@[simp]
theorem norm_equiv_apply (x : CompactOperatorC0Sum H) :
    ‖equiv H K e U x‖ = ‖x‖ := by
  exact C0DirectSum.norm_equiv_apply
    (fun i => FiberH H i) (fun j => FiberK K j) e
      (fun i => (U i).compactOperatorStarAlgEquiv) x

end MathlibAnnex.Analysis.CStarAlgebra.CompactOperatorC0Sum
