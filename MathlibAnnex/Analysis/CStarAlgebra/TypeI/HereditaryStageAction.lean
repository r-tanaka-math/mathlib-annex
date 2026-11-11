/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.Hereditary.MatrixAction
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.HereditaryMatrixSystem
import Mathlib.Data.Fintype.BigOperators

/-!
# Scalar actions on successive hereditary matrix systems

The scalar matrix acting on a hereditary stage passes to its standard CAR
amplification at the next stage. The proof uses the actual corner recursion,
the inclusion of the next coefficient algebra in the current one, and the
specified link's membership in that current coefficient algebra.

Both action identities are proved by reindexing the finite sums through the
existing `CAR.stepIndexEquiv`. No scalar matrix units in the ambient algebra,
faithfulness, projections, or separability are assumed here.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace MathlibAnnex.CStarAlgebra.CAR

/-- The standard CAR step has the old matrix entry on equal new bit
coordinates and zero on unequal new bit coordinates. -/
theorem step_apply_stepIndexEquiv (n : ℕ) (M : Stage n)
    (i j : Fin (2 ^ n)) (s t : Fin 2) :
    step n M (stepIndexEquiv n (i, s)) (stepIndexEquiv n (j, t)) =
      if s = t then M i j else 0 := by
  change amplify n M
      ((stepIndexEquiv n).symm (stepIndexEquiv n (i, s)))
      ((stepIndexEquiv n).symm (stepIndexEquiv n (j, t))) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  by_cases hst : s = t <;> simp [amplify, Matrix.kronecker_apply, hst]

/-- Reindex one column of an amplified scalar action. The new bit coordinate
is forced to agree with the fixed column's bit coordinate. -/
theorem sum_step_column_smul {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (n : ℕ) (M : Stage n) (i : Fin (2 ^ n)) (s : Fin 2)
    (f : Fin (2 ^ (n + 1)) → V) :
    (∑ k, step n M k (stepIndexEquiv n (i, s)) • f k) =
      ∑ k, M k i • f (stepIndexEquiv n (k, s)) := by
  classical
  calc
    (∑ k, step n M k (stepIndexEquiv n (i, s)) • f k) =
        ∑ p : Fin (2 ^ n) × Fin 2,
          step n M (stepIndexEquiv n p) (stepIndexEquiv n (i, s)) •
            f (stepIndexEquiv n p) :=
      ((stepIndexEquiv n).sum_comp _).symm
    _ = ∑ k, ∑ t : Fin 2,
        (if t = s then M k i else 0) • f (stepIndexEquiv n (k, t)) := by
      rw [Fintype.sum_prod_type]
      simp only [step_apply_stepIndexEquiv]
    _ = ∑ k, M k i • f (stepIndexEquiv n (k, s)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_eq_single s]
      · simp
      · intro t ht hts
        simp only [if_neg hts, zero_smul]
      · intro hs
        exact (hs (Finset.mem_univ s)).elim

/-- Reindex one row of an amplified scalar action, retaining the fixed
row's new bit coordinate. -/
theorem sum_step_row_smul {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (n : ℕ) (M : Stage n) (j : Fin (2 ^ n)) (t : Fin 2)
    (f : Fin (2 ^ (n + 1)) → V) :
    (∑ k, step n M (stepIndexEquiv n (j, t)) k • f k) =
      ∑ k, M j k • f (stepIndexEquiv n (k, t)) := by
  classical
  calc
    (∑ k, step n M (stepIndexEquiv n (j, t)) k • f k) =
        ∑ p : Fin (2 ^ n) × Fin 2,
          step n M (stepIndexEquiv n (j, t)) (stepIndexEquiv n p) •
            f (stepIndexEquiv n p) :=
      ((stepIndexEquiv n).sum_comp _).symm
    _ = ∑ k, ∑ s : Fin 2,
        (if t = s then M j k else 0) • f (stepIndexEquiv n (k, s)) := by
      rw [Fintype.sum_prod_type]
      simp only [step_apply_stepIndexEquiv]
    _ = ∑ k, M j k • f (stepIndexEquiv n (k, t)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_eq_single t]
      · simp
      · intro s hs hst
        simp only [if_neg hst.symm, zero_smul]
      · intro ht
        exact (ht (Finset.mem_univ t)).elim

end MathlibAnnex.CStarAlgebra.CAR

namespace MathlibAnnex.Analysis.CStarAlgebra

open MathlibAnnex.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- The actual recursive ambient matrix entry restricted to the specified
closed hereditary coefficient algebra. -/
def hereditaryStageCoreEntry (b v : ℕ → A) (n : ℕ)
    (i j : Fin (2 ^ n)) : hereditarySubalgebra (b n) →ₗ[ℂ] A :=
  (hereditaryStageEntry v n i j).comp
    (hereditarySubalgebra (b n)).toNonUnitalSubalgebra.toSubmodule.subtype

@[simp]
theorem hereditaryStageCoreEntry_apply (b v : ℕ → A) (n : ℕ)
    (i j : Fin (2 ^ n)) (z : hereditarySubalgebra (b n)) :
    hereditaryStageCoreEntry b v n i j z = hereditaryStageEntry v n i j (z : A) := rfl

/-- Adjoint compatibility is inherited from the ambient recursion and
requires no matrix-system or nonzero-coefficient hypotheses. -/
@[simp]
theorem star_hereditaryStageCoreEntry (b v : ℕ → A) (n : ℕ)
    (i j : Fin (2 ^ n)) (z : hereditarySubalgebra (b n)) :
    star (hereditaryStageCoreEntry b v n i j z) =
      hereditaryStageCoreEntry b v n j i (star z) := by
  change star (hereditaryStageEntry v n i j (z : A)) =
    hereditaryStageEntry v n j i (star (z : A))
  exact star_hereditaryStageEntry v n i j (z : A)

/-- A scalar action on one hereditary stage acts on the next stage by exactly
the existing CAR step. The inner two-by-two entry belongs to the old core
because both its coefficient and the specified link belong to that core. -/
theorem ActsOnMatrixCorners.hereditaryStageCoreEntry_step (b v : ℕ → A) (n : ℕ)
    (hcore : hereditarySubalgebra (b (n + 1)) ≤ hereditarySubalgebra (b n))
    (hv : v n ∈ hereditarySubalgebra (b n)) {a : A} {M : CAR.Stage n}
    (hM : ActsOnMatrixCorners (hereditaryStageCoreEntry b v n) a M) :
    ActsOnMatrixCorners (hereditaryStageCoreEntry b v (n + 1)) a (CAR.step n M) := by
  classical
  constructor
  · intro i j z
    obtain ⟨⟨i, s⟩, rfl⟩ := (CAR.stepIndexEquiv n).surjective i
    obtain ⟨⟨j, t⟩, rfl⟩ := (CAR.stepIndexEquiv n).surjective j
    let w : hereditarySubalgebra (b n) :=
      ⟨hereditaryMatrixEntry (v n) (decide (s ≠ 0)) (decide (t ≠ 0)) (z : A),
        hereditaryMatrixEntry_mem hv (hcore z.property) _ _⟩
    rw [CAR.sum_step_column_smul]
    simpa only [hereditaryStageCoreEntry_apply, hereditaryStageEntry_step, w] using
      hM.1 i j w
  · intro i j z
    obtain ⟨⟨i, s⟩, rfl⟩ := (CAR.stepIndexEquiv n).surjective i
    obtain ⟨⟨j, t⟩, rfl⟩ := (CAR.stepIndexEquiv n).surjective j
    let w : hereditarySubalgebra (b n) :=
      ⟨hereditaryMatrixEntry (v n) (decide (s ≠ 0)) (decide (t ≠ 0)) (z : A),
        hereditaryMatrixEntry_mem hv (hcore z.property) _ _⟩
    rw [CAR.sum_step_row_smul]
    simpa only [hereditaryStageCoreEntry_apply, hereditaryStageEntry_step, w] using
      hM.2 i j w

end MathlibAnnex.Analysis.CStarAlgebra
