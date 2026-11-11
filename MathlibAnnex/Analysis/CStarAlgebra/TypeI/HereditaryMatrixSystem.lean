/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.Hereditary.MatrixCorners
import MathlibAnnex.Analysis.CStarAlgebra.Hereditary.Plateau
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.HereditaryCornerLink
import MathlibAnnex.Analysis.CStarAlgebra.CAR.FiniteStages
import Mathlib.Data.Fin.Basic

/-!
# Coherent finite hereditary matrix systems

Each level is obtained by choosing one split in a representative hereditary
corner and applying all previously chosen entries to that split. Indices use
the existing CAR `stepIndexEquiv`, in the order old coordinate × new bit.
Thus this construction never chooses independent splits in different siblings.

The entries are linear maps with coefficients in genuine closed hereditary
algebras. Their exact multiplication, star, coefficient norm, and refinement
formulas are proved below. Smaller plateau cores have actual local units in
the larger coefficient algebra; the local units are not required to be projections.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra
open MathlibAnnex.CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

private def cornerBit (i : Fin 2) : Bool := decide (i ≠ 0)

private theorem cornerBit_injective : Function.Injective cornerBit := by
  intro i j hij
  by_cases hi : i = 0
  · subst i
    have hj : j = 0 := by
      by_contra hj
      simp [cornerBit, hj] at hij
    exact hj.symm
  · have hj : j ≠ 0 := by
      intro hj
      subst j
      simp [cornerBit, hi] at hij
    exact (Fin.eq_one_of_ne_zero i hi).trans (Fin.eq_one_of_ne_zero j hj).symm

/-- A single two-by-two entry, bundled as an ambient linear map. -/
def hereditaryMatrixEntryLinearMap (v : A) (i j : Bool) : A →ₗ[ℂ] A where
  toFun := hereditaryMatrixEntry v i j
  map_add' := hereditaryMatrixEntry_add v i j
  map_smul' := hereditaryMatrixEntry_smul v i j

private theorem matrixEntryLinearMap_apply (v : A) (i j : Bool) (z : A) :
    hereditaryMatrixEntryLinearMap v i j z = hereditaryMatrixEntry v i j z := rfl

/-- Iterated actual corner entries, with exactly the existing CAR index order. -/
def hereditaryStageEntry (v : ℕ → A) :
    (n : ℕ) → Fin (2 ^ n) → Fin (2 ^ n) → A →ₗ[ℂ] A
  | 0, _, _ => LinearMap.id
  | n + 1, i, j =>
      (hereditaryStageEntry v n ((CAR.stepIndexEquiv n).symm i).1
        ((CAR.stepIndexEquiv n).symm j).1).comp
        (hereditaryMatrixEntryLinearMap (v n)
          (cornerBit ((CAR.stepIndexEquiv n).symm i).2)
          (cornerBit ((CAR.stepIndexEquiv n).symm j).2))

@[simp]
theorem hereditaryStageEntry_zero (v : ℕ → A) (i j : Fin (2 ^ 0)) (z : A) :
    hereditaryStageEntry v 0 i j z = z := rfl

/-- The child entry is evaluated by the old entry on the same representative
split. This is the exact refinement equality used for matrix actions. -/
theorem hereditaryStageEntry_step (v : ℕ → A) (n : ℕ)
    (i j : Fin (2 ^ n)) (b d : Fin 2) (z : A) :
    hereditaryStageEntry v (n + 1) (CAR.stepIndexEquiv n (i, b))
      (CAR.stepIndexEquiv n (j, d)) z =
      hereditaryStageEntry v n i j
        (hereditaryMatrixEntry (v n) (decide (b ≠ 0)) (decide (d ≠ 0)) z) := by
  simp only [hereditaryStageEntry, Equiv.symm_apply_apply, LinearMap.comp_apply,
    matrixEntryLinearMap_apply, cornerBit]

/-- Adjoint compatibility holds for every ambient coefficient, before any
hereditary membership restriction. -/
theorem star_hereditaryStageEntry (v : ℕ → A) (n : ℕ)
    (i j : Fin (2 ^ n)) (z : A) :
    star (hereditaryStageEntry v n i j z) = hereditaryStageEntry v n j i (star z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      simp only [hereditaryStageEntry, LinearMap.comp_apply,
        matrixEntryLinearMap_apply, ih, star_hereditaryMatrixEntry]

/-- All entries stay in an actual common parent closed hereditary algebra. -/
theorem hereditaryStageEntry_mem {a : A} (v : ℕ → A) (n : ℕ)
    (hv : ∀ k < n, v k ∈ hereditarySubalgebra a)
    (i j : Fin (2 ^ n)) {z : A} (hz : z ∈ hereditarySubalgebra a) :
    hereditaryStageEntry v n i j z ∈ hereditarySubalgebra a := by
  induction n generalizing z with
  | zero => exact hz
  | succ n ih =>
      apply ih (fun k hk => hv k (Nat.lt_trans hk (Nat.lt_succ_self n)))
      exact hereditaryMatrixEntry_mem (hv n (Nat.lt_succ_self n)) hz _ _

section FixedSystem

variable (c v : ℕ → A)
variable (hc : ∀ n, IsSelfAdjoint (c n))
variable (hchild : ∀ n, c (n + 1) ∈ hereditarySubalgebra (c n))
variable (hlink : ∀ n, v n ∈ hereditarySubalgebra (c n))
variable (hfix : ∀ n, star (v n) * v n * c (n + 1) = c (n + 1))
variable (hzero : ∀ n, c (n + 1) * v n = 0)

include hc hchild hlink hfix in
/-- Every stage entry preserves the norm of its actual hereditary coefficient. -/
theorem norm_hereditaryStageEntry (n : ℕ) (i j : Fin (2 ^ n))
    {z : A} (hz : z ∈ hereditarySubalgebra (c n)) :
    ‖hereditaryStageEntry v n i j z‖ = ‖z‖ := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      have hz' := hereditarySubalgebra_le_of_mem (hchild n) hz
      have hm := hereditaryMatrixEntry_mem (hlink n) hz'
        (cornerBit ((CAR.stepIndexEquiv n).symm i).2)
        (cornerBit ((CAR.stepIndexEquiv n).symm j).2)
      change ‖hereditaryStageEntry v n _ _
        (hereditaryMatrixEntry (v n) _ _ z)‖ = ‖z‖
      rw [ih _ _ hm]
      exact norm_hereditaryMatrixEntry (hc (n + 1)) (hfix n) hz _ _

include hc hchild hlink hfix hzero in
/-- Exact finite matrix multiplication. At no stage is a scalar matrix unit
asserted to be an element of the original algebra. -/
theorem hereditaryStageEntry_mul (n : ℕ) (i j k l : Fin (2 ^ n))
    {z w : A} (hz : z ∈ hereditarySubalgebra (c n))
    (hw : w ∈ hereditarySubalgebra (c n)) :
    hereditaryStageEntry v n i j z * hereditaryStageEntry v n k l w =
      if j = k then hereditaryStageEntry v n i l (z * w) else 0 := by
  induction n generalizing z w with
  | zero =>
      have hjk : j = k := by apply Fin.ext; omega
      simp only [hereditaryStageEntry_zero, if_pos hjk]
  | succ n ih =>
      let i' := (CAR.stepIndexEquiv n).symm i
      let j' := (CAR.stepIndexEquiv n).symm j
      let k' := (CAR.stepIndexEquiv n).symm k
      let l' := (CAR.stepIndexEquiv n).symm l
      have hz' := hereditarySubalgebra_le_of_mem (hchild n) hz
      have hw' := hereditarySubalgebra_le_of_mem (hchild n) hw
      have hzm := hereditaryMatrixEntry_mem (hlink n) hz' (cornerBit i'.2) (cornerBit j'.2)
      have hwm := hereditaryMatrixEntry_mem (hlink n) hw' (cornerBit k'.2) (cornerBit l'.2)
      change hereditaryStageEntry v n i'.1 j'.1
          (hereditaryMatrixEntry (v n) (cornerBit i'.2) (cornerBit j'.2) z) *
        hereditaryStageEntry v n k'.1 l'.1
          (hereditaryMatrixEntry (v n) (cornerBit k'.2) (cornerBit l'.2) w) = _
      rw [ih _ _ _ _ hzm hwm]
      by_cases hold : j'.1 = k'.1
      · rw [if_pos hold, hereditaryMatrixEntry_mul (hc (n + 1)) (hfix n) (hzero n) hz hw]
        by_cases hbit : cornerBit j'.2 = cornerBit k'.2
        · have hjk : j = k := (CAR.stepIndexEquiv n).symm.injective
            (Prod.ext hold (cornerBit_injective hbit))
          rw [if_pos hbit, if_pos hjk]
          rfl
        · have hjk : j ≠ k := by
            intro h
            subst k
            exact hbit rfl
          rw [if_neg hbit, map_zero, if_neg hjk]
      · have hjk : j ≠ k := by
          intro h
          subst k
          exact hold rfl
        rw [if_neg hold, if_neg hjk]

end FixedSystem

/-- The recursive choices retain a larger coefficient corner, a smaller
nonzero plateau core, its local unit, and one link chosen inside that core.
All data lie in the original arbitrary nonunital algebra. -/
theorem IsAntiliminal.exists_hereditary_matrix_data (hA : IsAntiliminal A)
    {a : A} (ha : 0 ≤ a) (ha0 : a ≠ 0) :
    ∃ c b e v : ℕ → A, c 0 = a ∧
      (∀ n, 0 ≤ c n ∧ c n ≠ 0) ∧
      (∀ n, 0 ≤ b n ∧ b n ≠ 0 ∧ b n ∈ hereditarySubalgebra (c n) ∧
        0 ≤ e n ∧ ‖e n‖ ≤ 1 ∧ e n ∈ hereditarySubalgebra (c n) ∧
        e n * b n = b n ∧ b n * e n = b n) ∧
      (∀ n, c (n + 1) ∈ hereditarySubalgebra (b n) ∧
        v n ∈ hereditarySubalgebra (b n) ∧ ‖v n‖ ≤ 1 ∧ v n * v n = 0 ∧
        star (v n) * v n * c (n + 1) = c (n + 1) ∧ c (n + 1) * v n = 0) := by
  classical
  let P := {z : A // 0 ≤ z ∧ z ≠ 0}
  have hp (z : P) := exists_nonzero_hereditary_plateau z.property.1 z.property.2
  let core (z : P) : A := (hp z).choose
  let unit (z : P) : A := (hp z).choose_spec.choose
  have hplateau (z : P) :
      0 ≤ core z ∧ core z ≠ 0 ∧ core z ∈ hereditarySubalgebra z.1 ∧
      0 ≤ unit z ∧ ‖unit z‖ ≤ 1 ∧ unit z ∈ hereditarySubalgebra z.1 ∧
      unit z * core z = core z ∧ core z * unit z = core z :=
    (hp z).choose_spec.choose_spec
  have hs (z : P) := hA.exists_contractive_hereditary_corner_link (hplateau z).2.1
  let next (z : P) : P := ⟨(hs z).choose,
    (hs z).choose_spec.choose_spec.2.2.1,
    (hs z).choose_spec.choose_spec.2.2.2.1⟩
  let link (z : P) : A := (hs z).choose_spec.choose
  have hsplit (z : P) : (next z).1 ∈ hereditarySubalgebra (core z) ∧
      link z ∈ hereditarySubalgebra (core z) ∧ ‖link z‖ ≤ 1 ∧ link z * link z = 0 ∧
      star (link z) * link z * (next z).1 = (next z).1 ∧ (next z).1 * link z = 0 := by
    have h := (hs z).choose_spec.choose_spec
    exact ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
      h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩
  let node : ℕ → P := fun n => Nat.rec (⟨a, ha, ha0⟩ : P) (fun _ z => next z) n
  refine ⟨fun n => (node n).1, fun n => core (node n), fun n => unit (node n),
    fun n => link (node n), rfl, (fun n => (node n).property),
    (fun n => hplateau (node n)), ?_⟩
  intro n
  exact hsplit (node n)

end MathlibAnnex.Analysis.CStarAlgebra
