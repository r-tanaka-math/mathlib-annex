/- R6 concrete nonzero finite-dimensional H_(n+1), level isometries, S_0 adapter,
block-by-block scalar observations, and their head dependence.
Nested PiLp 2 keeps every inner product/norm in the actual L2 geometry.
Local execution status is recorded in the external qualification receipts. -/
import BanachGeometry.HilbertSums.Graded.FiniteCoordinates
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section
open scoped BigOperators InnerProductSpace
namespace BanachGeometry.HilbertSums.Nonlinear
open Coding

abbrev BlockCoordinate (n : ℕ) := Σ k : Fin (n + 1), GridPoint k.val
abbrev GradedBlock (n : ℕ) := PiLp 2 (fun k : Fin (n + 1) => CodeSpace k.val)
abbrev GradedHilbert := lp GradedBlock 2

instance blockCoordinate_nonempty (n : ℕ) : Nonempty (BlockCoordinate n) :=
  ⟨⟨⟨0, by omega⟩, fun i => Fin.elim0 i⟩⟩

instance gradedBlock_finiteDimensional (n : ℕ) : FiniteDimensional ℝ (GradedBlock n) := by
  exact Module.Finite.of_injective
    (WithLp.linearEquiv 2 ℝ (∀ k : Fin (n + 1), CodeSpace k.val)).toLinearMap
    (WithLp.linearEquiv 2 ℝ (∀ k : Fin (n + 1), CodeSpace k.val)).injective

instance gradedBlock_complete (n : ℕ) : CompleteSpace (GradedBlock n) := inferInstance
instance gradedBlock_separable (n : ℕ) : TopologicalSpace.SeparableSpace (GradedBlock n) := inferInstance
instance gradedHilbert_complete : CompleteSpace GradedHilbert := inferInstance

/-- The actual isometric inclusion of S_k into H_(n+1), for k≤n. -/
def levelIsometry (n k : ℕ) (hk : k < n + 1) : CodeSpace k →ₗᵢ[ℝ] GradedBlock n where
  toFun u := PiLp.single 2 ⟨k, hk⟩ u
  map_add' u v := by
    simpa using (PiLp.single_add (p := 2) (β := fun j : Fin (n + 1) => CodeSpace j.val)
      (i := (⟨k, hk⟩ : Fin (n + 1))) (a := u) (b := v))
  map_smul' c u := by
    apply PiLp.ext
    intro j
    by_cases hj : j = ⟨k, hk⟩
    · subst j; simp
    · simp [Pi.single_apply, hj]
  norm_map' u := by
    simpa using (PiLp.norm_single (p := 2)
      (β := fun j : Fin (n + 1) => CodeSpace j.val) (⟨k, hk⟩ : Fin (n + 1)) u)

theorem level_inner_ne (n k l : ℕ) (hk : k < n + 1) (hl : l < n + 1) (hkl : k ≠ l)
    (u : CodeSpace k) (v : CodeSpace l) :
    ⟪levelIsometry n k hk u, levelIsometry n l hl v⟫_ℝ = 0 := by
  classical
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j = ⟨k, hk⟩
  · subst j
    have hne : (⟨k, hk⟩ : Fin (n + 1)) ≠ ⟨l, hl⟩ := by
      intro h; exact hkl (congrArg Fin.val h)
    simp [levelIsometry, Pi.single_apply, hne]
  · simp [levelIsometry, Pi.single_apply, hj]

/-- The manuscript's S_0=ℝ is isometrically identical to the singleton code space. -/
def zeroLevelEquiv : CodeSpace 0 ≃ₗᵢ[ℝ] ℝ where
  toFun u := u default
  invFun r := WithLp.toLp 2 (fun _ => r)
  left_inv u := by
    apply PiLp.ext
    intro a
    have ha : a = default := Subsingleton.elim _ _
    subst a
    rfl
  right_inv r := rfl
  map_add' u v := rfl
  map_smul' c u := rfl
  norm_map' u := by
    have hu : u = PiLp.single 2 default (u default) := by
      apply PiLp.ext
      intro a
      have ha : a = default := Subsingleton.elim _ _
      subst a
      simp
    rw [hu, PiLp.norm_single]
    simp

def baseDirection (n : ℕ) : GradedBlock n :=
  levelIsometry n 0 (by omega) (zeroLevelEquiv.symm 1)

theorem norm_baseDirection (n : ℕ) : ‖baseDirection n‖ = 1 := by
  simp [baseDirection]

instance gradedBlock_nontrivial (n : ℕ) : Nontrivial (GradedBlock n) :=
  ⟨⟨baseDirection n, 0, by
    intro h
    have hn := norm_baseDirection n
    rw [h, norm_zero] at hn
    norm_num at hn⟩⟩

instance gradedHilbert_nontrivial : Nontrivial GradedHilbert := by
  refine ⟨⟨lp.single 2 0 (baseDirection 0), 0, ?_⟩⟩
  intro h
  have he := congrArg (fun z : GradedHilbert => z 0) h
  change lp.single (E := GradedBlock) 2 0 (baseDirection 0) 0 = 0 at he
  rw [lp.single_apply_self] at he
  have hn := norm_baseDirection 0
  rw [he, norm_zero] at hn
  norm_num at hn

theorem finrank_gradedBlock (n : ℕ) :
    Module.finrank ℝ (GradedBlock n) = ∑ k : Fin (n + 1), (2 * k.val + 1) ^ k.val := by
  rw [(WithLp.linearEquiv 2 ℝ (∀ k : Fin (n + 1), CodeSpace k.val)).finrank_eq,
    Module.finrank_pi_fintype]
  simp only [CodeSpace, finrank_euclideanSpace, card_gridPoint]

def scalarEnumeration : ℕ ≃ (Σ n, BlockCoordinate n) := FiniteFibres.enumeration BlockCoordinate

/-- The scalar coordinate p_(j+1) reads a genuine coordinate of the first j+1 blocks. -/
def scalarObservation (j : ℕ) (y : GradedHilbert) : ℝ :=
  let a := scalarEnumeration j
  boundedScalar (y a.1 a.2.1 a.2.2)

theorem abs_scalarObservation_lt_one (j : ℕ) (y : GradedHilbert) : |scalarObservation j y| < 1 :=
  abs_boundedScalar_lt_one _

theorem abs_scalarObservation_sub_le (j : ℕ) (y z : GradedHilbert) :
    |scalarObservation j y - scalarObservation j z| ≤ ‖y - z‖ := by
  let a := scalarEnumeration j
  calc
    _ ≤ |y a.1 a.2.1 a.2.2 - z a.1 a.2.1 a.2.2| := abs_boundedScalar_sub_le _ _
    _ = ‖(y - z) a.1 a.2.1 a.2.2‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖(y - z) a.1 a.2.1‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖(y - z) a.1‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖y - z‖ := lp.norm_apply_le_norm (by norm_num) _ _

theorem scalarObservation_head {j N : ℕ} (hj : j < N) (y : GradedHilbert) :
    scalarObservation j (blockHead N y) = scalarObservation j y := by
  have hblock : (scalarEnumeration j).1 < N :=
    (FiniteFibres.enumeration_block_le BlockCoordinate j).trans_lt hj
  simp [scalarObservation, blockHead_apply, hblock]

/-- These observations separate points because the enumeration exhausts every scalar coordinate. -/
theorem scalarObservations_separate {y z : GradedHilbert}
    (h : ∀ j, scalarObservation j y = scalarObservation j z) : y = z := by
  apply lp.ext
  funext n
  apply PiLp.ext
  intro k
  apply PiLp.ext
  intro a
  obtain ⟨j, hj⟩ := scalarEnumeration.surjective ⟨n, ⟨k, a⟩⟩
  let fy : (Σ n, BlockCoordinate n) → ℝ := fun p => boundedScalar (y p.1 p.2.1 p.2.2)
  let fz : (Σ n, BlockCoordinate n) → ℝ := fun p => boundedScalar (z p.1 p.2.1 p.2.2)
  have he : fy (scalarEnumeration j) = fz (scalarEnumeration j) := h j
  apply boundedScalar_injective
  exact (congrArg fy hj).symm.trans (he.trans (congrArg fz hj))

/-- Unit level-k direction in block n; k≤n, and k=0 has no observations. -/
def codeDirection (n k : ℕ) (hk : k < n + 1) (y : GradedHilbert) : GradedBlock n :=
  levelIsometry n k hk (unitCode k (fun j => scalarObservation j.val y))

theorem norm_codeDirection (n k : ℕ) (hk : k < n + 1) (y : GradedHilbert) :
    ‖codeDirection n k hk y‖ = 1 := by
  rw [codeDirection, (levelIsometry n k hk).norm_map]
  exact norm_unitCode _ _ (fun j => (abs_scalarObservation_lt_one _ _).le)

theorem codeDirection_head (n k : ℕ) (hk : k < n + 1) (y : GradedHilbert) :
    codeDirection n k hk (blockHead n y) = codeDirection n k hk y := by
  unfold codeDirection
  congr 2
  funext j
  exact scalarObservation_head (by omega) y

theorem codeDirection_norm_sub_le (n k : ℕ) (hk : k < n + 1) (y z : GradedHilbert) :
    ‖codeDirection n k hk y - codeDirection n k hk z‖ ≤ Clock.codeLipschitz k * ‖y - z‖ := by
  rw [codeDirection, codeDirection, ← (levelIsometry n k hk).map_sub,
    (levelIsometry n k hk).norm_map]
  exact norm_unitCode_sub_le _ _
    (fun j => (abs_scalarObservation_lt_one _ _).le)
    (fun j => (abs_scalarObservation_lt_one _ _).le)
    (norm_nonneg _) (fun j => abs_scalarObservation_sub_le j.val y z)

end BanachGeometry.HilbertSums.Nonlinear
