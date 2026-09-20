import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

/-!
# Unitary dilation of a contraction in a two-by-two C*-matrix algebra

The dilation is built from the selfadjoint matrix D = [[0,a],[a*,0]] and
R = sqrt(1-D^2).  Commutation with diag(1,-1) forces the off-diagonal entries
of R to vanish.  Therefore D+iR is unitary and still has a as its (0,1)
entry.  No polar decomposition, invertibility of a, or Russo--Dye theorem
is assumed.

This supplies the normalization bridge for bounded-sequence bilinear
forms without invoking a C*-ultrapower.  Controller source checkpoint C01;
not compiled and not authorized for a separate Codex dispatch.
-/

set_option autoImplicit false
noncomputable section
open scoped ComplexOrder

namespace MathlibAnnex.MatrixContraction

universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

abbrev TwoByTwo (A : Type u) := CStarMatrix (Fin 2) (Fin 2) A

local instance : NonUnitalContinuousFunctionalCalculus ℝ (TwoByTwo A) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
local instance : ContinuousFunctionalCalculus ℝ (TwoByTwo A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus
local instance : NonnegSpectrumClass ℝ (TwoByTwo A) :=
  CStarAlgebra.instNonnegSpectrumClass

/-- Diagonal inclusion uses the genuine C*-matrix norm. -/
def diagonalHom : A × A →⋆ₐ[ℂ] TwoByTwo A where
  toFun p := CStarMatrix.ofMatrix (fun i j => if i = j then if i = 0 then p.1 else p.2 else 0)
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp [CStarMatrix.one_apply]
  map_add' p q := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' p q := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [CStarMatrix.mul_apply, Fin.sum_univ_two]
  map_star' p := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [CStarMatrix.star_apply]
  commutes' z := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [CStarMatrix.algebraMap_apply]

@[simp] theorem diagonalHom_00 (a b : A) : diagonalHom (a,b) 0 0 = a := rfl
@[simp] theorem diagonalHom_11 (a b : A) : diagonalHom (a,b) 1 1 = b := rfl
@[simp] theorem diagonalHom_01 (a b : A) : diagonalHom (a,b) 0 1 = 0 := rfl
@[simp] theorem diagonalHom_10 (a b : A) : diagonalHom (a,b) 1 0 = 0 := rfl

/-- Selfadjoint off-diagonal embedding, not a claim that a is selfadjoint. -/
def offDiagonal (a : A) : TwoByTwo A :=
  CStarMatrix.ofMatrix (fun i j => if i = 0 then if j = 0 then 0 else a
    else if j = 0 then star a else 0)

@[simp] theorem offDiagonal_00 (a : A) : offDiagonal a 0 0 = 0 := rfl
@[simp] theorem offDiagonal_01 (a : A) : offDiagonal a 0 1 = a := rfl
@[simp] theorem offDiagonal_10 (a : A) : offDiagonal a 1 0 = star a := rfl
@[simp] theorem offDiagonal_11 (a : A) : offDiagonal a 1 1 = 0 := rfl

theorem isSelfAdjoint_offDiagonal (a : A) : IsSelfAdjoint (offDiagonal a) := by
  change star (offDiagonal a) = offDiagonal a
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CStarMatrix.star_apply]

theorem offDiagonal_sq (a : A) :
    offDiagonal a * offDiagonal a = diagonalHom (a * star a, star a * a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CStarMatrix.mul_apply, Fin.sum_univ_two]

/-- No factor two is lost in the off-diagonal matrix norm. -/
theorem norm_offDiagonal (a : A) : ‖offDiagonal a‖ = ‖a‖ := by
  have he : ‖a‖ ≤ ‖offDiagonal a‖ :=
    CStarMatrix.norm_entry_le_norm (M := offDiagonal a) (i := 0) (j := 1)
  have hs : ‖offDiagonal a‖ * ‖offDiagonal a‖ ≤ ‖a‖ * ‖a‖ := by
    calc
      _ = ‖star (offDiagonal a) * offDiagonal a‖ :=
        (CStarRing.norm_star_mul_self (x := offDiagonal a)).symm
      _ = ‖diagonalHom (a * star a, star a * a)‖ := by
        rw [(isSelfAdjoint_offDiagonal a).star_eq, offDiagonal_sq]
      _ ≤ ‖(a * star a, star a * a)‖ := NonUnitalStarAlgHom.norm_apply_le (diagonalHom (A := A)).toNonUnitalStarAlgHom _
      _ = ‖a‖ * ‖a‖ := by
        simp [Prod.norm_def, CStarRing.norm_self_mul_star, CStarRing.norm_star_mul_self]
  exact le_antisymm (by nlinarith [norm_nonneg a, norm_nonneg (offDiagonal a)]) he

def grading : TwoByTwo A := diagonalHom (1,-1)

def defect (a : A) : TwoByTwo A := 1 - offDiagonal a * offDiagonal a

def defectRoot (a : A) : TwoByTwo A := CFC.sqrt (defect a)

theorem defect_nonneg (a : A) (ha : ‖a‖ ≤ 1) : 0 ≤ defect a := by
  have hn : ‖star (offDiagonal a) * offDiagonal a‖ ≤ 1 := by
    rw [CStarRing.norm_star_mul_self, norm_offDiagonal]
    nlinarith [norm_nonneg a]
  have hle : star (offDiagonal a) * offDiagonal a ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg _)).mp hn
  simpa [defect, (isSelfAdjoint_offDiagonal a).star_eq] using sub_nonneg.mpr hle

theorem isSelfAdjoint_defectRoot (a : A) : IsSelfAdjoint (defectRoot a) :=
  IsSelfAdjoint.of_nonneg (by simpa only [defectRoot] using CFC.sqrt_nonneg (defect a))

theorem defectRoot_sq (a : A) (ha : ‖a‖ ≤ 1) :
    defectRoot a * defectRoot a = defect a :=
  CFC.sqrt_mul_sqrt_self _ (defect_nonneg a ha)

theorem defect_commutes (a : A) : Commute (defect a) (offDiagonal a) := by
  change (1 - offDiagonal a * offDiagonal a) * offDiagonal a =
    offDiagonal a * (1 - offDiagonal a * offDiagonal a)
  noncomm_ring

theorem defectRoot_commutes (a : A) : Commute (defectRoot a) (offDiagonal a) := by
  simpa only [defectRoot, CFC.sqrt_eq_cfc] using
    (defect_commutes a).cfc_nnreal NNReal.sqrt

theorem defect_commutes_grading (a : A) : Commute (defect a) (grading (A := A)) := by
  change defect a * grading = grading * defect a
  rw [defect, offDiagonal_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [grading, CStarMatrix.mul_apply, Fin.sum_univ_two, CStarMatrix.one_apply]

theorem defectRoot_commutes_grading (a : A) :
    Commute (defectRoot a) (grading (A := A)) := by
  simpa only [defectRoot, CFC.sqrt_eq_cfc] using
    (defect_commutes_grading a).cfc_nnreal NNReal.sqrt

/-- Commutation with the grading annihilates the off-diagonal entry. -/
theorem defectRoot_01 (a : A) : defectRoot a 0 1 = 0 := by
  have h := congrArg (fun M : TwoByTwo A => M 0 1) (defectRoot_commutes_grading a).eq
  have hneg : -(defectRoot a 0 1) = defectRoot a 0 1 := by
    simpa [grading, CStarMatrix.mul_apply, Fin.sum_univ_two] using h
  have hadd : defectRoot a 0 1 + defectRoot a 0 1 = 0 := by
    calc
      _ = -(defectRoot a 0 1) + defectRoot a 0 1 := by rw [hneg]
      _ = 0 := neg_add_cancel _
  have hs : (2 : ℂ) • defectRoot a 0 1 = 0 := by simpa [two_smul] using hadd
  exact (smul_eq_zero.mp hs).resolve_left (by norm_num)

/-- Actual unitary matrix, with no inverse or polar decomposition of a. -/
def unitaryDilationValue (a : A) : TwoByTwo A := offDiagonal a + Complex.I • defectRoot a

theorem star_unitaryDilationValue (a : A) :
    star (unitaryDilationValue a) = offDiagonal a - Complex.I • defectRoot a := by
  simp [unitaryDilationValue, star_add, star_smul,
    (isSelfAdjoint_offDiagonal a).star_eq, (isSelfAdjoint_defectRoot a).star_eq]
  abel

theorem unitaryDilationValue_mem (a : A) (ha : ‖a‖ ≤ 1) :
    unitaryDilationValue a ∈ unitary (TwoByTwo A) := by
  have hc := (defectRoot_commutes a).eq
  have hs : offDiagonal a * offDiagonal a + defectRoot a * defectRoot a = 1 := by
    rw [defectRoot_sq a ha, defect]
    abel
  constructor
  · rw [star_unitaryDilationValue, unitaryDilationValue]
    calc
      _ = offDiagonal a * offDiagonal a + defectRoot a * defectRoot a := by
        simp only [sub_mul, mul_add, mul_smul_comm, smul_mul_assoc,
          smul_smul, Complex.I_mul_I, neg_one_smul]
        rw [hc]
        simp [smul_sub, smul_smul, Complex.I_mul_I]
        abel
      _ = 1 := hs
  · rw [star_unitaryDilationValue, unitaryDilationValue]
    calc
      _ = offDiagonal a * offDiagonal a + defectRoot a * defectRoot a := by
        simp only [mul_sub, add_mul, mul_smul_comm, smul_mul_assoc,
          smul_smul, Complex.I_mul_I, neg_one_smul]
        rw [hc]
        simp [smul_sub, smul_smul, Complex.I_mul_I]
        abel
      _ = 1 := hs

def unitaryDilation (a : A) (ha : ‖a‖ ≤ 1) : unitary (TwoByTwo A) :=
  ⟨unitaryDilationValue a, unitaryDilationValue_mem a ha⟩

@[simp]
theorem unitaryDilation_entry (a : A) (ha : ‖a‖ ≤ 1) :
    ((unitaryDilation a ha : unitary (TwoByTwo A)) : TwoByTwo A) 0 1 = a := by
  simp [unitaryDilation, unitaryDilationValue, defectRoot_01]

/-- Every contraction is an exact corner of a genuine unitary. -/
theorem exists_unitary_with_entry (a : A) (ha : ‖a‖ ≤ 1) :
    ∃ U : unitary (TwoByTwo A), (U : TwoByTwo A) 0 1 = a :=
  ⟨unitaryDilation a ha, unitaryDilation_entry a ha⟩

end MathlibAnnex.MatrixContraction
