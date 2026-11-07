/- Fixed Pair R6 §9 finite max-tent code. Fin labels encode integers -k,...,k.
No switch to a product tent or another norm.
Execution evidence is recorded in the external receipts. -/
import BanachGeometry.HilbertSums.Coding.Scalar
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Normed.Module.Normalize

noncomputable section
open scoped BigOperators NNReal
namespace BanachGeometry.HilbertSums.Coding

abbrev GridPoint (k : ℕ) := Fin k → Fin (2 * k + 1)
abbrev CodeSpace (k : ℕ) := EuclideanSpace ℝ (GridPoint k)

def gridValue (k : ℕ) (a : Fin (2 * k + 1)) : ℝ := (a.val : ℝ) - k

@[simp] theorem card_gridPoint (k : ℕ) : Fintype.card (GridPoint k) = (2 * k + 1) ^ k := by
  simp [GridPoint]

/-- Taking the maximum in NNReal supplies the empty maximum 0 at level k=0. -/
def codingErrorNN (k : ℕ) (x : Fin k → ℝ) (a : GridPoint k) : ℝ≥0 :=
  Finset.univ.sup fun j => ‖(k : ℝ) * x j - gridValue k (a j)‖₊

def codingError (k : ℕ) (x : Fin k → ℝ) (a : GridPoint k) : ℝ := codingErrorNN k x a

def tent (k : ℕ) (x : Fin k → ℝ) (a : GridPoint k) : ℝ :=
  max 0 (1 - codingError k x a)

def tentVector (k : ℕ) (x : Fin k → ℝ) : CodeSpace k :=
  WithLp.toLp 2 (tent k x)

def unitCode (k : ℕ) (x : Fin k → ℝ) : CodeSpace k :=
  NormedSpace.normalize (tentVector k x)

@[simp] theorem tentVector_apply (k : ℕ) (x : Fin k → ℝ) (a : GridPoint k) :
    tentVector k x a = tent k x a := rfl

theorem codingError_nonneg (k : ℕ) (x : Fin k → ℝ) (a : GridPoint k) :
    0 ≤ codingError k x a := (codingErrorNN k x a).coe_nonneg

theorem coordinate_le_codingError (k : ℕ) (x : Fin k → ℝ) (a : GridPoint k) (j : Fin k) :
    |(k : ℝ) * x j - gridValue k (a j)| ≤ codingError k x a := by
  simpa only [codingError, codingErrorNN, coe_nnnorm, Real.norm_eq_abs] using
    (show ((‖(k : ℝ) * x j - gridValue k (a j)‖₊ : ℝ≥0) : ℝ) ≤
      (Finset.univ.sup (fun i => ‖(k : ℝ) * x i - gridValue k (a i)‖₊) : ℝ≥0) from
      NNReal.coe_le_coe.mpr (Finset.le_sup
        (f := fun i => ‖(k : ℝ) * x i - gridValue k (a i)‖₊) (Finset.mem_univ j)))

theorem codingError_le {k : ℕ} {x : Fin k → ℝ} {a : GridPoint k} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ j, |(k : ℝ) * x j - gridValue k (a j)| ≤ C) :
    codingError k x a ≤ C := by
  lift C to ℝ≥0 using hC with C hCeq
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro j _
  exact_mod_cast h j

theorem tent_nonneg (k : ℕ) (x : Fin k → ℝ) (a : GridPoint k) : 0 ≤ tent k x a :=
  le_max_left _ _

theorem tent_le_one (k : ℕ) (x : Fin k → ℝ) (a : GridPoint k) : tent k x a ≤ 1 := by
  unfold tent
  exact max_le (by norm_num) (by linarith [codingError_nonneg k x a])

theorem tent_ne_zero_iff (k : ℕ) (x : Fin k → ℝ) (a : GridPoint k) :
    tent k x a ≠ 0 ↔ codingError k x a < 1 := by
  simp only [tent, ne_eq, max_eq_left_iff, not_le]
  constructor <;> intro h <;> linarith

/-- Rounding a point of [-k,k] gives an actual label in the finite grid. -/
theorem exists_grid_digit (k : ℕ) (t : ℝ) (ht : |t| ≤ k) :
    ∃ a : Fin (2 * k + 1), |t - gridValue k a| ≤ 1 / 2 := by
  let z : ℤ := round (t + k)
  have hzerr : |(t + k) - (z : ℝ)| ≤ 1 / 2 := abs_sub_round _
  have htlo : -(k : ℝ) ≤ t := (abs_le.mp ht).1
  have hthi : t ≤ k := (abs_le.mp ht).2
  have hzloR : (-1 : ℝ) < (z : ℝ) := by linarith [(abs_le.mp hzerr).2]
  have hzlo : 0 ≤ z := by
    have : (-1 : ℤ) < z := by exact_mod_cast hzloR
    omega
  have hzhiR : (z : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [(abs_le.mp hzerr).1]
  have hzhi : z < (2 * k + 1 : ℕ) := by exact_mod_cast hzhiR
  have hnat : z.toNat < 2 * k + 1 := by omega
  let a : Fin (2 * k + 1) := ⟨z.toNat, hnat⟩
  have hacast : (a.val : ℝ) = (z : ℝ) := by
    dsimp [a]
    exact_mod_cast Int.toNat_of_nonneg hzlo
  refine ⟨a, ?_⟩
  calc
    |t - gridValue k a| = |(t + k) - (z : ℝ)| := by rw [gridValue, hacast]; congr 1 <;> ring
    _ ≤ 1 / 2 := hzerr

theorem exists_near_grid (k : ℕ) (x : Fin k → ℝ) (hx : ∀ j, |x j| ≤ 1) :
    ∃ a : GridPoint k, codingError k x a ≤ 1 / 2 := by
  have hbound (j : Fin k) : |(k : ℝ) * x j| ≤ k := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    simpa using mul_le_mul_of_nonneg_left (hx j) (Nat.cast_nonneg k)
  choose a ha using fun j => exists_grid_digit k ((k : ℝ) * x j) (hbound j)
  exact ⟨a, codingError_le (by norm_num) ha⟩

theorem one_half_le_norm_tentVector (k : ℕ) (x : Fin k → ℝ) (hx : ∀ j, |x j| ≤ 1) :
    1 / 2 ≤ ‖tentVector k x‖ := by
  obtain ⟨a, ha⟩ := exists_near_grid k x hx
  have ht : 1 / 2 ≤ tent k x a :=
    (show (1 / 2 : ℝ) ≤ 1 - codingError k x a by linarith).trans (le_max_right _ _)
  calc
    1 / 2 ≤ tent k x a := ht
    _ = ‖tentVector k x a‖ := by simp [Real.norm_eq_abs, abs_of_nonneg (tent_nonneg k x a)]
    _ ≤ ‖tentVector k x‖ := PiLp.norm_apply_le _ _

theorem tentVector_ne_zero (k : ℕ) (x : Fin k → ℝ) (hx : ∀ j, |x j| ≤ 1) :
    tentVector k x ≠ 0 := by
  intro h
  have hl := one_half_le_norm_tentVector k x hx
  rw [h, norm_zero] at hl
  norm_num at hl

theorem norm_unitCode (k : ℕ) (x : Fin k → ℝ) (hx : ∀ j, |x j| ≤ 1) :
    ‖unitCode k x‖ = 1 :=
  NormedSpace.norm_normalize (tentVector_ne_zero k x hx)

theorem unitCode_coordinate_ne_zero_iff (k : ℕ) (x : Fin k → ℝ)
    (hx : ∀ j, |x j| ≤ 1) (a : GridPoint k) :
    unitCode k x a ≠ 0 ↔ tent k x a ≠ 0 := by
  have hn : ‖tentVector k x‖ ≠ 0 := norm_ne_zero_iff.mpr (tentVector_ne_zero k x hx)
  simp [unitCode, NormedSpace.normalize, hn]

/-- Shared nonzero grid coordinates force all observed coordinates within 2/k. -/
theorem shared_support_close {k : ℕ} (hk : 0 < k) (x z : Fin k → ℝ) (a : GridPoint k)
    (hx : tent k x a ≠ 0) (hz : tent k z a ≠ 0) (j : Fin k) :
    |x j - z j| < 2 / k := by
  have hx' := (coordinate_le_codingError k x a j).trans_lt ((tent_ne_zero_iff k x a).mp hx)
  have hz' := (coordinate_le_codingError k z a j).trans_lt ((tent_ne_zero_iff k z a).mp hz)
  have hscaled : (k : ℝ) * |x j - z j| < 2 := by
    have htriangle := abs_sub ( (k : ℝ) * x j - gridValue k (a j))
      ((k : ℝ) * z j - gridValue k (a j))
    have heq : ((k : ℝ) * x j - gridValue k (a j)) -
        ((k : ℝ) * z j - gridValue k (a j)) = (k : ℝ) * (x j - z j) := by ring
    rw [heq, abs_mul, abs_of_nonneg (Nat.cast_nonneg k)] at htriangle
    linarith
  exact (lt_div_iff₀ (by exact_mod_cast hk : (0 : ℝ) < k)).2 (by simpa [mul_comm] using hscaled)

theorem unitCode_support_disjoint {k : ℕ} (hk : 0 < k) (x z : Fin k → ℝ)
    (hx : ∀ j, |x j| ≤ 1) (hz : ∀ j, |z j| ≤ 1)
    (j : Fin k) (hsep : 2 / (k : ℝ) ≤ |x j - z j|) :
    Disjoint (Function.support (unitCode k x)) (Function.support (unitCode k z)) := by
  apply Set.disjoint_left.mpr
  intro a ha hb
  exact (not_lt_of_ge hsep) (shared_support_close hk x z a
    ((unitCode_coordinate_ne_zero_iff k x hx a).mp ha)
    ((unitCode_coordinate_ne_zero_iff k z hz a).mp hb) j)

end BanachGeometry.HilbertSums.Coding
