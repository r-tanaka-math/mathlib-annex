import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Analytic.FiniteAverage

/-!
# Exact finite Rademacher moments

The proof uses a coordinate-flip permutation.  The fourth moment contains
all three pairings and subtracts twice the all-equal diagonal.  No circle
integration, four-phase replacement, commutativity of algebra elements, or
asymptotic independence is used. SOURCE_UNBUILT.
-/

set_option autoImplicit false
noncomputable section
open Finset
namespace MathlibAnnex.CStarBilinear.Analytic

universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- A point of the finite sign cube carries only the values +1 and -1. -/
def rSign (ε : ι → Bool) (i : ι) : ℝ := if ε i then -1 else 1

@[simp] theorem rSign_mul_self (ε : ι → Bool) (i : ι) :
    rSign ε i * rSign ε i = 1 := by
  cases h : ε i <;> norm_num [rSign, h]

@[simp] theorem rSign_sq (ε : ι → Bool) (i : ι) : rSign ε i ^ 2 = 1 := by
  simpa [pow_two] using rSign_mul_self ε i

/-- The coordinate-flip is its own inverse, including on a one-coordinate cube. -/
def flipSign (i : ι) (ε : ι → Bool) : ι → Bool :=
  fun j ↦ if j = i then !(ε j) else ε j

theorem flipSign_involutive (i : ι) :
    Function.Involutive (flipSign i) := by
  intro ε
  funext j
  by_cases h : j = i <;> simp [flipSign, h]

def flipSignEquiv (i : ι) : (ι → Bool) ≃ (ι → Bool) where
  toFun := flipSign i
  invFun := flipSign i
  left_inv := flipSign_involutive i
  right_inv := flipSign_involutive i

@[simp] theorem rSign_flip_self (i : ι) (ε : ι → Bool) :
    rSign (flipSign i ε) i = -rSign ε i := by
  cases h : ε i <;> simp [flipSign, rSign, h]

@[simp] theorem rSign_flip_ne (i j : ι) (h : j ≠ i)
    (ε : ι → Bool) : rSign (flipSign i ε) j = rSign ε j := by
  simp [flipSign, rSign, h]

/-- An odd occurrence of a sign kills its mean, by an actual permutation. -/
theorem finiteMean_zero_of_flip (i : ι)
    (f : (ι → Bool) → ℝ) (hf : ∀ ε, f (flipSign i ε) = -f ε) :
    finiteMean f = 0 := by
  have he := finiteMean_equiv (flipSignEquiv i) f
  change finiteMean (fun ε ↦ f (flipSign i ε)) = finiteMean f at he
  rw [finiteMean_congr hf, finiteMean_neg] at he
  linarith

/-- Exact covariance, with no restriction on the universe of the index type. -/
theorem finiteMean_sign_two (i j : ι) :
    finiteMean (fun ε : ι → Bool ↦ rSign ε i * rSign ε j) =
      if i = j then (1 : ℝ) else 0 := by
  classical
  by_cases h : i = j
  · subst j
    simp
  · rw [if_neg h]
    apply finiteMean_zero_of_flip i
    intro ε
    simp [rSign_flip_ne i j (Ne.symm h)]

/-- Real Kronecker coefficient, used only inside finite sums. -/
def rDelta (i j : ι) : ℝ := if i = j then 1 else 0

/-- The all-equal case contributes one, not three. -/
theorem finiteMean_sign_four (i j k l : ι) :
    finiteMean (fun ε : ι → Bool ↦ rSign ε i * rSign ε j * rSign ε k * rSign ε l) =
      rDelta i j * rDelta k l + rDelta i k * rDelta j l +
      rDelta i l * rDelta j k - 2 * rDelta i j * rDelta i k * rDelta i l := by
  by_cases hij : i = j
  · subst j
    have he : ∀ ε : ι → Bool,
        rSign ε i * rSign ε i * rSign ε k * rSign ε l = rSign ε k * rSign ε l := by
      intro ε; rw [rSign_mul_self, one_mul]
    rw [finiteMean_congr he, finiteMean_sign_two]
    by_cases hik : i = k <;> by_cases hil : i = l <;> by_cases hkl : k = l <;>
      simp_all [rDelta] <;> norm_num
  · by_cases hik : i = k
    · subst k
      have he : ∀ ε : ι → Bool,
          rSign ε i * rSign ε j * rSign ε i * rSign ε l = rSign ε j * rSign ε l := by
        intro ε
        calc
          _ = (rSign ε i * rSign ε i) * (rSign ε j * rSign ε l) := by ring
          _ = _ := by rw [rSign_mul_self, one_mul]
      rw [finiteMean_congr he, finiteMean_sign_two]
      by_cases hil : i = l <;> by_cases hjl : j = l <;> simp_all [rDelta]
    · by_cases hil : i = l
      · subst l
        have he : ∀ ε : ι → Bool,
            rSign ε i * rSign ε j * rSign ε k * rSign ε i = rSign ε j * rSign ε k := by
          intro ε
          calc
            _ = (rSign ε i * rSign ε i) * (rSign ε j * rSign ε k) := by ring
            _ = _ := by rw [rSign_mul_self, one_mul]
        rw [finiteMean_congr he, finiteMean_sign_two]
        by_cases hjk : j = k <;> simp_all [rDelta]
      · have hz : finiteMean (fun ε : ι → Bool ↦
            rSign ε i * rSign ε j * rSign ε k * rSign ε l) = 0 := by
          apply finiteMean_zero_of_flip i
          intro ε
          simp [rSign_flip_ne i j (Ne.symm hij), rSign_flip_ne i k (Ne.symm hik),
            rSign_flip_ne i l (Ne.symm hil)]
        rw [hz]
        simp [rDelta, hij, hik, hil]

section Algebra
variable {A : Type v} [Ring A] [Algebra ℝ A]

/-- A finite selfadjoint family will later be substituted here. -/
def rademacherSum (a : ι → A) (ε : ι → Bool) : A := ∑ i, rSign ε i • a i

/-- Square budget of a selfadjoint family; positivity is proved separately. -/
def squareBudget (a : ι → A) : A := ∑ i, a i ^ 2

/-- Ordered words are kept in their original order in every expansion. -/
theorem rademacherSum_fourth_expand (a : ι → A) (ε : ι → Bool) :
    rademacherSum a ε ^ 4 = ∑ i, ∑ j, ∑ k, ∑ l,
      (rSign ε i * rSign ε j * rSign ε k * rSign ε l) •
        (a i * a j * a k * a l) := by
  simp only [rademacherSum, pow_succ, pow_zero, mul_one, Finset.sum_mul,
    Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul,
    Finset.smul_sum, mul_assoc]
  conv_lhs => enter [2, i, 2, j]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, i, 2, j]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i, 2, j]; rw [Finset.sum_comm]
  simp only [one_mul]
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem finiteMean_rademacher_sq (a : ι → A) :
    finiteMean (fun ε : ι → Bool ↦ rademacherSum a ε ^ 2) = squareBudget a := by
  classical
  have he : ∀ ε : ι → Bool, rademacherSum a ε ^ 2 =
      ∑ i, ∑ j, (rSign ε i * rSign ε j) • (a i * a j) := by
    intro ε
    simp only [rademacherSum, pow_two, Finset.sum_mul, Finset.mul_sum,
      smul_mul_assoc, mul_smul_comm, smul_smul, Finset.smul_sum]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [finiteMean_congr he]
  simp_rw [finiteMean_sum, finiteMean_smul_const, finiteMean_sign_two]
  simp [squareBudget, ite_smul, pow_two]

/-- Wick expansion over the finite sign cube, including the diagonal correction. -/
theorem finiteMean_rademacher_fourth (a : ι → A) :
    finiteMean (fun ε : ι → Bool ↦ rademacherSum a ε ^ 4) =
      squareBudget a ^ 2 + (∑ i, a i * squareBudget a * a i) +
      (∑ i, ∑ j, a i * a j * a i * a j) - (2 : ℝ) • ∑ i, a i ^ 4 := by
  classical
  rw [finiteMean_congr (rademacherSum_fourth_expand a)]
  simp_rw [finiteMean_sum, finiteMean_smul_const, finiteMean_sign_four]
  have hpairs : (∑ i, ∑ j, ∑ k, ∑ l,
        (rDelta i j * rDelta k l + rDelta i k * rDelta j l +
          rDelta i l * rDelta j k - 2 * rDelta i j * rDelta i k * rDelta i l) •
          (a i * a j * a k * a l)) =
      (∑ i, ∑ k, a i * a i * a k * a k) +
      (∑ i, ∑ j, a i * a j * a i * a j) +
      (∑ i, ∑ j, a i * a j * a j * a i) - (2 : ℝ) • ∑ i, a i ^ 4 := by
    simp only [add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp [rDelta, mul_ite, ite_mul, ite_smul, Finset.smul_sum, smul_smul,
      pow_succ, mul_assoc]
  rw [hpairs]
  have hP : (∑ i, ∑ k, a i * a i * a k * a k) = squareBudget a ^ 2 := by
    simp only [squareBudget, pow_two, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  have hS : (∑ i, ∑ j, a i * a j * a j * a i) =
      ∑ i, a i * squareBudget a * a i := by
    simp only [squareBudget, pow_two, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [hP, hS]
  abel

end Algebra

section Bilinear
variable {A : Type v} {D : Type w}
variable [NormedAddCommGroup A] [NormedSpace ℂ A]
variable [NormedAddCommGroup D] [NormedSpace ℂ D]

/-- A module-only signed sum for arbitrary complex normed spaces. -/
def signedSum (a : ι → A) (ε : ι → Bool) : A := ∑ i, rSign ε i • a i

/-- Covariance recovers the diagonal bilinear sum, not its sum of norms. -/
theorem finiteMean_bilinear_signedSum (V : A →L[ℂ] D →L[ℂ] ℂ)
    (a : ι → A) (b : ι → D) :
    finiteMean (fun ε : ι → Bool ↦ V (signedSum a ε) (signedSum b ε)) =
      ∑ i, V (a i) (b i) := by
  classical
  have he : ∀ ε : ι → Bool, V (signedSum a ε) (signedSum b ε) =
      ∑ i, ∑ j, (rSign ε i * rSign ε j) • V (a i) (b j) := by
    intro ε
    simp only [signedSum, map_sum, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.map_smul_of_tower, ContinuousLinearMap.smul_apply, smul_smul]
    rw [Finset.sum_comm]
  rw [finiteMean_congr he]
  simp_rw [finiteMean_sum, finiteMean_smul_const, finiteMean_sign_two]
  simp [ite_smul]

end Bilinear
end MathlibAnnex.CStarBilinear.Analytic
