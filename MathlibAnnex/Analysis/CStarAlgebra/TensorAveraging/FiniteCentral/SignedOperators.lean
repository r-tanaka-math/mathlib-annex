import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteCentral.BasisOperators
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteCentral.SignedPermutations

/-!
# Signed permutation operators on one finite coordinate corner

C06, UNBUILT. The action is identity outside the finite corner. A Hilbert-sum
extension, its multiplication law and BOTH unitary identities are proved;
no matrix norm is silently substituted for the operator norm.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical
open scoped InnerProductSpace ComplexConjugate
namespace MathlibAnnex.FiniteCentral
universe v w
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {ι : Type w}
variable (b : HilbertBasis ι ℂ H) (s : Finset ι)

def labelVector (q : s × Bool) : H := signScalar q.2 • b q.1.val

@[simp] theorem labelVector_flip (q : s × Bool) :
    labelVector b s (flipLabel q) = -labelVector b s q := by
  simp [labelVector, flipLabel, signScalar_flip, neg_smul]

/-- A group element sends every signed label by the same linear rule. -/
theorem labelVector_signed_apply (g : SignedPermutation s) (q : s × Bool) :
    labelVector b s (g.val q) = signScalar q.2 •
      labelVector b s (g.val (q.1, false)) := by
  rcases q with ⟨i,t⟩
  cases t
  · simp
  · rw [signed_apply_true, labelVector_flip]
    simp

def signedBasisImage (g : SignedPermutation s) (i : ι) : H :=
  if hi : i ∈ s then labelVector b s (g.val (⟨i,hi⟩,false)) else b i

@[simp] theorem signedBasisImage_on (g : SignedPermutation s) (i : s) :
    signedBasisImage b s g i.val = labelVector b s (g.val (i,false)) := by
  simp [signedBasisImage, i.property]

@[simp] theorem signedBasisImage_off (g : SignedPermutation s) (i : ι) (hi : i ∉ s) :
    signedBasisImage b s g i = b i := by simp [signedBasisImage, hi]

/-- Orthonormality uses injectivity of the underlying coordinate permutation,
not injectivity of the signed labels alone. -/
theorem orthonormal_signedBasisImage (g : SignedPermutation s) :
    Orthonormal ℂ (signedBasisImage b s g) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hi : i ∈ s
  · by_cases hj : j ∈ s
    · by_cases hij : i = j
      · subst j
        simp [signedBasisImage, hi, labelVector, norm_smul,
          b.orthonormal.norm_eq_one]
      · have hne : (g.val (⟨i,hi⟩,false)).1.val ≠ (g.val (⟨j,hj⟩,false)).1.val := by
          intro he
          have he' := signed_first_injective g (Subtype.ext he)
          exact hij (congrArg Subtype.val he')
        simp [signedBasisImage, hi, hj, labelVector, inner_smul_left,
          inner_smul_right, basis_inner, hne, hij]
    · have hne : (g.val (⟨i,hi⟩,false)).1.val ≠ j := by
        intro h; apply hj; rw [← h]; exact (g.val (⟨i,hi⟩,false)).1.property
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      simp [signedBasisImage, hi, hj, labelVector, inner_smul_left,
        basis_inner, hne, hij]
  · by_cases hj : j ∈ s
    · have hne : i ≠ (g.val (⟨j,hj⟩,false)).1.val := by
        intro h; apply hi; rw [h]; exact (g.val (⟨j,hj⟩,false)).1.property
      have hij : i ≠ j := fun h => hi (h.symm ▸ hj)
      simp [signedBasisImage, hi, hj, labelVector, inner_smul_right,
        basis_inner, hne, hij]
    · simp [signedBasisImage, hi, hj, basis_inner]

def signedOperator (g : SignedPermutation s) : H →L[ℂ] H :=
  (basisIsometry b (signedBasisImage b s g) (orthonormal_signedBasisImage b s g)).toContinuousLinearMap

@[simp] theorem signedOperator_basis (g : SignedPermutation s) (i : ι) :
    signedOperator b s g (b i) = signedBasisImage b s g i :=
  basisIsometry_basis b (signedBasisImage b s g)
    (orthonormal_signedBasisImage b s g) i

@[simp] theorem signedOperator_basis_on (g : SignedPermutation s) (i : s) :
    signedOperator b s g (b i.val) = labelVector b s (g.val (i,false)) := by
  simp only [signedOperator_basis, signedBasisImage_on]

@[simp] theorem signedOperator_basis_off (g : SignedPermutation s) (i : ι) (hi : i ∉ s) :
    signedOperator b s g (b i) = b i := by
  simp only [signedOperator_basis, signedBasisImage_off b s g i hi]

@[simp] theorem signedOperator_label (g : SignedPermutation s) (q : s × Bool) :
    signedOperator b s g (labelVector b s q) = labelVector b s (g.val q) := by
  calc
    signedOperator b s g (labelVector b s q) =
        signScalar q.2 • signedOperator b s g (b q.1.val) := by
          rw [labelVector, map_smul]
    _ = signScalar q.2 • labelVector b s (g.val (q.1, false)) := by
      rw [signedOperator_basis_on]
    _ = labelVector b s (g.val q) := (labelVector_signed_apply b s g q).symm

@[simp] theorem signedOperator_one : signedOperator b s 1 = 1 := by
  apply operator_ext_basis b
  intro i
  classical
  by_cases hi : i ∈ s <;> simp [signedOperator_basis, signedBasisImage, hi, labelVector]

/-- Multiplication order is function composition, hence right translation in
FiniteGroupBalance is the required direction. -/
theorem signedOperator_mul (g h : SignedPermutation s) :
    signedOperator b s (g * h) = signedOperator b s g * signedOperator b s h := by
  apply operator_ext_basis b
  intro i
  classical
  by_cases hi : i ∈ s
  · have he : i = (⟨i,hi⟩ : s).val := rfl
    rw [he, ContinuousLinearMap.mul_apply]
    rw [signedOperator_basis_on b s (g * h) ⟨i, hi⟩]
    rw [signedOperator_basis_on b s h ⟨i, hi⟩]
    rw [signedOperator_label]
    rfl
  · simp [ContinuousLinearMap.mul_apply, signedOperator_basis_off, hi]

theorem signedOperator_star_mul (g : SignedPermutation s) :
    star (signedOperator b s g) * signedOperator b s g = 1 :=
  star_mul_of_linearIsometry _

theorem signedOperator_mul_star (g : SignedPermutation s) :
    signedOperator b s g * star (signedOperator b s g) = 1 := by
  have hinv : signedOperator b s g * signedOperator b s g⁻¹ = 1 := by
    rw [← signedOperator_mul, mul_inv_cancel, signedOperator_one]
  have heq : star (signedOperator b s g) = signedOperator b s g⁻¹ := by
    calc
      _ = star (signedOperator b s g) *
          (signedOperator b s g * signedOperator b s g⁻¹) := by rw [hinv, mul_one]
      _ = signedOperator b s g⁻¹ := by
        rw [← mul_assoc, signedOperator_star_mul, one_mul]
  rw [heq]
  exact hinv

def signedUnitary (g : SignedPermutation s) : unitary (H →L[ℂ] H) :=
  ⟨signedOperator b s g, signedOperator_star_mul b s g, signedOperator_mul_star b s g⟩

end MathlibAnnex.FiniteCentral
