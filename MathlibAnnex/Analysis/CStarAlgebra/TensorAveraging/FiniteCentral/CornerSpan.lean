import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteCentral.SignedOperators
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteCentral.Compression

/-!
# The complex group span contains the full finite operator corner

C06, UNBUILT. Identity outside the corner cancels in a DIFFERENCE of group
operators. The matrix-unit formula works also for diagonal units and does
not claim that each individual group element has finite rank.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical
open scoped BigOperators InnerProductSpace
namespace MathlibAnnex.FiniteCentral
universe v w
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {ι : Type w}
variable (b : HilbertBasis ι ℂ H) (s : Finset ι)

/-- Sign reversal of one basis vector as an operator formula. -/
theorem signed_flip_operator (i : s) :
    signedOperator b s (flipCoordinate i) = 1 - (2 : ℂ) • matrixUnit b i.val i.val := by
  classical
  apply operator_ext_basis b
  intro k
  by_cases hk : k ∈ s
  · have hs : k = (⟨k,hk⟩ : s).val := rfl
    rw [hs, signedOperator_basis_on]
    by_cases hki : (⟨k,hk⟩ : s) = i
    · have hval : i.val = k := (congrArg Subtype.val hki).symm
      simp [labelVector, flipCoordinate_apply, hki,
        ContinuousLinearMap.sub_apply, matrixUnit_basis, hval,
        b.orthonormal.norm_eq_one, two_smul] <;> abel
    · have hval : k ≠ i.val := fun h => hki (Subtype.ext h)
      simp [labelVector, flipCoordinate_apply, hki,
        ContinuousLinearMap.sub_apply, matrixUnit_basis, Ne.symm hval]
  · have hki : i.val ≠ k := fun h => hk (h ▸ i.property)
    simp [signedOperator_basis_off b s _ k hk, matrixUnit_basis,
      ContinuousLinearMap.sub_apply, hki]

/-- Multiplying a diagonal matrix unit by a swap picks out the desired column. -/
theorem matrixUnit_mul_swap (i j : s) :
    matrixUnit b i.val i.val * signedOperator b s (unsignedPermutation (Equiv.swap i j)) =
      matrixUnit b i.val j.val := by
  classical
  apply operator_ext_basis b
  intro k
  by_cases hk : k ∈ s
  · rw [ContinuousLinearMap.mul_apply,
      show k = (⟨k,hk⟩ : s).val from rfl, signedOperator_basis_on]
    simp only [unsignedPermutation_apply, labelVector, signScalar_false, one_smul,
      matrixUnit_basis]
    have he : i.val = (Equiv.swap i j ⟨k,hk⟩).val ↔ j.val = k := by
      change i.val = (Equiv.swap i j ⟨k,hk⟩).val ↔ j.val = (⟨k,hk⟩ : s).val
      rw [Subtype.val_inj, Subtype.val_inj]
      constructor
      · intro h
        have hh := congrArg (Equiv.swap i j) h
        simpa using hh
      · rintro rfl
        simp
    simp only [he]
  · have hik : i.val ≠ k := fun h => hk (h ▸ i.property)
    have hjk : j.val ≠ k := fun h => hk (h ▸ j.property)
    simp [ContinuousLinearMap.mul_apply, signedOperator_basis_off, hk,
      matrixUnit_basis, hik, hjk]

/-- Actual linear-span membership, not a formal matrix identification. -/
theorem matrixUnit_mem_group_span (i j : s) :
    matrixUnit b i.val j.val ∈ Submodule.span ℂ (Set.range (signedOperator b s)) := by
  classical
  let v : SignedPermutation s := unsignedPermutation (Equiv.swap i j)
  let d : SignedPermutation s := flipCoordinate i
  have hv : signedOperator b s v ∈ Submodule.span ℂ (Set.range (signedOperator b s)) :=
    Submodule.subset_span ⟨v,rfl⟩
  have hdv : signedOperator b s (d*v) ∈ Submodule.span ℂ (Set.range (signedOperator b s)) :=
    Submodule.subset_span ⟨d*v,rfl⟩
  have heq : (1 / 2 : ℂ) • (signedOperator b s v - signedOperator b s (d*v)) =
      matrixUnit b i.val j.val := by
    rw [signedOperator_mul]
    change (1/2 : ℂ) • (signedOperator b s v -
      signedOperator b s (flipCoordinate i) * signedOperator b s v) = _
    rw [signed_flip_operator, sub_mul, one_mul, smul_mul_assoc, sub_sub_cancel]
    rw [show matrixUnit b i.val i.val * signedOperator b s v = matrixUnit b i.val j.val from
      matrixUnit_mul_swap b s i j]
    simp only [smul_smul]
    norm_num
  rw [← heq]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hv hdv)

/-- Every PaP belongs to the SAME finite group's complex span. -/
theorem compression_mem_group_span (T : H →L[ℂ] H) :
    compression b s T ∈ Submodule.span ℂ (Set.range (signedOperator b s)) := by
  classical
  rw [compression, compression_eq_matrix_sum]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.smul_mem _ _ (matrixUnit_mem_group_span b s ⟨i,hi⟩ ⟨j,hj⟩)

/-- A finite Hilbert basis gives projection 1, with no positive-dimension
assumption required for this identity. -/
theorem coordinateProjection_univ [Fintype ι] :
    coordinateProjection b (Finset.univ : Finset ι) = 1 := by
  apply operator_ext_basis b
  intro i
  simp

end MathlibAnnex.FiniteCentral
