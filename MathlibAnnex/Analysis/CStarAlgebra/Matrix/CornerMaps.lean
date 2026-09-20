import MathlibAnnex.Analysis.CStarAlgebra.Matrix.UnitaryDilation

/-!
# Exact two-by-two corner embeddings and unitary changes of variables

Both row and column norms of a finite family are preserved.  These are
norm equalities for the true C*-matrix norm, not entrywise estimates.
Controller C01: proof source, uncompiled.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MathlibAnnex.MatrixContraction

universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem norm_diagonalHom (a b : A) : ‖diagonalHom (a,b)‖ = max ‖a‖ ‖b‖ := by
  apply le_antisymm
  · simpa [Prod.norm_def] using NonUnitalStarAlgHom.norm_apply_le (diagonalHom (A := A)).toNonUnitalStarAlgHom (a,b)
  · exact max_le (CStarMatrix.norm_entry_le_norm (M := diagonalHom (a,b)) (i := 0) (j := 0))
      (CStarMatrix.norm_entry_le_norm (M := diagonalHom (a,b)) (i := 1) (j := 1))

/-- Upper-right corner, with zero other entries; linear in a. -/
def corner (a : A) : TwoByTwo A :=
  CStarMatrix.ofMatrix (fun i j => if i = 0 ∧ j = 1 then a else 0)

@[simp] theorem corner_00 (a : A) : corner a 0 0 = 0 := rfl
@[simp] theorem corner_01 (a : A) : corner a 0 1 = a := rfl
@[simp] theorem corner_10 (a : A) : corner a 1 0 = 0 := rfl
@[simp] theorem corner_11 (a : A) : corner a 1 1 = 0 := rfl

@[simp] theorem corner_add (a b : A) : corner (a+b) = corner a + corner b := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

@[simp] theorem corner_smul (c : ℂ) (a : A) : corner (c • a) = c • corner a := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem star_corner_mul (a b : A) :
    star (corner a) * corner b = diagonalHom (0, star a * b) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [CStarMatrix.star_apply, CStarMatrix.mul_apply, Fin.sum_univ_two]

theorem corner_mul_star (a b : A) :
    corner a * star (corner b) = diagonalHom (a * star b, 0) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [CStarMatrix.star_apply, CStarMatrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem norm_corner (a : A) : ‖corner a‖ = ‖a‖ := by
  have hs : ‖corner a‖ * ‖corner a‖ = ‖a‖ * ‖a‖ := by
    rw [← CStarRing.norm_star_mul_self, star_corner_mul, norm_diagonalHom]
    simp [CStarRing.norm_star_mul_self] <;> positivity
  exact (mul_self_inj_of_nonneg (norm_nonneg (corner a)) (norm_nonneg a)).mp hs

def cornerMap : A →L[ℂ] TwoByTwo A :=
  LinearMap.mkContinuous
    ({ toFun := corner, map_add' := corner_add, map_smul' := corner_smul } : A →ₗ[ℂ] TwoByTwo A)
    1 (by intro a; simp)

@[simp] theorem cornerMap_apply (a : A) : cornerMap a = corner a := rfl

def entryMap : TwoByTwo A →L[ℂ] A :=
  LinearMap.mkContinuous
    ({ toFun := fun M => M 0 1
       map_add' := by intro M N; rfl
       map_smul' := by intro c M; rfl } : TwoByTwo A →ₗ[ℂ] A)
    1 (by intro M; simpa using CStarMatrix.norm_entry_le_norm (M := M) (i := 0) (j := 1))

@[simp] theorem entryMap_apply (M : TwoByTwo A) : entryMap M = M 0 1 := rfl
@[simp] theorem entryMap_corner (a : A) : entryMap (corner a) = a := rfl

theorem entryMap_norm_le (M : TwoByTwo A) : ‖entryMap M‖ ≤ ‖M‖ :=
  by simpa only [entryMap_apply] using
    (CStarMatrix.norm_entry_le_norm (M := M) (i := 0) (j := 1))

/-- Input correction for the normalized form x ↦ V(Ux,Vy). -/
def unitaryInput (U : unitary (TwoByTwo A)) : A →L[ℂ] TwoByTwo A :=
  (ContinuousLinearMap.mul ℂ (TwoByTwo A) (star (U : TwoByTwo A))).comp cornerMap

@[simp] theorem unitaryInput_apply (U : unitary (TwoByTwo A)) (a : A) :
    unitaryInput U a = star (U : TwoByTwo A) * corner a := rfl

@[simp] theorem norm_unitaryInput (U : unitary (TwoByTwo A)) (a : A) :
    ‖unitaryInput U a‖ = ‖a‖ := by
  change ‖((star U : unitary (TwoByTwo A)) : TwoByTwo A) * corner a‖ = _
  rw [CStarRing.norm_coe_unitary_mul, norm_corner]

@[simp] theorem recover_unitaryInput (U : unitary (TwoByTwo A)) (a : A) :
    entryMap ((U : TwoByTwo A) * unitaryInput U a) = a := by
  simp [unitaryInput_apply, ← mul_assoc, Unitary.coe_mul_star_self]

theorem unitaryInput_star_mul (U : unitary (TwoByTwo A)) (a b : A) :
    star (unitaryInput U a) * unitaryInput U b = diagonalHom (0, star a * b) := by
  simp only [unitaryInput_apply, star_mul, star_star]
  calc
    (star (corner a) * (U : TwoByTwo A)) * (star (U : TwoByTwo A) * corner b) =
        star (corner a) * ((U : TwoByTwo A) * star (U : TwoByTwo A)) * corner b := by noncomm_ring
    _ = diagonalHom (0, star a * b) := by simp [Unitary.coe_mul_star_self, star_corner_mul]

theorem unitaryInput_mul_star (U : unitary (TwoByTwo A)) (a b : A) :
    unitaryInput U a * star (unitaryInput U b) =
      star (U : TwoByTwo A) * diagonalHom (a * star b, 0) * (U : TwoByTwo A) := by
  simp only [unitaryInput_apply, star_mul, star_star]
  rw [← corner_mul_star]
  noncomm_ring

/-- Right square sums are unchanged in norm. -/
theorem norm_sum_star_unitaryInput {ι : Type*} (s : Finset ι)
    (U : unitary (TwoByTwo A)) (a : ι → A) :
    ‖∑ i ∈ s, star (unitaryInput U (a i)) * unitaryInput U (a i)‖ =
      ‖∑ i ∈ s, star (a i) * a i‖ := by
  have hsum : (∑ i ∈ s, diagonalHom (0, star (a i) * a i)) =
      diagonalHom (0, ∑ i ∈ s, star (a i) * a i) := by
    rw [← map_sum]
    congr 1
    ext <;> simp [Prod.fst_sum, Prod.snd_sum]
  simp_rw [unitaryInput_star_mul]
  rw [hsum, norm_diagonalHom]
  simp

/-- Left square sums are unitarily conjugated; their norm is unchanged. -/
theorem norm_sum_unitaryInput_star {ι : Type*} (s : Finset ι)
    (U : unitary (TwoByTwo A)) (a : ι → A) :
    ‖∑ i ∈ s, unitaryInput U (a i) * star (unitaryInput U (a i))‖ =
      ‖∑ i ∈ s, a i * star (a i)‖ := by
  have hsum : (∑ i ∈ s, diagonalHom (a i * star (a i), 0)) =
      diagonalHom (∑ i ∈ s, a i * star (a i), 0) := by
    rw [← map_sum]
    congr 1
    ext <;> simp [Prod.fst_sum, Prod.snd_sum]
  simp_rw [unitaryInput_mul_star]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hsum]
  rw [CStarRing.norm_mul_coe_unitary]
  change ‖((star U : unitary (TwoByTwo A)) : TwoByTwo A) * _‖ = _
  rw [CStarRing.norm_coe_unitary_mul, norm_diagonalHom]
  simp

end MathlibAnnex.MatrixContraction
