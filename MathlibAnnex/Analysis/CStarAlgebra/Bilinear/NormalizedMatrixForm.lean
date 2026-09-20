import MathlibAnnex.Analysis.CStarAlgebra.Matrix.CornerMaps
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Actual normalization of an attained bilinear form

A norm-attaining pair of contractions is replaced by two actual unitaries
in two-by-two C*-matrix algebras.  Left multiplication moves the unitary
pair to (1,1).  The normalized form has norm one and value one at (1,1).
Explicit linear inputs recover the original form, preserving both finite
row-square and column-square norms.  No estimate for normalized forms is
assumed or claimed here.

Controller source C01; not compiled.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MathlibAnnex.NormalizedBilinear
open MatrixContraction

universe u v
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {D : Type v} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

/-- Corner compression after unitary changes of variables. -/
def twistedCorner (B : A →L[ℂ] D →L[ℂ] ℂ)
    (U : unitary (TwoByTwo A)) (V : unitary (TwoByTwo D)) :
    TwoByTwo A →L[ℂ] TwoByTwo D →L[ℂ] ℂ :=
  (LinearMap.mk₂ ℂ
    (fun M N => B (entryMap ((U : TwoByTwo A) * M)) (entryMap ((V : TwoByTwo D) * N)))
    (by intro M N P; simp only [mul_add, map_add, ContinuousLinearMap.add_apply])
    (by intro z M N; simp only [mul_smul_comm, map_smul, ContinuousLinearMap.smul_apply])
    (by intro M N P; simp only [mul_add, map_add])
    (by intro z M N; simp only [mul_smul_comm, map_smul])).mkContinuous₂ ‖B‖ (by
      intro M N
      calc
        ‖B (entryMap ((U : TwoByTwo A) * M)) (entryMap ((V : TwoByTwo D) * N))‖ ≤
            ‖B‖ * ‖entryMap ((U : TwoByTwo A) * M)‖ * ‖entryMap ((V : TwoByTwo D) * N)‖ := by
          exact ((B _).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _))
        _ ≤ ‖B‖ * ‖(U : TwoByTwo A) * M‖ * ‖(V : TwoByTwo D) * N‖ := by
          gcongr <;> exact entryMap_norm_le _
        _ = ‖B‖ * ‖M‖ * ‖N‖ := by
          rw [CStarRing.norm_coe_unitary_mul, CStarRing.norm_coe_unitary_mul])

@[simp]
theorem twistedCorner_apply (B : A →L[ℂ] D →L[ℂ] ℂ)
    (U : unitary (TwoByTwo A)) (V : unitary (TwoByTwo D)) (M : TwoByTwo A) (N : TwoByTwo D) :
    twistedCorner B U V M N =
      B (entryMap ((U : TwoByTwo A) * M)) (entryMap ((V : TwoByTwo D) * N)) := rfl

theorem norm_twistedCorner_le (B : A →L[ℂ] D →L[ℂ] ℂ)
    (U : unitary (TwoByTwo A)) (V : unitary (TwoByTwo D)) : ‖twistedCorner B U V‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
  intro M
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg B) (norm_nonneg M))
  intro N
  calc
    ‖twistedCorner B U V M N‖ ≤
        ‖B‖ * ‖entryMap ((U : TwoByTwo A) * M)‖ * ‖entryMap ((V : TwoByTwo D) * N)‖ := by
      exact ((B _).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _))
    _ ≤ ‖B‖ * ‖(U : TwoByTwo A) * M‖ * ‖(V : TwoByTwo D) * N‖ := by
      gcongr <;> exact entryMap_norm_le _
    _ = ‖B‖ * ‖M‖ * ‖N‖ := by
      rw [CStarRing.norm_coe_unitary_mul, CStarRing.norm_coe_unitary_mul]

@[simp]
theorem twistedCorner_recovery (B : A →L[ℂ] D →L[ℂ] ℂ)
    (U : unitary (TwoByTwo A)) (V : unitary (TwoByTwo D)) (a : A) (d : D) :
    twistedCorner B U V (unitaryInput U a) (unitaryInput V d) = B a d := by
  simp only [twistedCorner_apply, recover_unitaryInput]

/-- The two actual dilations preserve the attained scalar. -/
theorem twistedCorner_one (B : A →L[ℂ] D →L[ℂ] ℂ)
    (a : A) (d : D) (ha : ‖a‖ ≤ 1) (hd : ‖d‖ ≤ 1) :
    twistedCorner B (unitaryDilation a ha) (unitaryDilation d hd) 1 1 = B a d := by
  simp [twistedCorner_apply]

section Nontrivial
variable [Nontrivial A] [Nontrivial D]

/-- Attainment proves exact equality of the two bilinear norms. -/
theorem norm_twistedCorner_of_attains (B : A →L[ℂ] D →L[ℂ] ℂ)
    (a : A) (d : D) (ha : ‖a‖ ≤ 1) (hd : ‖d‖ ≤ 1)
    (hattain : B a d = (‖B‖ : ℂ)) :
    ‖twistedCorner B (unitaryDilation a ha) (unitaryDilation d hd)‖ = ‖B‖ := by
  let W := twistedCorner B (unitaryDilation a ha) (unitaryDilation d hd)
  refine le_antisymm (norm_twistedCorner_le B _ _) ?_
  have h11 : W 1 1 = (‖B‖ : ℂ) := (twistedCorner_one B a d ha hd).trans hattain
  calc
    ‖B‖ = ‖W 1 1‖ := by rw [h11]; simp [abs_of_nonneg (norm_nonneg B)]
    _ ≤ ‖W 1‖ * ‖(1 : TwoByTwo D)‖ := (W 1).le_opNorm _
    _ ≤ (‖W‖ * ‖(1 : TwoByTwo A)‖) * ‖(1 : TwoByTwo D)‖ :=
      mul_le_mul_of_nonneg_right (W.le_opNorm _) (norm_nonneg _)
    _ = ‖W‖ := by simp

/-- Division by the norm is used only for a nonzero form. -/
def normalized (B : A →L[ℂ] D →L[ℂ] ℂ)
    (a : A) (d : D) (ha : ‖a‖ ≤ 1) (hd : ‖d‖ ≤ 1) :
    TwoByTwo A →L[ℂ] TwoByTwo D →L[ℂ] ℂ :=
  ((‖B‖ : ℂ)⁻¹) • twistedCorner B (unitaryDilation a ha) (unitaryDilation d hd)

theorem normalized_one (B : A →L[ℂ] D →L[ℂ] ℂ) (hB : B ≠ 0)
    (a : A) (d : D) (ha : ‖a‖ ≤ 1) (hd : ‖d‖ ≤ 1)
    (hattain : B a d = (‖B‖ : ℂ)) : normalized B a d ha hd 1 1 = 1 := by
  have hnR : ‖B‖ ≠ 0 := by
    intro hz
    exact hB ((ContinuousLinearMap.opNorm_zero_iff B).mp hz)
  have hn : (‖B‖ : ℂ) ≠ 0 := by exact_mod_cast hnR
  simp [normalized, twistedCorner_one, hattain, hn]

theorem norm_normalized (B : A →L[ℂ] D →L[ℂ] ℂ) (hB : B ≠ 0)
    (a : A) (d : D) (ha : ‖a‖ ≤ 1) (hd : ‖d‖ ≤ 1)
    (hattain : B a d = (‖B‖ : ℂ)) : ‖normalized B a d ha hd‖ = 1 := by
  have hnR : ‖B‖ ≠ 0 := by
    intro hz
    exact hB ((ContinuousLinearMap.opNorm_zero_iff B).mp hz)
  have hUpper : ‖normalized B a d ha hd‖ ≤ 1 := by
    unfold normalized
    calc
      ‖(‖B‖ : ℂ)⁻¹ • twistedCorner B (unitaryDilation a ha) (unitaryDilation d hd)‖ ≤
          ‖(‖B‖ : ℂ)⁻¹‖ *
            ‖twistedCorner B (unitaryDilation a ha) (unitaryDilation d hd)‖ :=
        (twistedCorner B (unitaryDilation a ha) (unitaryDilation d hd)).opNorm_smul_le _
      _ = 1 := by
        rw [norm_twistedCorner_of_attains B a d ha hd hattain]
        simp [abs_of_nonneg (norm_nonneg B), hnR]
  have hLower : 1 ≤ ‖normalized B a d ha hd‖ := by
    let W := normalized B a d ha hd
    have h11 : W 1 1 = 1 := normalized_one B hB a d ha hd hattain
    calc
      1 = ‖W 1 1‖ := by rw [h11]; norm_num
      _ ≤ ‖W 1‖ * ‖(1 : TwoByTwo D)‖ := (W 1).le_opNorm _
      _ ≤ (‖W‖ * ‖(1 : TwoByTwo A)‖) * ‖(1 : TwoByTwo D)‖ :=
        mul_le_mul_of_nonneg_right (W.le_opNorm _) (norm_nonneg _)
      _ = ‖W‖ := by simp
  exact le_antisymm hUpper hLower

theorem normalized_recovery (B : A →L[ℂ] D →L[ℂ] ℂ) (hB : B ≠ 0)
    (a : A) (d : D) (ha : ‖a‖ ≤ 1) (hd : ‖d‖ ≤ 1) (x : A) (y : D) :
    (‖B‖ : ℂ) * normalized B a d ha hd
      (unitaryInput (unitaryDilation a ha) x)
      (unitaryInput (unitaryDilation d hd) y) = B x y := by
  have hnR : ‖B‖ ≠ 0 := by
    intro hz
    exact hB ((ContinuousLinearMap.opNorm_zero_iff B).mp hz)
  have hn : (‖B‖ : ℂ) ≠ 0 := by exact_mod_cast hnR
  simp [normalized, twistedCorner_recovery, smul_eq_mul, ← mul_assoc, hn]

/-- All four square-sum norms survive the change of variables. -/
theorem normalized_inputs_preserve_squares {ι : Type*} (s : Finset ι)
    (a : A) (d : D) (ha : ‖a‖ ≤ 1) (hd : ‖d‖ ≤ 1)
    (x : ι → A) (y : ι → D) :
    (‖∑ i ∈ s, star (unitaryInput (unitaryDilation a ha) (x i)) *
        unitaryInput (unitaryDilation a ha) (x i)‖ = ‖∑ i ∈ s, star (x i) * x i‖) ∧
    (‖∑ i ∈ s, unitaryInput (unitaryDilation a ha) (x i) *
        star (unitaryInput (unitaryDilation a ha) (x i))‖ = ‖∑ i ∈ s, x i * star (x i)‖) ∧
    (‖∑ i ∈ s, star (unitaryInput (unitaryDilation d hd) (y i)) *
        unitaryInput (unitaryDilation d hd) (y i)‖ = ‖∑ i ∈ s, star (y i) * y i‖) ∧
    (‖∑ i ∈ s, unitaryInput (unitaryDilation d hd) (y i) *
        star (unitaryInput (unitaryDilation d hd) (y i))‖ = ‖∑ i ∈ s, y i * star (y i)‖) :=
  ⟨norm_sum_star_unitaryInput s _ x, norm_sum_unitaryInput_star s _ x,
    norm_sum_star_unitaryInput s _ y, norm_sum_unitaryInput_star s _ y⟩

end Nontrivial
end MathlibAnnex.NormalizedBilinear
