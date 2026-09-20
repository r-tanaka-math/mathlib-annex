import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Analytic.ComplexFamilies
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.NormalizedSequenceForm

/-!
# A row/column estimate for every bounded complex C*-bilinear form

The constant 146*||B|| is fixed before every finite family.  The same C01
leftInput/rightInput maps recover B and preserve all four square-norm
budgets.  Normalization is only invoked in the nonzero/nontrivial branch.
No weak compactness, regularity, domination or factorization is assumed.
SOURCE_UNBUILT.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Finset

namespace MathlibAnnex.CStarBilinear
open MathlibAnnex.CStarBilinear.Analytic
open MathlibAnnex.NormalizedSequenceBilinear
open MathlibAnnex.MatrixContraction

universe uA uD
local instance universalSequenceOrder (X : Type*) [CStarAlgebra X] :
    PartialOrder (BoundedContinuousFunction ℕ X) :=
  CStarAlgebra.spectralOrder _
local instance universalSequenceStarOrder (X : Type*) [CStarAlgebra X] :
    StarOrderedRing (BoundedContinuousFunction ℕ X) :=
  CStarAlgebra.spectralOrderedRing _
local instance universalSequenceNontrivial (X : Type*) [CStarAlgebra X] [Nontrivial X] :
    Nontrivial (BoundedContinuousFunction ℕ X) := by
  refine ⟨constants X 0, constants X 1, ?_⟩
  intro h
  exact zero_ne_one (congrArg (fun f : BoundedContinuousFunction ℕ X => f 0) h)
local instance universalMatrixNontrivial (X : Type*) [CStarAlgebra X] [Nontrivial X] :
    Nontrivial (TwoByTwo (BoundedContinuousFunction ℕ X)) := by
  refine ⟨0, 1, ?_⟩
  intro h
  have h00 := congrArg
    (fun M : TwoByTwo (BoundedContinuousFunction ℕ X) => M 0 0) h
  exact (zero_ne_one : (0 : BoundedContinuousFunction ℕ X) ≠ 1) (by simpa using h00)

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

/-- Pullback uses the same linear maps for the entire form, not choices made
for one particular list.  The Finset helpers retain arbitrary index universes. -/
theorem hasFiniteRowColumnEstimate_nonzero [Nontrivial A] [Nontrivial D]
    (B : A →L[ℂ] D →L[ℂ] ℂ) (hB : B ≠ 0) :
    HasFiniteRowColumnEstimate B (146 * ‖B‖) := by
  intro ι _ _ x y
  let L := leftInput B
  let R := rightInput B
  have h := normalized_complex_family_le (model B) (model_norm B hB).le (model_one B hB)
    (fun i ↦ L (x i)) (fun i ↦ R (y i))
  obtain ⟨hlc, hlr⟩ := leftInput_square_norms B Finset.univ x
  obtain ⟨hrc, hrr⟩ := rightInput_square_norms B Finset.univ y
  have hLc : ‖starMulSum (fun i ↦ L (x i))‖ = ‖starMulSum x‖ := hlc
  have hLr : ‖mulStarSum (fun i ↦ L (x i))‖ = ‖mulStarSum x‖ := hlr
  have hRc : ‖starMulSum (fun i ↦ R (y i))‖ = ‖starMulSum y‖ := hrc
  have hRr : ‖mulStarSum (fun i ↦ R (y i))‖ = ‖mulStarSum y‖ := hrr
  rw [hLc, hLr, hRc, hRr] at h
  have he : (∑ i, B (x i) (y i)) =
      (‖B‖ : ℂ) * ∑ i, model B (L (x i)) (R (y i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (model_recovery B hB (x i) (y i)).symm
  rw [he, norm_mul]
  have hs : ‖(‖B‖ : ℂ)‖ = ‖B‖ := by simp [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg B)]
  rw [hs]
  calc
    _ ≤ ‖B‖ * (73 * (‖starMulSum x‖ + ‖mulStarSum x‖ +
        ‖starMulSum y‖ + ‖mulStarSum y‖)) := mul_le_mul_of_nonneg_left h (norm_nonneg B)
    _ = (146 * ‖B‖ / 2) * (‖starMulSum x‖ + ‖mulStarSum x‖ +
        ‖starMulSum y‖ + ‖mulStarSum y‖) := by ring

/-- The explicit quantitative result includes zero forms and subsingleton
algebras without requesting a normalized state on a zero algebra. -/
theorem hasFiniteRowColumnEstimate_146_norm (B : A →L[ℂ] D →L[ℂ] ℂ) :
    HasFiniteRowColumnEstimate B (146 * ‖B‖) := by
  by_cases hB : B = 0
  · subst B
    simp
    intro x y
    positivity
  · rcases subsingleton_or_nontrivial A with hA | hA
    · letI : Subsingleton A := hA
      have hz : B = 0 := by
        ext a d
        have ha : a = 0 := Subsingleton.elim _ _
        simp [ha]
      exact (hB hz).elim
    · letI : Nontrivial A := hA
      rcases subsingleton_or_nontrivial D with hD | hD
      · letI : Subsingleton D := hD
        have hz : B = 0 := by
          ext a d
          have hd : d = 0 := Subsingleton.elim _ _
          simp [hd]
        exact (hB hz).elim
      · letI : Nontrivial D := hD
        exact hasFiniteRowColumnEstimate_nonzero B hB

/-- The assigned analytic supplier, now derived rather than assumed. -/
theorem exists_rowColumnEstimate (B : A →L[ℂ] D →L[ℂ] ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ HasFiniteRowColumnEstimate B C :=
  ⟨146 * ‖B‖, mul_nonneg (by norm_num) (norm_nonneg B),
    hasFiniteRowColumnEstimate_146_norm B⟩

end MathlibAnnex.CStarBilinear
