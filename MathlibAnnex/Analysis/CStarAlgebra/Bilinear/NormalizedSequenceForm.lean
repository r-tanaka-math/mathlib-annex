import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.SequenceNormAttainment
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.NormalizedMatrixForm
import Mathlib.Util.Superscript

/-!
# Normalization of an arbitrary bounded C*-bilinear form

The construction is explicit at the level of classical choices already
provided by Hahn--Banach: extend to bounded sequences, select a maximizing
pair, dilate both contractions to unitaries, then twist and divide by the
nonzero norm.  The original form is recovered by linear maps which
preserve all four finite square-sum norms.

This is the normalization step, not the still-missing analytic estimate
for a norm-one form with V(1,1)=1.  No arbitrary-bilinear weak compactness
or invariant mean is asserted.  Source checkpoint C01, uncompiled.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MathlibAnnex.NormalizedSequenceBilinear
open MatrixContraction SequenceBilinear NormalizedBilinear

universe u v

/-- These order instances are local to this file.  They do not install a
new global order on a shared bidual or on arbitrary bounded functions. -/
local instance sequenceOrder (X : Type*) [CStarAlgebra X] : PartialOrder (BoundedContinuousFunction ℕ X) :=
  CStarAlgebra.spectralOrder _
local instance sequenceStarOrder (X : Type*) [CStarAlgebra X] : StarOrderedRing (BoundedContinuousFunction ℕ X) :=
  CStarAlgebra.spectralOrderedRing _

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]
variable {D : Type v} [CStarAlgebra D] [Nontrivial D]

def constants (X : Type*) [CStarAlgebra X] : X →⋆ₐ[ℂ] (BoundedContinuousFunction ℕ X) where
  toFun := BoundedContinuousFunction.const ℕ
  map_zero' := by ext; rfl
  map_one' := by ext; rfl
  map_add' _ _ := by ext; rfl
  map_mul' _ _ := by ext; rfl
  map_star' _ := by ext; rfl
  commutes' _ := by ext; rfl

@[simp] theorem constants_apply (X : Type*) [CStarAlgebra X] (a : X) (n : ℕ) :
    constants X a n = a := rfl

@[simp] theorem norm_constants (X : Type*) [CStarAlgebra X] (a : X) :
    ‖constants X a‖ = ‖a‖ := BoundedContinuousFunction.norm_const_eq a

local instance sequenceNontrivial (X : Type*) [CStarAlgebra X] [Nontrivial X] :
    Nontrivial (BoundedContinuousFunction ℕ X) := by
  refine ⟨constants X 0, constants X 1, ?_⟩
  intro h
  exact zero_ne_one (congrArg (fun f : BoundedContinuousFunction ℕ X => f 0) h)

def constantsCLM (X : Type*) [CStarAlgebra X] : X →L[ℂ] (BoundedContinuousFunction ℕ X) :=
  (constants X).toLinearMap.mkContinuous 1 (by intro a; simp)

@[simp] theorem constantsCLM_apply (X : Type*) [CStarAlgebra X] (a : X) :
    constantsCLM X a = constants X a := rfl

/-- Nonzero original forms have nonzero sequence extensions. -/
theorem sequenceExtension_ne_zero (B : A →L[ℂ] D →L[ℂ] ℂ) (hB : B ≠ 0) :
    sequenceExtension B ≠ 0 := by
  intro hz
  have hzero : ‖sequenceExtension B‖ = 0 :=
    (ContinuousLinearMap.opNorm_zero_iff (sequenceExtension B)).mpr hz
  have hBnorm : ‖B‖ = 0 := (norm_sequenceExtension B).symm.trans hzero
  exact hB ((ContinuousLinearMap.opNorm_zero_iff B).mp hBnorm)

def leftUnitary (B : A →L[ℂ] D →L[ℂ] ℂ) : unitary (TwoByTwo (BoundedContinuousFunction ℕ A)) :=
  unitaryDilation (attainingLeft B) (norm_attainingLeft_le B)

def rightUnitary (B : A →L[ℂ] D →L[ℂ] ℂ) : unitary (TwoByTwo (BoundedContinuousFunction ℕ D)) :=
  unitaryDilation (attainingRight B) (norm_attainingRight_le B)

def leftInput (B : A →L[ℂ] D →L[ℂ] ℂ) : A →L[ℂ] TwoByTwo (BoundedContinuousFunction ℕ A) :=
  (unitaryInput (leftUnitary B)).comp (constantsCLM A)

def rightInput (B : A →L[ℂ] D →L[ℂ] ℂ) : D →L[ℂ] TwoByTwo (BoundedContinuousFunction ℕ D) :=
  (unitaryInput (rightUnitary B)).comp (constantsCLM D)

@[simp] theorem leftInput_apply (B : A →L[ℂ] D →L[ℂ] ℂ) (a : A) :
    leftInput B a = unitaryInput (leftUnitary B) (constants A a) := rfl
@[simp] theorem rightInput_apply (B : A →L[ℂ] D →L[ℂ] ℂ) (d : D) :
    rightInput B d = unitaryInput (rightUnitary B) (constants D d) := rfl

@[simp] theorem norm_leftInput (B : A →L[ℂ] D →L[ℂ] ℂ) (a : A) :
    ‖leftInput B a‖ = ‖a‖ := by
  rw [leftInput_apply, norm_unitaryInput, norm_constants]
@[simp] theorem norm_rightInput (B : A →L[ℂ] D →L[ℂ] ℂ) (d : D) :
    ‖rightInput B d‖ = ‖d‖ := by
  rw [rightInput_apply, norm_unitaryInput, norm_constants]

def model (B : A →L[ℂ] D →L[ℂ] ℂ) :
    TwoByTwo (BoundedContinuousFunction ℕ A) →L[ℂ] TwoByTwo (BoundedContinuousFunction ℕ D) →L[ℂ] ℂ :=
  normalized (sequenceExtension B) (attainingLeft B) (attainingRight B)
    (norm_attainingLeft_le B) (norm_attainingRight_le B)

theorem extension_attains (B : A →L[ℂ] D →L[ℂ] ℂ) :
    sequenceExtension B (attainingLeft B) (attainingRight B) =
      (‖sequenceExtension B‖ : ℂ) := by
  rw [norm_sequenceExtension]
  exact sequenceExtension_of_tendsto B _ _ _ (tendsto_attaining_value B)

theorem model_norm (B : A →L[ℂ] D →L[ℂ] ℂ) (hB : B ≠ 0) : ‖model B‖ = 1 :=
  norm_normalized _ (sequenceExtension_ne_zero B hB) _ _ _ _ (extension_attains B)

theorem model_one (B : A →L[ℂ] D →L[ℂ] ℂ) (hB : B ≠ 0) : model B 1 1 = 1 :=
  normalized_one _ (sequenceExtension_ne_zero B hB) _ _ _ _ (extension_attains B)

/-- Recovery of every original pair, with the original norm as scale. -/
theorem model_recovery (B : A →L[ℂ] D →L[ℂ] ℂ) (hB : B ≠ 0) (a : A) (d : D) :
    (‖B‖ : ℂ) * model B (leftInput B a) (rightInput B d) = B a d := by
  have hconst : sequenceExtension B (constants A a) (constants D d) = B a d := by
    convert sequenceExtension_const B a d using 1 <;> rfl
  simpa only [model, leftInput_apply, rightInput_apply, leftUnitary, rightUnitary,
    norm_sequenceExtension] using
    normalized_recovery (sequenceExtension B) (sequenceExtension_ne_zero B hB)
      (attainingLeft B) (attainingRight B) (norm_attainingLeft_le B)
      (norm_attainingRight_le B) (constants A a) (constants D d) |>.trans hconst

theorem constants_sum_star_mul (X : Type*) [CStarAlgebra X] {ι : Type*}
    (s : Finset ι) (a : ι → X) :
    (∑ i ∈ s, star (constants X (a i)) * constants X (a i)) =
      constants X (∑ i ∈ s, star (a i) * a i) := by
  simp only [map_sum, map_mul, map_star]

theorem constants_sum_mul_star (X : Type*) [CStarAlgebra X] {ι : Type*}
    (s : Finset ι) (a : ι → X) :
    (∑ i ∈ s, constants X (a i) * star (constants X (a i))) =
      constants X (∑ i ∈ s, a i * star (a i)) := by
  simp only [map_sum, map_mul, map_star]

theorem leftInput_square_norms (B : A →L[ℂ] D →L[ℂ] ℂ)
    {ι : Type*} (s : Finset ι) (a : ι → A) :
    (‖∑ i ∈ s, star (leftInput B (a i)) * leftInput B (a i)‖ =
      ‖∑ i ∈ s, star (a i) * a i‖) ∧
    (‖∑ i ∈ s, leftInput B (a i) * star (leftInput B (a i))‖ =
      ‖∑ i ∈ s, a i * star (a i)‖) := by
  simp only [leftInput_apply]
  constructor
  · rw [norm_sum_star_unitaryInput, constants_sum_star_mul, norm_constants]
  · rw [norm_sum_unitaryInput_star, constants_sum_mul_star, norm_constants]

theorem rightInput_square_norms (B : A →L[ℂ] D →L[ℂ] ℂ)
    {ι : Type*} (s : Finset ι) (a : ι → D) :
    (‖∑ i ∈ s, star (rightInput B (a i)) * rightInput B (a i)‖ =
      ‖∑ i ∈ s, star (a i) * a i‖) ∧
    (‖∑ i ∈ s, rightInput B (a i) * star (rightInput B (a i))‖ =
      ‖∑ i ∈ s, a i * star (a i)‖) := by
  simp only [rightInput_apply]
  constructor
  · rw [norm_sum_star_unitaryInput, constants_sum_star_mul, norm_constants]
  · rw [norm_sum_unitaryInput_star, constants_sum_mul_star, norm_constants]

/-- One pair of linear inputs recovers the whole form and retains all
finite-family square budgets.  The normalized analytic estimate remains
a separate, not-yet-implemented proof obligation. -/
theorem exists_normalized_model (B : A →L[ℂ] D →L[ℂ] ℂ) (hB : B ≠ 0) :
    ∃ (V : TwoByTwo (BoundedContinuousFunction ℕ A) →L[ℂ] TwoByTwo (BoundedContinuousFunction ℕ D) →L[ℂ] ℂ)
      (L : A →L[ℂ] TwoByTwo (BoundedContinuousFunction ℕ A))
      (R : D →L[ℂ] TwoByTwo (BoundedContinuousFunction ℕ D)),
      ‖V‖ = 1 ∧ V 1 1 = 1 ∧
      (∀ a d, (‖B‖ : ℂ) * V (L a) (R d) = B a d) ∧
      (∀ a, ‖L a‖ = ‖a‖) ∧ (∀ d, ‖R d‖ = ‖d‖) ∧
      (∀ (n : ℕ) (a : Fin n → A),
        ‖∑ i, star (L (a i)) * L (a i)‖ = ‖∑ i, star (a i) * a i‖ ∧
        ‖∑ i, L (a i) * star (L (a i))‖ = ‖∑ i, a i * star (a i)‖) ∧
      (∀ (n : ℕ) (d : Fin n → D),
        ‖∑ i, star (R (d i)) * R (d i)‖ = ‖∑ i, star (d i) * d i‖ ∧
        ‖∑ i, R (d i) * star (R (d i))‖ = ‖∑ i, d i * star (d i)‖) := by
  refine ⟨model B, leftInput B, rightInput B, model_norm B hB, model_one B hB,
    model_recovery B hB, norm_leftInput B, norm_rightInput B, ?_, ?_⟩
  · intro n a
    exact leftInput_square_norms B Finset.univ a
  · intro n d
    exact rightInput_square_norms B Finset.univ d

end MathlibAnnex.NormalizedSequenceBilinear
