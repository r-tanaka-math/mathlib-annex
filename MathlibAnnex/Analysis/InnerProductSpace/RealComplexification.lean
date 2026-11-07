/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Tactic

/-!
# Hilbert complexification of a real inner product space

The actual L2 product norm, complex scalar action, conjugation, norm-preserving extension and conjugation-invariant descent. Positivity and positive-part invariance are proved for the same maps.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped ComplexConjugate CStarAlgebra

namespace InnerProductSpace

/-- The Hilbert complexification of a real space, using the L2 rather than max norm. -/
def RealComplexification (H : Type*) := WithLp 2 (H × H)

namespace RealComplexification

section Algebra
variable {H : Type*} [AddCommGroup H] [Module ℝ H]

instance instAddCommGroup : AddCommGroup (RealComplexification H) :=
  inferInstanceAs (AddCommGroup (WithLp 2 (H × H)))

instance instModuleReal : Module ℝ (RealComplexification H) :=
  inferInstanceAs (Module ℝ (WithLp 2 (H × H)))

/-- Real coordinate of the complexification. -/
def re (z : RealComplexification H) : H := (WithLp.ofLp z).1

/-- Imaginary coordinate of the complexification. -/
def im (z : RealComplexification H) : H := (WithLp.ofLp z).2

/-- A vector with prescribed real and imaginary coordinates. -/
def mk (x y : H) : RealComplexification H := WithLp.toLp 2 (x, y)

@[ext]
theorem ext {z w : RealComplexification H} (hr : re z = re w) (hi : im z = im w) :
    z = w := by
  apply (WithLp.equiv 2 (H × H)).injective
  exact Prod.ext hr hi

@[simp]
theorem re_mk (x y : H) : re (mk x y) = x := rfl
@[simp]
theorem im_mk (x y : H) : im (mk x y) = y := rfl
@[simp]
theorem mk_re_im (z : RealComplexification H) : mk (re z) (im z) = z := rfl
@[simp]
theorem re_zero : re (0 : RealComplexification H) = 0 := rfl
@[simp]
theorem im_zero : im (0 : RealComplexification H) = 0 := rfl
@[simp]
theorem re_add (z w : RealComplexification H) : re (z + w) = re z + re w := rfl
@[simp]
theorem im_add (z w : RealComplexification H) : im (z + w) = im z + im w := rfl
@[simp]
theorem re_neg (z : RealComplexification H) : re (-z) = -re z := rfl
@[simp]
theorem im_neg (z : RealComplexification H) : im (-z) = -im z := rfl
@[simp]
theorem re_sub (z w : RealComplexification H) : re (z - w) = re z - re w := rfl
@[simp]
theorem im_sub (z w : RealComplexification H) : im (z - w) = im z - im w := rfl
@[simp]
theorem re_real_smul (r : ℝ) (z : RealComplexification H) : re (r • z) = r • re z := rfl
@[simp]
theorem im_real_smul (r : ℝ) (z : RealComplexification H) : im (r • z) = r • im z := rfl

instance instSMulComplex : SMul ℂ (RealComplexification H) where
  smul a z := mk (a.re • re z - a.im • im z) (a.im • re z + a.re • im z)

@[simp]
theorem re_complex_smul (a : ℂ) (z : RealComplexification H) :
    re (a • z) = a.re • re z - a.im • im z := rfl

@[simp]
theorem im_complex_smul (a : ℂ) (z : RealComplexification H) :
    im (a • z) = a.im • re z + a.re • im z := rfl

instance instModuleComplex : Module ℂ (RealComplexification H) where
  one_smul z := by ext <;> simp
  mul_smul a b z := by
    ext <;> simp [Complex.mul_re, Complex.mul_im, smul_add, smul_sub,
      add_smul, sub_smul, smul_smul] <;> module
  smul_zero a := by ext <;> simp
  smul_add a z w := by ext <;> simp [smul_add] <;> module
  add_smul a b z := by ext <;> simp [add_smul] <;> module
  zero_smul z := by ext <;> simp

@[simp]
theorem ofReal_smul (r : ℝ) (z : RealComplexification H) :
    (r : ℂ) • z = r • z := by
  apply ext
  · change r • re z - (0 : ℝ) • im z = r • re z
    simp
  · change (0 : ℝ) • re z + r • im z = r • im z
    simp

instance instIsScalarTower : IsScalarTower ℝ ℂ (RealComplexification H) where
  smul_assoc r a z := by
    ext <;> simp [smul_add, smul_sub, smul_smul] <;> module

/-- The original real scalar action commutes with the newly defined complex action. -/
instance instSMulCommClassComplexReal : SMulCommClass ℂ ℝ (RealComplexification H) where
  smul_comm a r z := by
    rw [← ofReal_smul r z, ← ofReal_smul r (a • z)]
    exact smul_comm a (r : ℂ) z

end Algebra

section Geometry
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

instance instNormedAddCommGroup : NormedAddCommGroup (RealComplexification H) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (H × H)))

instance instNormedSpaceReal : NormedSpace ℝ (RealComplexification H) :=
  inferInstanceAs (NormedSpace ℝ (WithLp 2 (H × H)))

/-- This identity fixes the Hilbert norm; the max norm on H × H is not used. -/
theorem norm_sq (z : RealComplexification H) :
    ‖z‖ ^ 2 = ‖re z‖ ^ 2 + ‖im z‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 z

/-- The complex scalar action multiplies the L2 norm by the complex modulus. -/
theorem norm_complex_smul_sq (a : ℂ) (z : RealComplexification H) :
    ‖a • z‖ ^ 2 = ‖a‖ ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_sq, re_complex_smul, im_complex_smul, norm_sq,
    Complex.sq_norm, Complex.normSq_apply]
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm (im z) (re z)]
  ring

instance instNormedSpaceComplex : NormedSpace ℂ (RealComplexification H) where
  norm_smul_le a z := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg a) (norm_nonneg z))).mp
    simpa only [mul_pow] using (norm_complex_smul_sq a z).le

instance instInnerProductSpace : InnerProductSpace ℂ (RealComplexification H) where
  inner z w := ⟨inner ℝ (re z) (re w) + inner ℝ (im z) (im w),
    inner ℝ (re z) (im w) - inner ℝ (im z) (re w)⟩
  norm_sq_eq_re_inner z := by
    change ‖z‖ ^ 2 = inner ℝ (re z) (re z) + inner ℝ (im z) (im z)
    simpa only [real_inner_self_eq_norm_sq] using norm_sq z
  conj_inner_symm z w := by
    apply Complex.ext <;> dsimp <;> simp only [real_inner_comm] <;> ring
  add_left z w v := by
    apply Complex.ext <;> dsimp <;> simp only [inner_add_left] <;> ring
  smul_left z w a := by
    apply Complex.ext <;>
      simp only [re_complex_smul, im_complex_smul, inner_add_left, inner_sub_left,
        real_inner_smul_left, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im] <;> ring

/-- The defining sesquilinear formula, conjugate-linear in its first argument. -/
theorem inner_eq (z w : RealComplexification H) :
    inner ℂ z w = ⟨inner ℝ (re z) (re w) + inner ℝ (im z) (im w),
      inner ℝ (re z) (im w) - inner ℝ (im z) (re w)⟩ := rfl

/-- Completeness is inherited from the genuine L2 product uniformity. -/
instance instCompleteSpace [CompleteSpace H] : CompleteSpace (RealComplexification H) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (H × H)))

theorem norm_re_le (z : RealComplexification H) : ‖re z‖ ≤ ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq]
  exact le_add_of_nonneg_right (sq_nonneg ‖im z‖)

theorem norm_im_le (z : RealComplexification H) : ‖im z‖ ≤ ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq]
  exact le_add_of_nonneg_left (sq_nonneg ‖re z‖)

/-- Real part as a continuous real-linear map. -/
def reCLM : RealComplexification H →L[ℝ] H :=
  LinearMap.mkContinuous
    { toFun := re, map_add' := re_add, map_smul' := re_real_smul }
    1 (fun z => by simpa using norm_re_le z)

/-- The real space embeds isometrically as the vectors with zero imaginary part. -/
def embed : H →ₗᵢ[ℝ] RealComplexification H where
  toFun x := mk x 0
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖mk x 0‖ ^ 2 = ‖x‖ ^ 2
    simpa only [re_mk, im_mk, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
      using norm_sq (mk x 0)

@[simp]
theorem re_embed (x : H) : re (embed x) = x := rfl
@[simp]
theorem im_embed (x : H) : im (embed x) = 0 := rfl
@[simp]
theorem inner_embed (x y : H) :
    inner ℂ (embed x) (embed y) = (inner ℝ x y : ℂ) := by
  apply Complex.ext <;> simp [inner_eq]

/-- Canonical conjugation as an actual conjugate-linear isometric equivalence. -/
def conjugation : RealComplexification H ≃ₗᵢ⋆[ℂ] RealComplexification H where
  toFun z := mk (re z) (-im z)
  invFun z := mk (re z) (-im z)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' z w := by ext <;> simp [add_comm]
  map_smul' a z := by ext <;> simp [smul_add, smul_sub] <;> module
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖mk (re z) (-im z)‖ ^ 2 = ‖z‖ ^ 2
    simp only [norm_sq, re_mk, im_mk, norm_neg]

@[simp]
theorem re_conjugation (z : RealComplexification H) :
    re (conjugation z) = re z := rfl
@[simp]
theorem im_conjugation (z : RealComplexification H) :
    im (conjugation z) = -im z := rfl
@[simp]
theorem conjugation_conjugation (z : RealComplexification H) :
    conjugation (conjugation z) = z := by ext <;> simp
@[simp]
theorem conjugation_embed (x : H) : conjugation (embed x) = embed x := by
  ext <;> simp

/-- The fixed vectors of conjugation are exactly the original real vectors. -/
theorem conjugation_eq_self_iff (z : RealComplexification H) :
    conjugation z = z ↔ z = embed (re z) := by
  constructor
  · intro h
    have hi : -im z = im z := congrArg im h
    have hz : im z = 0 := by
      have htwo : (2 : ℝ) • im z = 0 := by
        calc (2 : ℝ) • im z = im z + im z := by module
             _ = -im z + im z := by rw [hi]
             _ = 0 := neg_add_cancel _
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    ext <;> simp [hz]
  · intro h
    rw [h, conjugation_embed]

theorem inner_conjugation (z w : RealComplexification H) :
    inner ℂ (conjugation z) (conjugation w) = star (inner ℂ z w) := by
  apply Complex.ext <;> simp [inner_eq] <;> ring

theorem inner_conjugation_left (z w : RealComplexification H) :
    inner ℂ (conjugation z) w = star (inner ℂ z (conjugation w)) := by
  simpa only [conjugation_conjugation] using inner_conjugation z (conjugation w)

end Geometry

section Operators
variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Complex extension of a bounded real-linear map, acting coordinatewise. -/
def extend (T : H →L[ℝ] K) : RealComplexification H →L[ℂ] RealComplexification K :=
  LinearMap.mkContinuous
    { toFun := fun z => mk (T (re z)) (T (im z))
      map_add' := by intro z w; ext <;> simp
      map_smul' := by intro a z; ext <;> simp }
    ‖T‖ (by
      intro z
      have h₁ := norm_sq (mk (T (re z)) (T (im z)))
      have h₂ := norm_sq z
      have hr := T.le_opNorm (re z)
      have hi := T.le_opNorm (im z)
      have hr2 : ‖T (re z)‖ ^ 2 ≤ (‖T‖ * ‖re z‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg T) (norm_nonneg _))).mpr hr
      have hi2 : ‖T (im z)‖ ^ 2 ≤ (‖T‖ * ‖im z‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg T) (norm_nonneg _))).mpr hi
      simp only [re_mk, im_mk] at h₁
      have hs : ‖mk (T (re z)) (T (im z))‖ ^ 2 ≤ (‖T‖ * ‖z‖) ^ 2 := by
        calc
          _ = ‖T (re z)‖ ^ 2 + ‖T (im z)‖ ^ 2 := h₁
          _ ≤ (‖T‖ * ‖re z‖) ^ 2 + (‖T‖ * ‖im z‖) ^ 2 :=
            add_le_add hr2 hi2
          _ = (‖T‖ * ‖z‖) ^ 2 := by simp only [mul_pow]; rw [h₂]; ring
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg T)
        (norm_nonneg z))).mp hs)

@[simp]
theorem re_extend (T : H →L[ℝ] K) (z : RealComplexification H) :
    re (extend T z) = T (re z) := rfl
@[simp]
theorem im_extend (T : H →L[ℝ] K) (z : RealComplexification H) :
    im (extend T z) = T (im z) := rfl
@[simp]
theorem extend_embed (T : H →L[ℝ] K) (x : H) :
    extend T (embed x) = embed (T x) := by ext <;> simp

/-- Complexification preserves the original real operator norm, not merely an equivalent norm. -/
theorem norm_extend (T : H →L[ℝ] K) : ‖extend T‖ = ‖T‖ := by
  apply le_antisymm
  · exact LinearMap.mkContinuous_norm_le _ (norm_nonneg T) _
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := (extend T).le_opNorm (embed x)
    simpa only [extend_embed, LinearIsometry.norm_map] using h

theorem extend_conjugation (T : H →L[ℝ] K) (z : RealComplexification H) :
    extend T (conjugation z) = conjugation (extend T z) := by ext <;> simp

/-- Symmetry of the real operator gives complex self-adjointness after extension. -/
theorem isSymmetric_extend (T : H →L[ℝ] H) (hT : T.IsSymmetric) :
    (extend T).IsSymmetric := by
  intro z w
  change inner ℂ (extend T z) w = inner ℂ z (extend T w)
  apply Complex.ext <;> simp only [inner_eq, re_extend, im_extend]
  · exact congrArg₂ (· + ·) (hT (re z) (re w)) (hT (im z) (im w))
  · exact congrArg₂ (· - ·) (hT (re z) (im w)) (hT (im z) (re w))

end Operators

section Descent
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Conjugating on both sides gives a genuinely complex-linear operator. -/
def conjugateOperator (A : RealComplexification H →L[ℂ] RealComplexification H) :
    RealComplexification H →L[ℂ] RealComplexification H :=
  (conjugation (H := H)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (A.comp (conjugation (H := H)).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp]
theorem conjugateOperator_apply (A : RealComplexification H →L[ℂ] RealComplexification H)
    (z : RealComplexification H) :
    conjugateOperator A z = conjugation (A (conjugation z)) := rfl

@[simp]
theorem conjugateOperator_zero :
    conjugateOperator (0 : RealComplexification H →L[ℂ] RealComplexification H) = 0 := by
  apply ContinuousLinearMap.ext
  intro z
  simp

@[simp]
theorem conjugateOperator_sub (A B : RealComplexification H →L[ℂ] RealComplexification H) :
    conjugateOperator (A - B) = conjugateOperator A - conjugateOperator B := by
  apply ContinuousLinearMap.ext
  intro z
  simp

@[simp]
theorem conjugateOperator_mul (A B : RealComplexification H →L[ℂ] RealComplexification H) :
    conjugateOperator (A * B) = conjugateOperator A * conjugateOperator B := by
  apply ContinuousLinearMap.ext
  intro z
  change conjugation (A (B (conjugation z))) =
    conjugation (A (conjugation (conjugation (B (conjugation z)))))
  rw [conjugation_conjugation]

@[simp]
theorem conjugateOperator_extend (D : H →L[ℝ] H) :
    conjugateOperator (extend D) = extend D := by
  apply ContinuousLinearMap.ext
  intro z
  simp [extend_conjugation]

/-- Positivity survives antiunitary conjugation; this is a direct inner-product proof. -/
theorem isPositive_conjugateOperator
    {A : RealComplexification H →L[ℂ] RealComplexification H} (hA : A.IsPositive) :
    (conjugateOperator A).IsPositive := by
  refine ⟨?_, ?_⟩
  · intro z w
    change inner ℂ (conjugation (A (conjugation z))) w =
      inner ℂ z (conjugation (A (conjugation w)))
    calc
      _ = star (inner ℂ (A (conjugation z)) (conjugation w)) :=
        inner_conjugation_left _ _
      _ = star (inner ℂ (conjugation z) (A (conjugation w))) :=
        congrArg star (hA.isSymmetric _ _)
      _ = _ := by
        simpa only [conjugation_conjugation] using
          (inner_conjugation (conjugation z) (A (conjugation w))).symm
  · intro z
    change 0 ≤ (inner ℂ (conjugation (A (conjugation z))) z).re
    rw [inner_conjugation_left]
    have hp := hA.re_inner_nonneg_left (conjugation z)
    change 0 ≤ (inner ℂ (A (conjugation z)) (conjugation z)).re at hp
    simpa only [Complex.star_def, Complex.conj_re] using hp

/-- Real compression, which becomes restriction when the operator preserves real vectors. -/
def descend (A : RealComplexification H →L[ℂ] RealComplexification H) : H →L[ℝ] H :=
  reCLM.comp ((A.restrictScalars ℝ).comp embed.toContinuousLinearMap)

@[simp]
theorem descend_apply (A : RealComplexification H →L[ℂ] RealComplexification H) (x : H) :
    descend A x = re (A (embed x)) := rfl

/-- A conjugation-invariant operator maps real fixed points to real fixed points. -/
theorem embed_descend (A : RealComplexification H →L[ℂ] RealComplexification H)
    (hA : conjugateOperator A = A) (x : H) :
    embed (descend A x) = A (embed x) := by
  have hfix := congrArg (fun B : RealComplexification H →L[ℂ] RealComplexification H =>
    B (embed x)) hA
  simp only [conjugateOperator_apply, conjugation_embed] at hfix
  exact ((conjugation_eq_self_iff _).mp hfix).symm

@[simp]
theorem descend_extend (D : H →L[ℝ] H) : descend (extend D) = D := by
  ext x
  simp

@[simp]
theorem descend_zero :
    descend (0 : RealComplexification H →L[ℂ] RealComplexification H) = 0 := by
  ext x
  simp

@[simp]
theorem descend_sub (A B : RealComplexification H →L[ℂ] RealComplexification H) :
    descend (A - B) = descend A - descend B := by
  ext x
  simp

/-- Restriction preserves composition when the right factor preserves the real space. -/
theorem descend_mul (A B : RealComplexification H →L[ℂ] RealComplexification H)
    (hB : conjugateOperator B = B) :
    descend (A * B) = descend A * descend B := by
  ext x
  change re (A (B (embed x))) = re (A (embed (descend B x)))
  rw [embed_descend B hB]

/-- Descending an invariant positive operator gives a positive real operator. -/
theorem isPositive_descend
    {A : RealComplexification H →L[ℂ] RealComplexification H}
    (hfix : conjugateOperator A = A) (hpos : A.IsPositive) :
    (descend A).IsPositive := by
  refine ⟨?_, ?_⟩
  · intro x y
    have he := hpos.isSymmetric (embed x) (embed y)
    change inner ℂ (A (embed x)) (embed y) = inner ℂ (embed x) (A (embed y)) at he
    rw [← embed_descend A hfix x, ← embed_descend A hfix y,
      inner_embed, inner_embed] at he
    exact Complex.ofReal_injective he
  · intro x
    have hp := hpos.re_inner_nonneg_left (embed x)
    rw [← embed_descend A hfix x, inner_embed] at hp
    change 0 ≤ inner ℝ (descend A x) x
    change 0 ≤ (Complex.ofReal (inner ℝ (descend A x) x)).re at hp
    simpa only [Complex.ofReal_re] using hp

variable [CompleteSpace H]

local instance : NormedSpace ℝ (RealComplexification H →L[ℂ] RealComplexification H) :=
  NormedSpace.complexToReal

local instance : Module ℝ (RealComplexification H →L[ℂ] RealComplexification H) :=
  (NormedSpace.complexToReal :
    NormedSpace ℝ (RealComplexification H →L[ℂ] RealComplexification H)).toModule

/-- Uniqueness, not a postulated real CFC, proves invariance of the complex parts. -/
theorem conjugateOperator_posPart_negPart
    (A : RealComplexification H →L[ℂ] RealComplexification H)
    (hA : IsSelfAdjoint A) (hfix : conjugateOperator A = A) :
    conjugateOperator (A⁺) = A⁺ ∧ conjugateOperator (A⁻) = A⁻ := by
  have hp : (A⁺).IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive).mp (CFC.posPart_nonneg A)
  have hn : (A⁻).IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive).mp (CFC.negPart_nonneg A)
  have hdec : A = conjugateOperator (A⁺) - conjugateOperator (A⁻) := by
    calc
      A = conjugateOperator A := hfix.symm
      _ = conjugateOperator (A⁺ - A⁻) :=
        congrArg conjugateOperator (CFC.posPart_sub_negPart A hA).symm
      _ = _ := conjugateOperator_sub _ _
  have hzero : conjugateOperator (A⁺) * conjugateOperator (A⁻) = 0 := by
    rw [← conjugateOperator_mul, CFC.posPart_mul_negPart, conjugateOperator_zero]
  have hh := CFC.posPart_negPart_unique hdec hzero
    ((ContinuousLinearMap.nonneg_iff_isPositive).mpr (isPositive_conjugateOperator hp))
    ((ContinuousLinearMap.nonneg_iff_isPositive).mpr (isPositive_conjugateOperator hn))
  exact ⟨hh.1.symm, hh.2.symm⟩

end Descent
end RealComplexification
end InnerProductSpace

