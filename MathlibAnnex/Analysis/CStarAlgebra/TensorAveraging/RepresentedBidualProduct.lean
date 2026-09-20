import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.RepresentedBidual
import MathlibAnnex.Analysis.Normed.TensorProduct.Algebra

/-!
# Arens multiplication and the represented quotient map

Multiplication below is an explicit operation on the existing strong Banach
bidual.  No competing global algebra, star, order, or topology instance is
installed.  It is bound by an equality to the project's existing `firstArens`
construction.  Multiplicativity of the represented extension is proved for
this operation directly from Hilbert-valued coefficient recovery; it does
not require the still-missing theorem for arbitrary bilinear forms.

The quotient-direction map is not a constructed central-corner section.
Controller checkpoint C01: source bodies written, compilation not performed.
-/

set_option autoImplicit false
noncomputable section
open Topology
open MathlibAnnex.FiniteApproximation MathlibAnnex.WeakCompact
open MathlibAnnex.BidualBilinear

namespace MathlibAnnex.RepresentedBidual

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Multiplication followed by a source functional, using the existing
continuous bilinear multiplication map. -/
def multiplicationForm (f : StrongDual ℂ A) : A →L[ℂ] A →L[ℂ] ℂ :=
  (ContinuousLinearMap.compL ℂ A A ℂ f).comp (ContinuousLinearMap.mul ℂ A)

@[simp]
theorem multiplicationForm_apply (f : StrongDual ℂ A) (a b : A) :
    multiplicationForm f a b = f (a * b) := rfl

theorem norm_multiplicationForm_le (f : StrongDual ℂ A) :
    ‖multiplicationForm f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro a
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg f) (norm_nonneg a))
  intro b
  change ‖f (a * b)‖ ≤ ‖f‖ * ‖a‖ * ‖b‖
  exact (f.le_opNorm _).trans ((mul_le_mul_of_nonneg_left
    (norm_mul_le a b) (norm_nonneg f)).trans_eq (mul_assoc _ _ _).symm)

/-- A right slice in the first-Arens convention.  The outer variable of
`arensProduct F G` is `F`, and `G` is applied first. -/
def rightSlice (G : StrongDual ℂ (StrongDual ℂ A)) :
    StrongDual ℂ A →L[ℂ] StrongDual ℂ A :=
  LinearMap.mkContinuous
    { toFun := fun f => dualMap (multiplicationForm f) G
      map_add' := by
        intro f g
        ext a
        change G (multiplicationForm (f + g) a) =
          G (multiplicationForm f a) + G (multiplicationForm g a)
        have h : multiplicationForm (f + g) a =
            multiplicationForm f a + multiplicationForm g a := by
          ext b
          rfl
        rw [h, map_add]
      map_smul' := by
        intro c f
        ext a
        change G (multiplicationForm (c • f) a) =
          c • G (multiplicationForm f a)
        have h : multiplicationForm (c • f) a =
            c • multiplicationForm f a := by
          ext b
          rfl
        rw [h, map_smul] }
    ‖G‖ (by
      intro f
      apply ContinuousLinearMap.opNorm_le_bound _
        (mul_nonneg (norm_nonneg G) (norm_nonneg f))
      intro a
      change ‖G (multiplicationForm f a)‖ ≤ ‖G‖ * ‖f‖ * ‖a‖
      calc
        ‖G (multiplicationForm f a)‖ ≤ ‖G‖ * ‖multiplicationForm f a‖ :=
          G.le_opNorm _
        _ ≤ ‖G‖ * (‖f‖ * ‖a‖) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg G)
          exact ((multiplicationForm f).le_opNorm a).trans
            (mul_le_mul_of_nonneg_right (norm_multiplicationForm_le f)
              (norm_nonneg a))
        _ = ‖G‖ * ‖f‖ * ‖a‖ := (mul_assoc _ _ _).symm)

@[simp]
theorem rightSlice_apply (G : StrongDual ℂ (StrongDual ℂ A))
    (f : StrongDual ℂ A) (a : A) :
    rightSlice G f a = G (multiplicationForm f a) := rfl

theorem norm_rightSlice_le (G : StrongDual ℂ (StrongDual ℂ A)) :
    ‖rightSlice G‖ ≤ ‖G‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg G)
  intro f
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg G) (norm_nonneg f))
  intro a
  calc
    ‖rightSlice G f a‖ ≤ ‖G‖ * ‖multiplicationForm f a‖ := G.le_opNorm _
    _ ≤ ‖G‖ * (‖f‖ * ‖a‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg G)
      exact ((multiplicationForm f).le_opNorm a).trans
        (mul_le_mul_of_nonneg_right (norm_multiplicationForm_le f) (norm_nonneg a))
    _ = ‖G‖ * ‖f‖ * ‖a‖ := (mul_assoc _ _ _).symm

/-- An actual bounded functional, not an extra multiplication assumption. -/
def arensProduct (F G : StrongDual ℂ (StrongDual ℂ A)) :
    StrongDual ℂ (StrongDual ℂ A) := F.comp (rightSlice G)

@[simp]
theorem arensProduct_apply (F G : StrongDual ℂ (StrongDual ℂ A))
    (f : StrongDual ℂ A) : arensProduct F G f = F (rightSlice G f) := rfl

/-- Exact correspondence with the already established scalar Arens model. -/
theorem arensProduct_eq_firstArens (F G : StrongDual ℂ (StrongDual ℂ A))
    (f : StrongDual ℂ A) :
    arensProduct F G f = BidualForm.eval (firstArens (multiplicationForm f)) F G := rfl

theorem norm_arensProduct_le (F G : StrongDual ℂ (StrongDual ℂ A)) :
    ‖arensProduct F G‖ ≤ ‖F‖ * ‖G‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le F (rightSlice G)).trans
    (mul_le_mul_of_nonneg_left (norm_rightSlice_le G) (norm_nonneg F))

/-- Associativity is inherited from multiplication in `A`, with the order of
all three dual evaluations kept fixed. -/
theorem rightSlice_comp (G K : StrongDual ℂ (StrongDual ℂ A))
    (f : StrongDual ℂ A) :
    rightSlice G (rightSlice K f) = rightSlice (arensProduct G K) f := by
  ext a
  simp only [rightSlice_apply, arensProduct_apply]
  congr 1
  ext b
  simp only [multiplicationForm_apply, rightSlice_apply]
  congr 1
  ext c
  simp only [multiplicationForm_apply, mul_assoc]

theorem arensProduct_assoc (F G K : StrongDual ℂ (StrongDual ℂ A)) :
    arensProduct (arensProduct F G) K = arensProduct F (arensProduct G K) := by
  ext f
  simp only [arensProduct_apply, rightSlice_comp]

/-- The first variable is weak-star continuous for every fixed second
variable.  No assertion of full Arens regularity is made here. -/
theorem continuous_arensProduct_left (G : StrongDual ℂ (StrongDual ℂ A)) :
    Continuous (fun F : WeakDual ℂ (StrongDual ℂ A) =>
      StrongDual.toWeakDual (arensProduct (WeakDual.toStrongDual F) G)) := by
  apply WeakDual.continuous_of_continuous_eval
  intro f
  exact WeakDual.eval_continuous (rightSlice G f)

/-- Left multiplication by an actual source element agrees with its ordinary
bidual map. -/
theorem arensProduct_canonical_left (a : A) (G : StrongDual ℂ (StrongDual ℂ A)) :
    arensProduct (NormedSpace.inclusionInDoubleDual ℂ A a) G =
      bidualMap (ContinuousLinearMap.mul ℂ A a) G := by
  ext f
  rfl

/-- Right multiplication by a source element uses the right multiplier, not
the reversed left multiplier. -/
theorem arensProduct_canonical_right (F : StrongDual ℂ (StrongDual ℂ A)) (b : A) :
    arensProduct F (NormedSpace.inclusionInDoubleDual ℂ A b) =
      bidualMap ((ContinuousLinearMap.mul ℂ A).flip b) F := by
  ext f
  rfl

@[simp]
theorem arensProduct_canonical (a b : A) :
    arensProduct (NormedSpace.inclusionInDoubleDual ℂ A a)
      (NormedSpace.inclusionInDoubleDual ℂ A b) =
      NormedSpace.inclusionInDoubleDual ℂ A (a * b) := by
  ext f
  rfl

/-- The key represented slice identity: the same recovered vector is used
for every value of the left source element. -/
theorem rightSlice_coefficient (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (G : StrongDual ℂ (StrongDual ℂ A)) (xi : H) (g : StrongDual ℂ H) :
    rightSlice G (coefficient rho xi g) =
      coefficient rho (extension rho G xi) g := by
  ext a
  rw [rightSlice_apply, coefficient_apply]
  change G (multiplicationForm (coefficient rho xi g) a) =
    (g.comp (rho a)) (extension rho G xi)
  rw [coefficient_extension]
  congr 1
  ext b
  simp only [multiplicationForm_apply, coefficient_apply, map_mul,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply]

/-- Multiplicativity of the actual quotient map, without a hypothetical
section or a general Grothendieck supplier. -/
theorem extension_arensProduct (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (F G : StrongDual ℂ (StrongDual ℂ A)) :
    extension rho (arensProduct F G) = extension rho F * extension rho G := by
  apply ContinuousLinearMap.ext
  intro xi
  apply MathlibAnnex.HilbertBidual.eq_of_dual_eq
  intro g
  simp only [coefficient_extension, arensProduct_apply, rightSlice_coefficient,
    ContinuousLinearMap.mul_apply]

/-- Left covariance with the original represented algebra. -/
theorem extension_left_covariance (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (a : A) (F : StrongDual ℂ (StrongDual ℂ A)) :
    extension rho (bidualMap (ContinuousLinearMap.mul ℂ A a) F) =
      rho a * extension rho F := by
  rw [← arensProduct_canonical_left, extension_arensProduct, extension_canonical]

/-- Right covariance with the original represented algebra. -/
theorem extension_right_covariance (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (F : StrongDual ℂ (StrongDual ℂ A)) (a : A) :
    extension rho (bidualMap ((ContinuousLinearMap.mul ℂ A).flip a) F) =
      extension rho F * rho a := by
  rw [← arensProduct_canonical_right, extension_arensProduct, extension_canonical]

/-- The kernel is stable under multiplication on either side.  This is a
proved ideal property, not yet a description by a central projection. -/
theorem extension_kernel_twoSided (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (F G : StrongDual ℂ (StrongDual ℂ A)) (hF : extension rho F = 0) :
    extension rho (arensProduct F G) = 0 ∧
      extension rho (arensProduct G F) = 0 := by
  simp only [extension_arensProduct, hF, zero_mul, mul_zero, and_self]

end MathlibAnnex.RepresentedBidual
