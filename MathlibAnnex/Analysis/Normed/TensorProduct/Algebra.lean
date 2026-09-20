import Mathlib.Analysis.Normed.Operator.Mul
import MathlibAnnex.Analysis.Normed.TensorProduct.Projective

/-!
# Projective tensor maps for normed algebras

The constructions here are applications of the generic projective universal
property.  They do not depend on C*-algebra-specific material.
-/

set_option autoImplicit false

namespace MathlibAnnex.ProjectiveTensorProduct.Algebra

universe uK uA

noncomputable section

variable (𝕜 : Type uK) [RCLike 𝕜]
variable (A : Type uA) [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- Left multiplication by `a`. -/
def leftMul (a : A) : A →L[𝕜] A := ContinuousLinearMap.mul 𝕜 A a

/-- Right multiplication by `a`. -/
def rightMul (a : A) : A →L[𝕜] A := (ContinuousLinearMap.mul 𝕜 A).flip a

@[simp]
theorem leftMul_apply (a x : A) : leftMul 𝕜 A a x = a * x := rfl

@[simp]
theorem rightMul_apply (a x : A) : rightMul 𝕜 A a x = x * a := rfl

theorem norm_leftMul_le (a : A) : ‖leftMul 𝕜 A a‖ ≤ ‖a‖ :=
  ContinuousLinearMap.opNorm_mul_apply_le 𝕜 A a

theorem norm_rightMul_le (a : A) : ‖rightMul 𝕜 A a‖ ≤ ‖a‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun x ↦ ?_
  simpa [rightMul, mul_comm ‖x‖ ‖a‖] using norm_mul_le x a

/-- Algebra multiplication as a bounded bilinear map. -/
def multiplicationBilinear :
    BoundedBilinearMap 𝕜 A A A :=
  BoundedBilinearMap.ofContinuousLinearMap 𝕜 A A A
    (ContinuousLinearMap.mul 𝕜 A)

@[simp]
theorem multiplicationBilinear_apply (x y : A) :
    BoundedBilinearMap.apply 𝕜 A A A (multiplicationBilinear 𝕜 A) x y = x * y :=
  rfl

variable [CompleteSpace A]

/-- Multiplication extended to the completed projective tensor product. -/
def multiplication : Completion 𝕜 A A →L[𝕜] A :=
  liftIsometry 𝕜 A A A (multiplicationBilinear 𝕜 A)

@[simp]
theorem multiplication_tprod (x y : A) :
    multiplication 𝕜 A (tprod 𝕜 A A x y) = x * y := by
  rw [multiplication, liftIsometry_tprod]
  rfl

theorem norm_multiplication_le : ‖multiplication 𝕜 A‖ ≤ 1 := by
  rw [multiplication, (liftIsometry 𝕜 A A A).norm_map,
    multiplicationBilinear, BoundedBilinearMap.norm_ofContinuousLinearMap]
  exact ContinuousLinearMap.opNorm_mul_le 𝕜 A

/-- Left multiplication on the first tensor factor. -/
def leftAction (a : A) : Completion 𝕜 A A →L[𝕜] Completion 𝕜 A A :=
  map 𝕜 A A A A (leftMul 𝕜 A a) (ContinuousLinearMap.id 𝕜 A)

/-- Right multiplication on the second tensor factor. -/
def rightAction (a : A) : Completion 𝕜 A A →L[𝕜] Completion 𝕜 A A :=
  map 𝕜 A A A A (ContinuousLinearMap.id 𝕜 A) (rightMul 𝕜 A a)

@[simp]
theorem leftAction_tprod (a x y : A) :
    leftAction 𝕜 A a (tprod 𝕜 A A x y) = tprod 𝕜 A A (a * x) y := by
  simp [leftAction]

@[simp]
theorem rightAction_tprod (a x y : A) :
    rightAction 𝕜 A a (tprod 𝕜 A A x y) = tprod 𝕜 A A x (y * a) := by
  simp [rightAction]

theorem norm_leftAction_le (a : A) : ‖leftAction 𝕜 A a‖ ≤ ‖a‖ := by
  calc
    ‖leftAction 𝕜 A a‖ ≤
        ‖leftMul 𝕜 A a‖ * ‖ContinuousLinearMap.id 𝕜 A‖ :=
      norm_map_le 𝕜 A A A A _ _
    _ ≤ ‖a‖ * 1 :=
      mul_le_mul (norm_leftMul_le 𝕜 A a) ContinuousLinearMap.norm_id_le
        (norm_nonneg _) (norm_nonneg a)
    _ = ‖a‖ := mul_one _

theorem norm_rightAction_le (a : A) : ‖rightAction 𝕜 A a‖ ≤ ‖a‖ := by
  calc
    ‖rightAction 𝕜 A a‖ ≤
        ‖ContinuousLinearMap.id 𝕜 A‖ * ‖rightMul 𝕜 A a‖ :=
      norm_map_le 𝕜 A A A A _ _
    _ ≤ 1 * ‖a‖ :=
      mul_le_mul ContinuousLinearMap.norm_id_le (norm_rightMul_le 𝕜 A a)
        (norm_nonneg _) zero_le_one
    _ = ‖a‖ := one_mul _

/-- The bilinear map `(x,y) ↦ (b ↦ x * b * y)`. -/
def sandwichOperatorBilinear :
    BoundedBilinearMap 𝕜 A A (A →L[𝕜] A) :=
  BoundedBilinearMap.ofContinuousLinearMap 𝕜 A A (A →L[𝕜] A)
    (ContinuousLinearMap.mulLeftRight 𝕜 A)

/-- The canonical contraction from the projective tensor product to bounded
operators, sending `x ⊗ y` to `b ↦ x * b * y`. -/
def sandwichOperator : Completion 𝕜 A A →L[𝕜] (A →L[𝕜] A) :=
  liftIsometry 𝕜 A A (A →L[𝕜] A) (sandwichOperatorBilinear 𝕜 A)

@[simp]
theorem sandwichOperator_tprod (x y b : A) :
    sandwichOperator 𝕜 A (tprod 𝕜 A A x y) b = x * b * y := by
  rw [sandwichOperator, liftIsometry_tprod]
  rfl

theorem norm_sandwichOperator_le : ‖sandwichOperator 𝕜 A‖ ≤ 1 := by
  rw [sandwichOperator, (liftIsometry 𝕜 A A (A →L[𝕜] A)).norm_map,
    sandwichOperatorBilinear, BoundedBilinearMap.norm_ofContinuousLinearMap]
  exact ContinuousLinearMap.opNorm_mulLeftRight_le 𝕜 A

/-- The tensor left/right action difference becomes the ordinary commutator
under the sandwich operator. -/
theorem sandwichOperator_action_sub (a b : A) (t : Completion 𝕜 A A) :
    sandwichOperator 𝕜 A
        (leftAction 𝕜 A a t - rightAction 𝕜 A a t) b =
      a * sandwichOperator 𝕜 A t b - sandwichOperator 𝕜 A t b * a := by
  let ev : (A →L[𝕜] A) →L[𝕜] A := ContinuousLinearMap.apply 𝕜 A b
  let θ : Completion 𝕜 A A →L[𝕜] A := ev.comp (sandwichOperator 𝕜 A)
  have hop :
      θ.comp (leftAction 𝕜 A a - rightAction 𝕜 A a) =
        (leftMul 𝕜 A a).comp θ - (rightMul 𝕜 A a).comp θ := by
    apply ext_tprod 𝕜 A A A
    intro x y
    simp [θ, ev, mul_assoc]
  simpa [θ, ev] using congrArg (fun q : Completion 𝕜 A A →L[𝕜] A ↦ q t) hop

/-- The usual curried sandwich map `(x,y) ↦ x * a * y`. -/
def sandwichCurried (a : A) : A →L[𝕜] A →L[𝕜] A :=
  (ContinuousLinearMap.compL 𝕜 A (A →L[𝕜] A) A
      (ContinuousLinearMap.apply 𝕜 A a)).comp
    (ContinuousLinearMap.mulLeftRight 𝕜 A)

@[simp]
theorem sandwichCurried_apply (a x y : A) :
    sandwichCurried 𝕜 A a x y = x * a * y := rfl

theorem norm_sandwichCurried_le (a : A) :
    ‖sandwichCurried 𝕜 A a‖ ≤ ‖a‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun x ↦ ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y ↦ ?_
  change ‖x * a * y‖ ≤ (‖a‖ * ‖x‖) * ‖y‖
  calc
    ‖x * a * y‖ ≤ (‖x‖ * ‖a‖) * ‖y‖ :=
      (norm_mul_le (x * a) y).trans <| mul_le_mul_of_nonneg_right
        (norm_mul_le x a) (norm_nonneg y)
    _ = (‖a‖ * ‖x‖) * ‖y‖ := by rw [mul_comm ‖x‖ ‖a‖]

/-- Sandwich multiplication as a bounded bilinear map. -/
def sandwichBilinear (a : A) : BoundedBilinearMap 𝕜 A A A :=
  BoundedBilinearMap.ofContinuousLinearMap 𝕜 A A A (sandwichCurried 𝕜 A a)

/-- Sandwich multiplication extended to the completed projective tensor
product. -/
def sandwich (a : A) : Completion 𝕜 A A →L[𝕜] A :=
  liftIsometry 𝕜 A A A (sandwichBilinear 𝕜 A a)

@[simp]
theorem sandwich_tprod (a x y : A) :
    sandwich 𝕜 A a (tprod 𝕜 A A x y) = x * a * y := by
  rw [sandwich, liftIsometry_tprod]
  rfl

theorem norm_sandwich_le (a : A) : ‖sandwich 𝕜 A a‖ ≤ ‖a‖ := by
  rw [sandwich, (liftIsometry 𝕜 A A A).norm_map,
    sandwichBilinear, BoundedBilinearMap.norm_ofContinuousLinearMap]
  exact norm_sandwichCurried_le 𝕜 A a

end

end MathlibAnnex.ProjectiveTensorProduct.Algebra
