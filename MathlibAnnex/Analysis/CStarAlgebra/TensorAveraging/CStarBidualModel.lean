import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.BidualCStarLaws
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Algebra.Defs

/-!
# A C*-algebra structure on a dedicated copy of the actual Banach bidual

`Model A` is a type synonym, not a renorming, quotient, or new assumed model.
Its additive/normed/complete structure is the original strong Banach bidual's.
Multiplication is the explicitly constructed first-Arens product, the unit is
j_A(1), and the involution is f ↦ conjugate(F(f*)). The C*-identity was proved
from a constructed coefficient family, not assumed as a model field.

Instances are confined to this new carrier. No global multiplication/order is
installed on StrongDual, WeakDual, or the older BidualModel carrier.
C03 controller proof-source candidate, not compiled.
-/
set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section

namespace MathlibAnnex.CStarBidual
open MathlibAnnex.RepresentedBidual
universe u
variable (A : Type u) [CStarAlgebra A]

/-- The norm and vectors are exactly those of the original Banach bidual. -/
def Model := StrongDual ℂ (StrongDual ℂ A)

namespace Model

instance : NormedAddCommGroup (Model A) :=
  inferInstanceAs (NormedAddCommGroup (StrongDual ℂ (StrongDual ℂ A)))
instance : NormedSpace ℂ (Model A) :=
  inferInstanceAs (NormedSpace ℂ (StrongDual ℂ (StrongDual ℂ A)))
instance : CompleteSpace (Model A) :=
  inferInstanceAs (CompleteSpace (StrongDual ℂ (StrongDual ℂ A)))

/-- Identity isometry to the actual Banach bidual, also fixing its predual. -/
def toRaw : Model A ≃ₗᵢ[ℂ] StrongDual ℂ (StrongDual ℂ A) where
  toFun F := F
  invFun F := F
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

instance : Mul (Model A) := ⟨fun F G => arensProduct (toRaw A F) (toRaw A G)⟩
instance : One (Model A) := ⟨NormedSpace.inclusionInDoubleDual ℂ A 1⟩
instance : Star (Model A) := ⟨fun F => bidualStar (toRaw A F)⟩

@[simp] theorem toRaw_mul (F G : Model A) :
    toRaw A (F * G) = arensProduct (toRaw A F) (toRaw A G) := rfl
@[simp] theorem toRaw_one :
    toRaw A 1 = NormedSpace.inclusionInDoubleDual ℂ A 1 := rfl
@[simp] theorem toRaw_star (F : Model A) :
    toRaw A (star F) = bidualStar (toRaw A F) := rfl

/-- The additive group is the original one; every multiplicative law is
proved for the explicit product, rather than inherited from another algebra. -/
instance : Ring (Model A) where
  __ := (inferInstance : AddCommGroup (Model A))
  __ := (inferInstance : Mul (Model A))
  __ := (inferInstance : One (Model A))
  mul_assoc F G K := arensProduct_assoc _ _ _
  one_mul F := arensProduct_one_left _
  mul_one F := arensProduct_one_right _
  zero_mul F := arensProduct_zero_left _
  mul_zero F := arensProduct_zero_right _
  left_distrib F G K := arensProduct_add_right _ _ _
  right_distrib F G K := arensProduct_add_left _ _ _
  natCast n := n • (1 : Model A)
  natCast_zero := zero_nsmul _
  natCast_succ n := by simp only [succ_nsmul, one_nsmul]
  intCast z := z • (1 : Model A)
  intCast_ofNat n := by rfl
  intCast_negSucc n := by simp only [negSucc_zsmul]; rfl

instance : NormedRing (Model A) where
  __ := (inferInstance : Ring (Model A))
  __ := (inferInstance : NormedAddCommGroup (Model A))
  norm_mul_le F G := norm_arensProduct_le _ _

instance : Algebra ℂ (Model A) :=
  Algebra.ofModule
    (fun c F G => arensProduct_smul_left c _ _)
    (fun c F G => arensProduct_smul_right c _ _)

instance : NormedAlgebra ℂ (Model A) where
  __ := (inferInstance : Algebra ℂ (Model A))
  norm_smul_le c F := by
    exact le_of_eq (norm_smul c F)

instance : StarRing (Model A) where
  star_involutive F := bidualStar_bidualStar _
  star_mul F G := bidualStar_arensProduct _ _
  star_add F G := bidualStar_add _ _

instance : StarModule ℂ (Model A) where
  star_smul c F := bidualStar_smul c _

instance : CStarRing (Model A) where
  norm_mul_self_le F := (norm_arensStar_square (toRaw A F)).ge

instance : CStarAlgebra (Model A) where
  __ := (inferInstance : NormedRing (Model A))
  __ := (inferInstance : StarRing (Model A))
  __ := (inferInstance : CompleteSpace (Model A))
  __ := (inferInstance : CStarRing (Model A))
  __ := (inferInstance : NormedAlgebra ℂ (Model A))
  __ := (inferInstance : StarModule ℂ (Model A))

/-- A local-to-carrier order, with no modification of source A's order. -/
instance : PartialOrder (Model A) := CStarAlgebra.spectralOrder (Model A)
instance : StarOrderedRing (Model A) := CStarAlgebra.spectralOrderedRing (Model A)

/-- Source inclusion with its actual Arens product and involution. -/
def canonical : A →⋆ₐ[ℂ] Model A where
  toFun a := (toRaw A).symm (NormedSpace.inclusionInDoubleDual ℂ A a)
  map_one' := rfl
  map_zero' := by
    apply (toRaw A).injective
    exact (NormedSpace.inclusionInDoubleDualLi (𝕜 := ℂ) (E := A)).map_zero
  map_add' a b := by
    apply (toRaw A).injective
    exact (NormedSpace.inclusionInDoubleDualLi (𝕜 := ℂ) (E := A)).map_add a b
  map_mul' a b := by
    apply (toRaw A).injective
    ext f
    change f (a * b) = f (a * b)
    rfl
  commutes' c := by
    apply (toRaw A).injective
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change NormedSpace.inclusionInDoubleDual ℂ A (c • 1) =
      c • NormedSpace.inclusionInDoubleDual ℂ A 1
    exact map_smul _ c 1
  map_star' a := by
    apply (toRaw A).injective
    exact (bidualStar_canonical a).symm

@[simp] theorem canonical_eval (a : A) (f : StrongDual ℂ A) :
    toRaw A (canonical A a) f = f a := rfl

theorem isometry_canonical : Isometry (canonical A) :=
  (toRaw A).symm.isometry.comp (NormedSpace.inclusionInDoubleDualLi (𝕜 := ℂ) (E := A)).isometry

@[simp] theorem norm_canonical (a : A) : ‖canonical A a‖ = ‖a‖ := by
  change ‖NormedSpace.inclusionInDoubleDual ℂ A a‖ = ‖a‖
  exact (NormedSpace.inclusionInDoubleDualLi (𝕜 := ℂ) (E := A)).norm_map a

/-- Evaluations on the prescribed predual, with no representation-dependent
choice of topology. -/
def evaluation (f : StrongDual ℂ A) : Model A →L[ℂ] ℂ :=
  (NormedSpace.inclusionInDoubleDual ℂ (StrongDual ℂ A) f).comp
    (toRaw A).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem evaluation_apply (f : StrongDual ℂ A) (F : Model A) :
    evaluation A f F = toRaw A F f := rfl

end Model
end MathlibAnnex.CStarBidual
