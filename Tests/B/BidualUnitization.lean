import MathlibAnnex.Analysis.CStarAlgebra.Bidual.Unitization

set_option autoImplicit false
noncomputable section

open Topology
open scoped CStarAlgebra
open MathlibAnnex.RepresentedBidual MathlibAnnex.WeakCompact
open MathlibAnnex.Analysis.CStarAlgebra.Bidual

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {B : Type v} [NonUnitalCStarAlgebra B]

private def starHomContinuousLinearMap (φ : A →⋆ₙₐ[ℂ] B) : A →L[ℂ] B where
  toLinearMap := (φ : A →ₗ[ℂ] B)
  cont := (NonUnitalStarAlgHom.instContinuousLinearMapClassComplex (F := A →⋆ₙₐ[ℂ] B)).map_continuous φ

-- No extra multiplicativity or star-preservation premise is required of a star homomorphism.
example (φ : A →⋆ₙₐ[ℂ] B) (F G : StrongDual ℂ (StrongDual ℂ A)) :
    bidualMap (starHomContinuousLinearMap φ) (arensProduct F G) =
      arensProduct (bidualMap (starHomContinuousLinearMap φ) F) (bidualMap (starHomContinuousLinearMap φ) G) :=
  bidualMap_arensProduct (starHomContinuousLinearMap φ) (map_mul φ) F G

example (φ : A →⋆ₙₐ[ℂ] B) (F : StrongDual ℂ (StrongDual ℂ A)) :
    bidualMap (starHomContinuousLinearMap φ) (bidualStar F) =
      bidualStar (bidualMap (starHomContinuousLinearMap φ) F) :=
  bidualMap_bidualStar (starHomContinuousLinearMap φ) (map_star φ) F

example (F : StrongDual ℂ (StrongDual ℂ A)) :
    ‖unitizationBidual F‖ = ‖F‖ := norm_unitizationBidual F

example (F : StrongDual ℂ (StrongDual ℂ A)) (f : StrongDual ℂ A) :
    unitizationBidual F
      (MathlibAnnex.Analysis.CStarAlgebra.unitizationDualExtension f) = F f :=
  unitizationBidual_eval_extension F f

example (F G : StrongDual ℂ (StrongDual ℂ A))
    (h : unitizationBidual F = unitizationBidual G) : F = G :=
  (unitizationBidualIsometry (A := A)).injective h

example (a : A) (g : StrongDual ℂ (Unitization ℂ A)) :
    unitizationBidual (NormedSpace.inclusionInDoubleDual ℂ A a) g =
      g (Unitization.inr a) := by
  rw [unitizationBidual_canonical]
  rfl

example (F : StrongDual ℂ (StrongDual ℂ A)) :
    ‖arensProduct (bidualStar F) F‖ = ‖F‖ * ‖F‖ :=
  MathlibAnnex.Analysis.CStarAlgebra.Bidual.norm_arensStar_square F

example (F G : StrongDual ℂ (StrongDual ℂ A)) :
    bidualStar (arensProduct F G) = arensProduct (bidualStar G) (bidualStar F) :=
  MathlibAnnex.Analysis.CStarAlgebra.Bidual.bidualStar_arensProduct F G

example : Continuous (fun F : WeakDual ℂ (StrongDual ℂ A) =>
    StrongDual.toWeakDual (bidualStar (WeakDual.toStrongDual F))) :=
  continuous_bidualStar

example : IsEmbedding (fun F : WeakDual ℂ (StrongDual ℂ A) =>
    StrongDual.toWeakDual (unitizationBidual (WeakDual.toStrongDual F))) :=
  isEmbedding_unitizationBidual

example (F G : StrongDual ℂ (StrongDual ℂ A))
    (f : StrongDual ℂ A) :
    arensProduct F G f =
      MathlibAnnex.BidualBilinear.BidualForm.eval
        (MathlibAnnex.BidualBilinear.secondArens (multiplicationForm f)) F G :=
  arensProduct_eq_secondArens F G f
