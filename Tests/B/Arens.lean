import MathlibAnnex.Analysis.CStarAlgebra.Bidual.Arens

set_option autoImplicit false
noncomputable section

open Topology
open MathlibAnnex.BidualBilinear MathlibAnnex.RepresentedBidual
open MathlibAnnex.WeakCompact
open MathlibAnnex.Analysis.CStarAlgebra.Bidual

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {B : Type v} [NonUnitalCStarAlgebra B]

-- The test consumes the literal StrongDual carrier and both scalar extensions.
example (F G : StrongDual ℂ (StrongDual ℂ A)) (f : StrongDual ℂ A) :
    arensProduct F G f = BidualForm.eval (firstArens (multiplicationForm f)) F G ∧
      arensProduct F G f = BidualForm.eval (secondArens (multiplicationForm f)) F G :=
  ⟨arensProduct_eq_firstArens F G f, arensProduct_eq_secondArens F G f⟩

example (a b : A) (f : StrongDual ℂ A) :
    arensProduct (NormedSpace.inclusionInDoubleDual ℂ A a)
      (NormedSpace.inclusionInDoubleDual ℂ A b) f = f (a * b) := by
  rw [arensProduct_canonical]
  rfl

example (F G : StrongDual ℂ (StrongDual ℂ A)) :
    ‖arensProduct F G‖ ≤ ‖F‖ * ‖G‖ := norm_arensProduct_le F G

example (F G K : StrongDual ℂ (StrongDual ℂ A)) :
    arensProduct (arensProduct F G) K = arensProduct F (arensProduct G K) :=
  arensProduct_assoc F G K

example (f : StrongDual ℂ A) :
    IsCompact (closure (weakBallImage (multiplicationForm f))) :=
  isWeaklyCompact_multiplicationForm f

example (F : StrongDual ℂ (StrongDual ℂ A)) :
    Continuous (fun G : WeakDual ℂ (StrongDual ℂ A) =>
      StrongDual.toWeakDual (arensProduct F (WeakDual.toStrongDual G))) :=
  MathlibAnnex.Analysis.CStarAlgebra.Bidual.continuous_arensProduct_right F

example (T : A →L[ℂ] B) (hT : ∀ a b : A, T (a * b) = T a * T b)
    (F G : StrongDual ℂ (StrongDual ℂ A)) (f : StrongDual ℂ B) :
    bidualMap T (arensProduct F G) f =
      arensProduct (bidualMap T F) (bidualMap T G) f := by
  rw [bidualMap_arensProduct T hT]
