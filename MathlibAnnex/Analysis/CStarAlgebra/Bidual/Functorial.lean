import Mathlib.Analysis.CStarAlgebra.Spectrum
import MathlibAnnex.Analysis.CStarAlgebra.Bidual.Arens

/-!
# Involutions and the ordinary bidual functor

The ordinary `bidualMap` and the explicit `dualStar` / `bidualStar` maps
already exist. Here their compatibility is proved directly on functionals.
For a non-unital star algebra homomorphism, the source map is the existing
coercion to a continuous linear map supplied by Mathlib's `CStarAlgebra`
scope. No additional represented or abstract model is selected.
-/

set_option autoImplicit false
noncomputable section

open Topology
open scoped CStarAlgebra
open MathlibAnnex.RepresentedBidual MathlibAnnex.WeakCompact

namespace MathlibAnnex.Analysis.CStarAlgebra.Bidual

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {B : Type v} [NonUnitalCStarAlgebra B]

/-- Pullback of source functionals respects their involution whenever the
underlying bounded map respects the source involutions. -/
theorem dualStar_comp (T : A →L[ℂ] B)
    (hT : ∀ a : A, T (star a) = star (T a)) (f : StrongDual ℂ B) :
    dualStar (f.comp T) = (dualStar f).comp T := by
  ext a
  change star (f (T (star a))) = star (f (star (T a)))
  rw [hT a]

/-- The literal bidual functor preserves the explicit involution. -/
theorem bidualMap_bidualStar (T : A →L[ℂ] B)
    (hT : ∀ a : A, T (star a) = star (T a))
    (F : StrongDual ℂ (StrongDual ℂ A)) :
    bidualMap T (bidualStar F) = bidualStar (bidualMap T F) := by
  ext f
  change star (F (dualStar (f.comp T))) = star (F ((dualStar f).comp T))
  rw [dualStar_comp T hT f]

/-- Weak-star continuity of the literal involution for non-unital algebras,
with the original strong dual as predual. -/
theorem continuous_bidualStar :
    Continuous (fun F : WeakDual ℂ (StrongDual ℂ A) =>
      StrongDual.toWeakDual (bidualStar (WeakDual.toStrongDual F))) := by
  apply WeakDual.continuous_of_continuous_eval
  intro f
  change Continuous (fun F : WeakDual ℂ (StrongDual ℂ A) => star (F (dualStar f)))
  exact (WeakDual.eval_continuous (dualStar f)).star

end MathlibAnnex.Analysis.CStarAlgebra.Bidual
