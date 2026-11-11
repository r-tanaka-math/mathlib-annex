import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.Representation

/-! Typed consumers of the nondegenerate representation extension.
 -/

set_option autoImplicit false
noncomputable section

open MathlibAnnex.RepresentedBidual
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra.EnvelopingRepresentationConsumers

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    extension pi (bidualUnit (A := A)) = 1 :=
  extension_bidualUnit_of_isNondegenerate pi hnd

example (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) (a : A) :
    (envelopingRepresentationExtension pi hnd (envelopingInclusion (A := A) a) :
      H →L[ℂ] H) = pi a :=
  envelopingRepresentationExtension_inclusion pi hnd a

/-- The actual target is the generated VN subtype, and the map is a unital
star homomorphism in Mathlib's usual sense. -/
example (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (S T : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) :
    envelopingRepresentationExtension pi hnd (S * T) =
        envelopingRepresentationExtension pi hnd S * envelopingRepresentationExtension pi hnd T ∧
      envelopingRepresentationExtension pi hnd (star S) =
        star (envelopingRepresentationExtension pi hnd S) ∧
      envelopingRepresentationExtension pi hnd 1 = 1 :=
  ⟨map_mul (envelopingRepresentationExtension pi hnd) S T,
    map_star (envelopingRepresentationExtension pi hnd) S,
    map_one (envelopingRepresentationExtension pi hnd)⟩

example (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    Continuous (fun F : WeakDual ℂ (StrongDual ℂ A) =>
      ContinuousLinearMapWOT.ofCLM
        (envelopingRepresentationExtension pi hnd
          (bidualEnvelopingEquiv (A := A) (WeakDual.toStrongDual F)) : H →L[ℂ] H)) :=
  envelopingRepresentationExtension_weakStar_wot pi hnd

example (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    Continuous (fun T :
      {T : UniversalHilbertSpace A →WOT[ℂ] UniversalHilbertSpace A //
        T.toCLM ∈ envelopingVonNeumannAlgebra (A := A)} =>
      ContinuousLinearMapWOT.ofCLM
        (envelopingRepresentationExtension pi hnd ⟨T.val.toCLM, T.property⟩ : H →L[ℂ] H)) :=
  continuous_envelopingRepresentationExtension_wot pi hnd

example (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (T : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra → (H →L[ℂ] H))
    (hcont : Continuous (fun F : WeakDual ℂ (StrongDual ℂ A) =>
      ContinuousLinearMapWOT.ofCLM
        (T (bidualEnvelopingEquiv (A := A) (WeakDual.toStrongDual F)))))
    (hsource : ∀ a : A, T (envelopingInclusion (A := A) a) = pi a) :
    T = fun S => (envelopingRepresentationExtension pi hnd S : H →L[ℂ] H) :=
  envelopingRepresentationExtension_unique pi hnd T hcont hsource

end MathlibAnnex.Analysis.CStarAlgebra.EnvelopingRepresentationConsumers
