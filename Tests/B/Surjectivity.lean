import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.Surjectivity

set_option autoImplicit false

open Set
open MathlibAnnex.Analysis.CStarAlgebra MathlibAnnex.RepresentedBidual

section

variable {A H : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)

example (r : ℝ) :
    IsCompact ((fun T : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra =>
      ContinuousLinearMapWOT.ofCLM
        (envelopingRepresentationExtension pi hnd T : H →L[ℂ] H)) ''
      Metric.closedBall 0 r) :=
  isCompact_wot_envelopingRepresentationExtension_closedBall pi hnd r

example (r : ℝ) :
    IsClosed ((fun T : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra =>
      ContinuousLinearMapWOT.ofCLM
        (envelopingRepresentationExtension pi hnd T : H →L[ℂ] H)) ''
      Metric.closedBall 0 r) :=
  isClosed_wot_envelopingRepresentationExtension_closedBall pi hnd r

example (T : (VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra)
    (hT : IsSelfAdjoint T) :
    ∃ S : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra,
      IsSelfAdjoint S ∧ envelopingRepresentationExtension pi hnd S = T ∧ ‖S‖ ≤ ‖T‖ :=
  exists_selfAdjoint_envelopingRepresentationExtension_preimage_norm_le pi hnd T hT

example (T : (VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra) :
    ∃ S : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra,
      envelopingRepresentationExtension pi hnd S = T ∧ ‖S‖ ≤ 2 * ‖T‖ :=
  exists_envelopingRepresentationExtension_preimage_norm_le_two_mul pi hnd T

example : Function.Surjective (envelopingRepresentationExtension pi hnd) :=
  surjective_envelopingRepresentationExtension pi hnd

example (T : H →L[ℂ] H) (hT : T ∈ VonNeumannAlgebra.generated pi.unitization.range) :
    ∃ F : StrongDual ℂ (StrongDual ℂ A), extension pi F = T ∧ ‖F‖ ≤ 2 * ‖T‖ :=
  exists_extension_preimage_norm_le_two_mul_of_isNondegenerate pi hnd T hT

example (S : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) :
    ‖envelopingRepresentationSupportProjection pi hnd * S‖ =
      ‖envelopingRepresentationExtension pi hnd S‖ :=
  norm_envelopingRepresentationSupportProjection_mul pi hnd S

example (T : (VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra) :
    ∃ S : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra,
      envelopingRepresentationExtension pi hnd S = T ∧ ‖S‖ = ‖T‖ :=
  exists_envelopingRepresentationExtension_preimage_norm_eq pi hnd T

example (T : H →L[ℂ] H) (hT : T ∈ VonNeumannAlgebra.generated pi.unitization.range) :
    ∃ F : StrongDual ℂ (StrongDual ℂ A), extension pi F = T ∧ ‖F‖ = ‖T‖ :=
  exists_extension_preimage_norm_eq_of_isNondegenerate pi hnd T hT

example : Set.range (extension pi) =
    (VonNeumannAlgebra.generated pi.unitization.range : Set (H →L[ℂ] H)) :=
  range_extension_of_isNondegenerate pi hnd

example (r : ℝ) :
    envelopingRepresentationExtension pi hnd '' Metric.closedBall 0 r = Metric.closedBall 0 r :=
  image_envelopingRepresentationExtension_closedBall pi hnd r

end
