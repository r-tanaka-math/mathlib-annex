import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.Kernel

/-!
Typed consumers of the constructed central kernel for a nondegenerate
representation of an arbitrary nonunital C*-algebra. No irreducibility,
surjectivity, separability or nonzero-Hilbert-space premise is supplied.
-/

set_option autoImplicit false
noncomputable section

open MathlibAnnex.RepresentedBidual
open MathlibAnnex.Analysis.CStarAlgebra

universe u v

section Ordered

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    ∃ p : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra,
      star p = p ∧ p * p = p ∧ (∀ T, p * T = T * p) ∧
      (∀ T, envelopingRepresentationExtension pi hnd T = 0 ↔ p * T = 0) := by
  refine ⟨envelopingRepresentationSupportProjection pi hnd,
    envelopingRepresentationSupportProjection_star pi hnd,
    envelopingRepresentationSupportProjection_idem pi hnd,
    envelopingRepresentationSupportProjection_central pi hnd, ?_⟩
  intro T
  exact envelopingRepresentationExtension_eq_zero_iff (pi := pi) (hnd := hnd) T

example (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    ∃ p : StrongDual ℂ (StrongDual ℂ A),
      bidualStar p = p ∧ arensProduct p p = p ∧
      (∀ F, arensProduct p F = arensProduct F p) ∧
      (∀ F, extension pi F = 0 ↔ arensProduct p F = 0) := by
  refine ⟨bidualRepresentationSupportProjection pi hnd,
    bidualRepresentationSupportProjection_star pi hnd,
    bidualRepresentationSupportProjection_idem pi hnd,
    bidualRepresentationSupportProjection_central pi hnd, ?_⟩
  intro F
  exact extension_eq_zero_iff_arensProduct_supportProjection (pi := pi) (hnd := hnd) F

example (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    ‖bidualRepresentationSupportProjection pi hnd‖ ≤ 1 :=
  norm_bidualRepresentationSupportProjection_le pi hnd

example (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) (x : H) :
    extension pi (bidualRepresentationSupportProjection pi hnd) x = x := by
  rw [extension_bidualRepresentationSupportProjection]
  rfl

example (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (F : StrongDual ℂ (StrongDual ℂ A)) (hF : extension pi F = 0) :
    arensProduct F (bidualRepresentationSupportProjection pi hnd) = 0 := by
  rw [← bidualRepresentationSupportProjection_central]
  exact (extension_eq_zero_iff_arensProduct_supportProjection pi hnd F).mp hF

/-- A zero represented Hilbert space has zero support; no nontriviality
condition is required by the construction. -/
example [Subsingleton H] (pi : NonUnitalCStarRepresentation A H)
    (hnd : pi.IsNondegenerate) : bidualRepresentationSupportProjection pi hnd = 0 := by
  have hzero : extension pi (bidualRepresentationSupportProjection pi hnd) = 0 :=
    by
      ext x
      exact Subsingleton.elim _ _
  have hp := (extension_eq_zero_iff_arensProduct_supportProjection pi hnd
    (bidualRepresentationSupportProjection pi hnd)).mp hzero
  simpa only [bidualRepresentationSupportProjection_idem] using hp

end Ordered

/-- The order interface is instantiated from Mathlib for an arbitrary
nonunital C*-algebra; no extra order hypothesis is imposed on the user. -/
example (A : Type u) [NonUnitalCStarAlgebra A]
    (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    letI : PartialOrder A := _root_.CStarAlgebra.spectralOrder A
    letI : StarOrderedRing A := _root_.CStarAlgebra.spectralOrderedRing A
    ∃ p : StrongDual ℂ (StrongDual ℂ A),
      bidualStar p = p ∧ arensProduct p p = p ∧
      (∀ F, arensProduct p F = arensProduct F p) ∧
      (∀ F, extension pi F = 0 ↔ arensProduct p F = 0) := by
  letI : PartialOrder A := _root_.CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := _root_.CStarAlgebra.spectralOrderedRing A
  exact ⟨bidualRepresentationSupportProjection pi hnd,
    bidualRepresentationSupportProjection_star pi hnd,
    bidualRepresentationSupportProjection_idem pi hnd,
    bidualRepresentationSupportProjection_central pi hnd,
    extension_eq_zero_iff_arensProduct_supportProjection pi hnd⟩
