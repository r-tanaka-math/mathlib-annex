import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.TypeI
import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.Normality

set_option autoImplicit false

open MathlibAnnex.Analysis.CStarAlgebra MathlibAnnex.RepresentedBidual
open scoped CStarAlgebra

section

variable {A H K : Type*} [NonUnitalCStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

attribute [local instance 100] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

variable (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)

example (S : envelopingRepresentationCorner pi hnd)
    (hS : (envelopingVonNeumannAlgebra (A := A)).IsAbelianProjection S) :
    (VonNeumannAlgebra.generated pi.unitization.range).IsAbelianProjection
      (envelopingRepresentationCornerEquiv pi hnd S) :=
  isAbelianProjection_envelopingRepresentationCornerEquiv pi hnd S hS

example (hA : IsTypeIBidual A) :
    (VonNeumannAlgebra.generated pi.unitization.range).IsTypeI :=
  hA.isTypeI_generated pi hnd

example (hA : IsTypeIBidual A) (N : VonNeumannAlgebra K)
    (e : (VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra ≃⋆ₐ[ℂ]
      N.toStarSubalgebra) : N.IsTypeI :=
  hA.isTypeI_of_generatedEquiv pi hnd N e

example (hA : IsTypeIBidual A)
    (s : Set (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra)
    (hne : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hpos : ∀ a ∈ s, 0 ≤ a) (hbdd : BddAbove s)
    (T : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) (hT : IsLUB s T) :
    (VonNeumannAlgebra.generated pi.unitization.range).IsTypeI ∧
      IsLUB (envelopingRepresentationExtension pi hnd '' s)
        (envelopingRepresentationExtension pi hnd T) :=
  ⟨hA.isTypeI_generated pi hnd,
    isLUB_image_envelopingRepresentationExtension pi hnd s hne hdir hpos hbdd T hT⟩

example (hnz : pi.IsNonzero) : bidualRepresentationSupportProjection pi hnd ≠ 0 :=
  bidualRepresentationSupportProjection_ne_zero pi hnd hnz

example (hIII : (VonNeumannAlgebra.generated pi.unitization.range).IsTypeIII)
    (Q : StrongDual ℂ (StrongDual ℂ A))
    (hQQ : arensProduct Q Q = Q) (hQstar : bidualStar Q = Q)
    (hQP : arensProduct Q (bidualRepresentationSupportProjection pi hnd) = Q)
    (hcomm : ∀ X Y : StrongDual ℂ (StrongDual ℂ A),
      arensProduct Q X = X → arensProduct X Q = X →
      arensProduct Q Y = Y → arensProduct Y Q = Y →
      arensProduct X Y = arensProduct Y X) : Q = 0 :=
  eq_zero_of_bidualProjection_mul_support_of_isTypeIII pi hnd hIII Q hQQ hQstar hQP hcomm

example (hnz : pi.IsNonzero)
    (hIII : (VonNeumannAlgebra.generated pi.unitization.range).IsTypeIII) :
    ∃ P : StrongDual ℂ (StrongDual ℂ A),
      arensProduct P P = P ∧ bidualStar P = P ∧ P ≠ 0 ∧
      ∀ Q : StrongDual ℂ (StrongDual ℂ A),
        arensProduct Q Q = Q → bidualStar Q = Q → arensProduct Q P = Q →
        (∀ X Y : StrongDual ℂ (StrongDual ℂ A),
          arensProduct Q X = X → arensProduct X Q = X →
          arensProduct Q Y = Y → arensProduct Y Q = Y →
          arensProduct X Y = arensProduct Y X) → Q = 0 := by
  refine ⟨bidualRepresentationSupportProjection pi hnd,
    bidualRepresentationSupportProjection_idem pi hnd,
    bidualRepresentationSupportProjection_star pi hnd,
    bidualRepresentationSupportProjection_ne_zero pi hnd hnz, ?_⟩
  exact eq_zero_of_bidualProjection_mul_support_of_isTypeIII pi hnd hIII

example (hnz : pi.IsNonzero)
    (hIII : (VonNeumannAlgebra.generated pi.unitization.range).IsTypeIII) :
    ¬ IsTypeIBidual A :=
  not_isTypeIBidual_of_isTypeIII_generated pi hnd hnz hIII

end
