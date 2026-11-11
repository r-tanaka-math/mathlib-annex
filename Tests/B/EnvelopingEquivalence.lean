import MathlibAnnex.Analysis.CStarAlgebra.Bidual.EnvelopingEquivalence

/-! Direct typed consumers of the literal-bidual identification.
These are source consumers, not a record of a Lean run. -/

set_option autoImplicit false
noncomputable section

open MathlibAnnex.Analysis.CStarAlgebra MathlibAnnex.RepresentedBidual
open scoped CStarAlgebra

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]

example : StrongDual ℂ (StrongDual ℂ A) ≃ₗᵢ[ℂ]
    (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra :=
  bidualEnvelopingEquiv (A := A)

example (F G : StrongDual ℂ (StrongDual ℂ A)) :
    bidualEnvelopingEquiv (A := A) (arensProduct F G) =
      bidualEnvelopingEquiv (A := A) F * bidualEnvelopingEquiv (A := A) G :=
  bidualEnvelopingEquiv_arensProduct (A := A) F G

example (F : StrongDual ℂ (StrongDual ℂ A)) :
    bidualEnvelopingEquiv (A := A) (bidualStar F) =
      star (bidualEnvelopingEquiv (A := A) F) :=
  bidualEnvelopingEquiv_bidualStar (A := A) F

example (F : StrongDual ℂ (StrongDual ℂ A)) :
    ‖bidualEnvelopingEquiv (A := A) F‖ = ‖F‖ :=
  (bidualEnvelopingEquiv (A := A)).norm_map F

example (a : A) :
    bidualEnvelopingEquiv (A := A) (NormedSpace.inclusionInDoubleDual ℂ A a) =
      envelopingInclusion (A := A) a :=
  bidualEnvelopingEquiv_canonical (A := A) a

example (a : A) (f : StrongDual ℂ A) :
    (bidualEnvelopingEquiv (A := A)).symm (envelopingInclusion (A := A) a) f = f a :=
  bidualEnvelopingEquiv_symm_inclusion_eval (A := A) a f

example (T : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) :
    extension (universalRepresentation (A := A))
      ((bidualEnvelopingEquiv (A := A)).symm T) = T.val :=
  extension_bidualEnvelopingEquiv_symm (A := A) T

example (S T : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) :
    (bidualEnvelopingEquiv (A := A)).symm (S * T) =
      arensProduct ((bidualEnvelopingEquiv (A := A)).symm S)
        ((bidualEnvelopingEquiv (A := A)).symm T) :=
  bidualEnvelopingEquiv_symm_mul (A := A) S T

example (T : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) :
    (bidualEnvelopingEquiv (A := A)).symm (star T) =
      bidualStar ((bidualEnvelopingEquiv (A := A)).symm T) :=
  bidualEnvelopingEquiv_symm_star (A := A) T

example (F : StrongDual ℂ (StrongDual ℂ A)) :
    arensProduct (bidualUnit (A := A)) F = F ∧
      arensProduct F (bidualUnit (A := A)) = F :=
  ⟨arensProduct_bidualUnit_left (A := A) F, arensProduct_bidualUnit_right (A := A) F⟩

example (F : StrongDual ℂ (StrongDual ℂ A)) :
    ‖arensProduct (bidualStar F) F‖ = ‖F‖ * ‖F‖ :=
  Bidual.norm_arensStar_square (A := A) F

example : WeakDual ℂ (StrongDual ℂ A) ≃ₜ
    {T : UniversalHilbertSpace A →WOT[ℂ] UniversalHilbertSpace A //
      T.toCLM ∈ envelopingVonNeumannAlgebra (A := A)} :=
  bidualEnvelopingWeakStarEquiv (A := A)

example : Continuous (bidualEnvelopingWeakStarEquiv (A := A)) :=
  (bidualEnvelopingWeakStarEquiv (A := A)).continuous

example : Continuous (bidualEnvelopingWeakStarEquiv (A := A)).symm :=
  (bidualEnvelopingWeakStarEquiv (A := A)).symm.continuous

example (F : WeakDual ℂ (StrongDual ℂ A)) :
    (bidualEnvelopingWeakStarEquiv (A := A) F).val.toCLM =
      (bidualEnvelopingEquiv (A := A) (WeakDual.toStrongDual F)).val :=
  bidualEnvelopingWeakStarEquiv_apply (A := A) F

example [Subsingleton A] (F : StrongDual ℂ (StrongDual ℂ A)) : F = 0 := by
  letI : Subsingleton (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra :=
    subsingleton_envelopingVonNeumannAlgebra (A := A)
  exact (bidualEnvelopingEquiv (A := A)).injective (Subsingleton.elim _ _)

set_option maxHeartbeats 1500000 in
/-- The ordered presentation is available for every nonunital C*-algebra;
no additional order-existence premise is needed from a consumer. -/
example {D : Type u} [NonUnitalCStarAlgebra D] :
    letI : PartialOrder D := _root_.CStarAlgebra.spectralOrder D
    letI : StarOrderedRing D := _root_.CStarAlgebra.spectralOrderedRing D
    StrongDual ℂ (StrongDual ℂ D) ≃ₗᵢ[ℂ]
      (envelopingVonNeumannAlgebra (A := D)).toStarSubalgebra :=
  @bidualEnvelopingEquiv D _ (_root_.CStarAlgebra.spectralOrder D)
    (_root_.CStarAlgebra.spectralOrderedRing D)
