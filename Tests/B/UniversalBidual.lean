import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.UniversalBidual

/-!
Typed consumers of the actual all-state coefficient realization and literal
bidual identification. These are proof-bearing consumers, including the
onto and reverse-topology directions.
-/

set_option autoImplicit false
noncomputable section

open Set
open MathlibAnnex.RepresentedBidual
open scoped CStarAlgebra InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra.UniversalBidualConsumers

universe u v

section Ordered

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]

/-- No irreducibility or positivity is assumed for this arbitrary bounded
functional. The bound is the exact dual norm bound needed for the inverse. -/
example (f : StrongDual ℂ A) :
    ∃ x y : UniversalHilbertSpace A,
      (∀ a : A, inner ℂ y (universalRepresentation a x) = f a) ∧
      ‖x‖ * ‖y‖ ≤ ‖f‖ := by
  obtain ⟨x, y, h, hn⟩ := exists_universalRepresentation_coefficient f
  exact ⟨x, y, fun a => congrArg (fun g : StrongDual ℂ A => g a) h, hn⟩

/-- The scaled unit-vector form retains the original functional norm. -/
example (f : StrongDual ℂ A) (hf : f ≠ 0) :
    ∃ x y : UniversalHilbertSpace A, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      f = (‖f‖ : ℂ) •
        NonUnitalCStarRepresentation.matrixCoefficient (universalRepresentation (A := A)) x y :=
  exists_unit_universalRepresentation_coefficient f hf

/-- Exact norm preservation on the literal, normed double dual. -/
example (F : StrongDual ℂ (StrongDual ℂ A)) :
    ‖extension (universalRepresentation (A := A)) F‖ = ‖F‖ :=
  norm_extension_universalRepresentation F

/-- Faithfulness applies to arbitrary bidual elements. -/
example (F G : StrongDual ℂ (StrongDual ℂ A))
    (h : extension (universalRepresentation (A := A)) F =
      extension (universalRepresentation (A := A)) G) : F = G :=
  extension_universalRepresentation_injective h

/-- The existing extension still agrees with the exact canonical Banach
embedding on every original element. -/
example (a : A) :
    extension (universalRepresentation (A := A))
      (NormedSpace.inclusionInDoubleDual ℂ A a) = universalRepresentation a :=
  extension_canonical (universalRepresentation (A := A)) a

/-- Explicit reverse weak-star continuity, with no boundedness premise. -/
example {X : Type v} [TopologicalSpace X]
    (F : X → WeakDual ℂ (StrongDual ℂ A))
    (h : Continuous (fun t => ContinuousLinearMapWOT.ofCLM
      (extension (universalRepresentation (A := A)) (WeakDual.toStrongDual (F t))))) :
    Continuous F :=
  (continuous_extension_universalRepresentation_iff F).mp h

/-- The converse direction uses the inherited represented extension. -/
example {X : Type v} [TopologicalSpace X]
    (F : X → WeakDual ℂ (StrongDual ℂ A)) (h : Continuous F) :
    Continuous (fun t => ContinuousLinearMapWOT.ofCLM
      (extension (universalRepresentation (A := A)) (WeakDual.toStrongDual (F t)))) :=
  (continuous_extension_universalRepresentation_iff F).mpr h

/-- The inverse is an actual bounded linear functional on the original
dual; its coefficient recovery is consumed on an arbitrary vector test. -/
example (T : UniversalHilbertSpace A →L[ℂ] UniversalHilbertSpace A)
    (hT : ContinuousLinearMapWOT.ofCLM T ∈ closure (Set.range (fun a : A =>
      ContinuousLinearMapWOT.ofCLM (universalRepresentation (A := A) a))))
    (x : UniversalHilbertSpace A) (g : StrongDual ℂ (UniversalHilbertSpace A)) :
    bidualOfUniversalWOTClosure T hT (coefficient (universalRepresentation (A := A)) x g) =
      g (T x) :=
  bidualOfUniversalWOTClosure_coefficient T hT x g

/-- The WOT-closure inverse reconstructs the original operator exactly. -/
example (T : UniversalHilbertSpace A →L[ℂ] UniversalHilbertSpace A)
    (hT : ContinuousLinearMapWOT.ofCLM T ∈ closure (Set.range (fun a : A =>
      ContinuousLinearMapWOT.ofCLM (universalRepresentation (A := A) a)))) :
    extension (universalRepresentation (A := A)) (bidualOfUniversalWOTClosure T hT) = T :=
  extension_bidualOfUniversalWOTClosure T hT

/-- Surjectivity is on the concrete envelope of the original algebra. The
consumer does not insert a unitization or a separability hypothesis. -/
example (T : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) :
    ∃ F : StrongDual ℂ (StrongDual ℂ A),
      extension (universalRepresentation (A := A)) F =
        (T : UniversalHilbertSpace A →L[ℂ] UniversalHilbertSpace A) :=
  exists_extension_eq_of_mem_envelopingVonNeumannAlgebra (A := A) T.val T.property

end Ordered

set_option maxHeartbeats 1500000 in
/-- The order-interface assumptions are instantiated from the existing
Mathlib spectral order for an arbitrary nonunital C*-algebra. -/
example (A : Type u) [NonUnitalCStarAlgebra A] (F : StrongDual ℂ (StrongDual ℂ A)) :
    letI : PartialOrder A := _root_.CStarAlgebra.spectralOrder A
    letI : StarOrderedRing A := _root_.CStarAlgebra.spectralOrderedRing A
    ‖extension (universalRepresentation (A := A)) F‖ = ‖F‖ := by
  letI : PartialOrder A := _root_.CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := _root_.CStarAlgebra.spectralOrderedRing A
  exact norm_extension_universalRepresentation (A := A) F

end MathlibAnnex.Analysis.CStarAlgebra.UniversalBidualConsumers
