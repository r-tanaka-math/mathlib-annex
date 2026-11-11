import MathlibAnnex.Analysis.CStarAlgebra.TypeI.PositiveBimodule

/-! Typed consumers for the actual pointwise-WOT extension family.
 -/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open MathlibAnnex.Analysis.CStarAlgebra
open scoped CStarAlgebra ComplexOrder InnerProduct

universe u v w

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (r : ℝ) : IsCompact {T : H →WOT[ℂ] H | ‖T.toCLM‖ ≤ r} :=
  isCompact_wot_norm_le r

example : IsClosed {T : H →WOT[ℂ] H | 0 ≤ T.toCLM} := isClosed_wot_nonneg

example : IsCompact (positiveUnitalMapSet (A := A) (H := H)) :=
  isCompact_positiveUnitalMapSet

example : Convex ℝ (positiveUnitalMapSet (A := A) (H := H)) :=
  convex_positiveUnitalMapSet

example (f : A → H →WOT[ℂ] H) (hf : f ∈ positiveUnitalMapSet) :
    positiveUnitalMapOfMem f hf 1 = 1 := positiveUnitalMapOfMem_one f hf

example (f : A → H →WOT[ℂ] H) (hf : f ∈ positiveUnitalMapSet) (a : A) :
    ‖positiveUnitalMapOfMem f hf a‖ ≤ 4 * ‖a‖ :=
  norm_le_four_of_mem_positiveUnitalMapSet hf a

example {ι : Type w} (l : Filter ι) [l.NeBot]
    (P : ι → A →P[ℂ] (H →L[ℂ] H)) (hP : ∀ i, P i 1 = 1) :
    ∃ f ∈ positiveUnitalMapSet (A := A) (H := H),
      MapClusterPt f l (fun i a => ContinuousLinearMapWOT.ofCLM (P i a)) :=
  exists_mapClusterPt_positiveUnitalMapSet l P hP

variable (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
variable (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra)

example : IsCompact (positiveBimoduleExtensionSet D M sigma) :=
  isCompact_positiveBimoduleExtensionSet D M sigma

example : Convex ℝ (positiveBimoduleExtensionSet D M sigma) :=
  convex_positiveBimoduleExtensionSet D M sigma

example (f : A → H →WOT[ℂ] H) (hf : f ∈ positiveBimoduleExtensionSet D M sigma)
    (d : D) : positiveBimoduleExtensionOfMem D M sigma f hf (d : A) = sigma d :=
  positiveBimoduleExtensionOfMem_restrict D M sigma f hf d

example (f : A → H →WOT[ℂ] H) (hf : f ∈ positiveBimoduleExtensionSet D M sigma)
    (d e : D) (a : A) :
    positiveBimoduleExtensionOfMem D M sigma f hf ((d : A) * a * (e : A)) =
      sigma d * positiveBimoduleExtensionOfMem D M sigma f hf a * sigma e :=
  positiveBimoduleExtensionOfMem_mul_mul D M sigma f hf d e a

example (hne : (positiveBimoduleExtensionSet D M sigma).Nonempty) :
    ((positiveBimoduleExtensionSet D M sigma).extremePoints ℝ).Nonempty :=
  extremePoints_positiveBimoduleExtensionSet_nonempty D M sigma hne

example [IsClosed (D : Set A)] [PartialOrder D] [StarOrderedRing D]
    (xi : H) (hxi : ‖xi‖ = 1)
    (hcyclic : DenseRange
      (StarAlgHom.orbitMap (M.toStarSubalgebra.subtype.comp sigma) xi))
    (E : (H →L[ℂ] H) →ₚ[ℂ] M.toStarSubalgebra)
    (hED : ∀ d : D, E (sigma d : H →L[ℂ] H) = sigma d)
    (hEbi : ∀ (d e : D) (T : H →L[ℂ] H),
      E ((sigma d : H →L[ℂ] H) * T * (sigma e : H →L[ℂ] H)) =
        sigma d * E T * sigma e) :
    (positiveBimoduleExtensionSet D M sigma).Nonempty :=
  positiveBimoduleExtensionSet_nonempty_of_positive_map D M sigma
    (M.toStarSubalgebra.subtype.comp sigma) xi hxi hcyclic E hED hEbi
