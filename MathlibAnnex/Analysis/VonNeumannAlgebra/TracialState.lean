import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import MathlibAnnex.Analysis.CStarAlgebra.GNS.TracialFaithfulness
import MathlibAnnex.Analysis.CStarAlgebra.State.Basic
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.VectorDomination

/-!
# Tracial vector functionals on a weakly dense represented algebra

The ambient vector functional and its weak-operator continuity are reused
from `TensorAveraging.VectorDomination`.  The trace identity extends through
weak-operator closure one variable at a time.  No joint continuity of
multiplication, and no assertion about arbitrary normal functionals, is used.

For a norm-closed von Neumann algebra, the faithful-state assertion is a
subtype application of the existing tracial cyclic GNS faithfulness theorem.
The norm-closedness hypothesis supplies the standard C-star algebra and
star-order instances; this file registers no competing subtype instances.
-/

set_option autoImplicit false

open Set Topology
open scoped CStarAlgebra ComplexOrder InnerProduct

open MathlibAnnex.CStarAlgebra.TensorAveraging
open MathlibAnnex.Analysis.CStarAlgebra

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

/-- A vector-functional commutation identity with one fixed operator passes
to the weak-operator closure of an arbitrary set of operators. -/
theorem vectorFunctional_mul_eq_mul_of_mem_wotClosure
    (s : Set (H →L[ℂ] H)) (ξ : H) (Q : H →L[ℂ] H)
    (hs : ∀ P ∈ s, operatorVectorState H ξ (P * Q) =
      operatorVectorState H ξ (Q * P))
    {T : H →L[ℂ] H}
    (hT : ContinuousLinearMapWOT.ofCLM T ∈
      closure (ContinuousLinearMapWOT.ofCLM '' s)) :
    operatorVectorState H ξ (T * Q) = operatorVectorState H ξ (Q * T) := by
  have hleft : Continuous (fun U : H →WOT[ℂ] H ↦
      operatorVectorState H ξ (U.toCLM * Q)) :=
    (operatorVectorState_wotContinuous H ξ).comp
      (ContinuousLinearMapWOT.continuous_precomp (ContinuousLinearMapWOT.ofCLM Q))
  have hright : Continuous (fun U : H →WOT[ℂ] H ↦
      operatorVectorState H ξ (Q * U.toCLM)) :=
    (operatorVectorState_wotContinuous H ξ).comp
      (ContinuousLinearMapWOT.continuous_postcomp (ContinuousLinearMapWOT.ofCLM Q))
  have hclosed : IsClosed {U : H →WOT[ℂ] H |
      operatorVectorState H ξ (U.toCLM * Q) =
        operatorVectorState H ξ (Q * U.toCLM)} :=
    isClosed_eq hleft hright
  have hsubset : ContinuousLinearMapWOT.ofCLM '' s ⊆
      {U : H →WOT[ℂ] H | operatorVectorState H ξ (U.toCLM * Q) =
        operatorVectorState H ξ (Q * U.toCLM)} := by
    rintro _ ⟨P, hP, rfl⟩
    exact hs P hP
  exact closure_minimal hsubset hclosed hT

end ContinuousLinearMap

namespace VonNeumannAlgebra

/-- Traciality of a vector functional extends from a weakly dense source
set to the von Neumann algebra.  Each use of continuity fixes one factor. -/
theorem vectorFunctional_mul_comm_of_wotDense
    (M : VonNeumannAlgebra H) (s : Set (H →L[ℂ] H)) (ξ : H)
    (hdense : ∀ T ∈ M, ContinuousLinearMapWOT.ofCLM T ∈
      closure (ContinuousLinearMapWOT.ofCLM '' s))
    (htrace : ∀ P ∈ s, ∀ Q ∈ s, operatorVectorState H ξ (P * Q) =
      operatorVectorState H ξ (Q * P))
    {P Q : H →L[ℂ] H} (hP : P ∈ M) (hQ : Q ∈ M) :
    operatorVectorState H ξ (P * Q) = operatorVectorState H ξ (Q * P) := by
  have hfirst (S : H →L[ℂ] H) (hS : S ∈ s) :
      operatorVectorState H ξ (Q * S) = operatorVectorState H ξ (S * Q) :=
    ContinuousLinearMap.vectorFunctional_mul_eq_mul_of_mem_wotClosure s ξ S
      (fun T hT ↦ htrace T hT S hS) (hdense Q hQ)
  exact ContinuousLinearMap.vectorFunctional_mul_eq_mul_of_mem_wotClosure s ξ Q
    (fun S hS ↦ (hfirst S hS).symm) (hdense P hP)

/-- A tracial cyclic vector functional on the concrete algebra detects
every nonzero star-square.  The proof reuses tracial GNS faithfulness on
the canonical inclusion of the norm-closed star subalgebra. -/
theorem vectorFunctional_star_mul_self_eq_zero_iff
    (M : VonNeumannAlgebra H)
    [IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H))]
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (htrace : ∀ P ∈ M, ∀ Q ∈ M, operatorVectorState H ξ (P * Q) =
      operatorVectorState H ξ (Q * P))
    (hcyclic : DenseRange (fun a : M.toStarSubalgebra ↦ (a : H →L[ℂ] H) ξ))
    {T : H →L[ℂ] H} (hT : T ∈ M) :
    operatorVectorState H ξ (star T * T) = 0 ↔ T = 0 := by
  constructor
  · intro hnull
    let ρ : Representation M.toStarSubalgebra H := M.toStarSubalgebra.subtype
    let f : M.toStarSubalgebra →ₚ[ℂ] ℂ := vectorPositiveFunctional ρ ξ hξ
    have hf (a b : M.toStarSubalgebra) : f (a * b) = f (b * a) :=
      htrace (a : H →L[ℂ] H) a.property (b : H →L[ℂ] H) b.property
    have hfaithful : Function.Injective ρ := by
      intro a b hab
      exact Subtype.ext hab
    have hzero : (⟨T, hT⟩ : M.toStarSubalgebra) = 0 :=
      eq_zero_of_apply_star_mul_self_eq_zero_of_tracial f hf ρ ξ
        (fun _ ↦ rfl) hcyclic hfaithful hnull
    exact congrArg (fun a : M.toStarSubalgebra ↦ (a : H →L[ℂ] H)) hzero
  · rintro rfl
    simp

end VonNeumannAlgebra
