import MathlibAnnex.Analysis.VonNeumannAlgebra.TracialState
import Mathlib.Tactic.LinearCombination

/-!
# Factors obtained from a unique trace on a weakly dense source

For a central element `z`, put `c = φ z`.  The continuous functional
`a ↦ φ (z * π a) + (1 - c) * τ a` is a normalized complex trace on the
source.  Uniqueness identifies it with `τ`, and weak-operator density
extends `φ (z * T) = c * φ T` to the whole represented algebra.
Faithfulness at `T = star (z - c • 1)` then gives `z = c • 1`.

The auxiliary functional is not assumed positive.  Accordingly, the
uniqueness hypothesis ranges over all normalized continuous complex traces.
The cyclic vector, source representation, and ambient Hilbert space remain
the same throughout the argument.
-/

set_option autoImplicit false

open Set Topology
open scoped CStarAlgebra ComplexOrder InnerProduct

open MathlibAnnex.CStarAlgebra.TensorAveraging
open MathlibAnnex.Analysis.CStarAlgebra

universe u v

namespace VonNeumannAlgebra

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A factor is a nonzero concrete von Neumann algebra whose central
operators are scalar multiples of the identity. -/
def IsFactor (M : VonNeumannAlgebra H) : Prop :=
  (1 : H →L[ℂ] H) ≠ 0 ∧
    ∀ z : H →L[ℂ] H, z ∈ M →
      (∀ a : H →L[ℂ] H, a ∈ M → a * z = z * a) →
        ∃ c : ℂ, z = c • (1 : H →L[ℂ] H)

/-- The von Neumann algebra in a cyclic trace representation is a factor
when its weakly dense C-star source has a unique normalized continuous
complex trace.  Norm-closedness is supplied through the standard subtype
instance; it is separate from the mathematical trace and density inputs. -/
theorem isFactor_of_unique_trace_of_wotDense
    {A : Type v} [CStarAlgebra A]
    (M : VonNeumannAlgebra H)
    [IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H))]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (hξ : ‖ξ‖ = 1)
    (hπ : ∀ a : A, π a ∈ M)
    (hdense : ∀ T ∈ M, ContinuousLinearMapWOT.ofCLM T ∈
      closure (Set.range (fun a : A ↦ ContinuousLinearMapWOT.ofCLM (π a))))
    (hcyclic : DenseRange (fun a : A ↦ π a ξ))
    (τ : A →L[ℂ] ℂ)
    (hτ : ∀ a : A, τ a = operatorVectorState H ξ (π a))
    (hτone : τ 1 = 1)
    (hτtrace : ∀ a b : A, τ (a * b) = τ (b * a))
    (hunique : ∀ f : A →L[ℂ] ℂ, f 1 = 1 →
      (∀ a b : A, f (a * b) = f (b * a)) → f = τ) :
    IsFactor M := by
  have hdense' : ∀ T ∈ M, ContinuousLinearMapWOT.ofCLM T ∈
      closure (ContinuousLinearMapWOT.ofCLM '' Set.range π) := by
    intro T hT
    simpa only [← Set.range_comp, Function.comp_def] using hdense T hT
  have hsource : ∀ P ∈ Set.range π, ∀ Q ∈ Set.range π,
      operatorVectorState H ξ (P * Q) = operatorVectorState H ξ (Q * P) := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    simpa only [hτ, map_mul] using hτtrace a b
  have htrace : ∀ P ∈ M, ∀ Q ∈ M,
      operatorVectorState H ξ (P * Q) = operatorVectorState H ξ (Q * P) := by
    intro P hP Q hQ
    exact vectorFunctional_mul_comm_of_wotDense M (Set.range π) ξ
      hdense' hsource hP hQ
  have hcyclicM : DenseRange
      (fun a : M.toStarSubalgebra ↦ (a : H →L[ℂ] H) ξ) := by
    refine Dense.mono ?_ hcyclic
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨π a, hπ a⟩, rfl⟩
  have hfaithful (T : H →L[ℂ] H) (hT : T ∈ M) :
      operatorVectorState H ξ (star T * T) = 0 → T = 0 :=
    (vectorFunctional_star_mul_self_eq_zero_iff M ξ hξ htrace hcyclicM hT).mp
  have hone : (1 : H →L[ℂ] H) ≠ 0 := by
    intro h
    have hzero : ξ = 0 := by
      simpa using congrArg (fun T : H →L[ℂ] H ↦ T ξ) h
    rw [hzero, norm_zero] at hξ
    exact zero_ne_one hξ
  refine ⟨hone, ?_⟩
  intro z hz hzcomm
  let c : ℂ := operatorVectorState H ξ z
  let f : A →L[ℂ] ℂ :=
    (((innerSL ℂ ξ).comp z).comp
      ((ContinuousLinearMap.apply ℂ H ξ).comp (Representation.continuousLinearMap π))) +
      (1 - c) • τ
  have hf_apply (a : A) :
      f a = operatorVectorState H ξ (z * π a) + (1 - c) * τ a := rfl
  have hf_one : f 1 = 1 := by
    simp only [hf_apply, map_one, hτone, mul_one]
    change c + (1 - c) = 1
    ring
  have hf_trace (a b : A) : f (a * b) = f (b * a) := by
    rw [hf_apply, hf_apply, hτtrace a b]
    congr 1
    simp only [map_mul π]
    calc
      operatorVectorState H ξ (z * (π a * π b)) =
          operatorVectorState H ξ ((z * π a) * π b) := by rw [mul_assoc]
      _ = operatorVectorState H ξ (π b * (z * π a)) :=
        htrace _ (mul_mem hz (hπ a)) _ (hπ b)
      _ = operatorVectorState H ξ (z * (π b * π a)) := by
        rw [← mul_assoc, hzcomm (π b) (hπ b), mul_assoc]
  have hf : f = τ := hunique f hf_one hf_trace
  have hzsource (a : A) :
      operatorVectorState H ξ (z * π a) = c * operatorVectorState H ξ (π a) := by
    have h := congrArg (fun g : A →L[ℂ] ℂ ↦ g a) hf
    simp only [hf_apply, hτ a] at h
    linear_combination h
  have hleft : Continuous (fun T : H →WOT[ℂ] H ↦
      operatorVectorState H ξ (z * T.toCLM)) :=
    (operatorVectorState_wotContinuous H ξ).comp
      (ContinuousLinearMapWOT.continuous_postcomp (ContinuousLinearMapWOT.ofCLM z))
  have hright : Continuous (fun T : H →WOT[ℂ] H ↦
      c * operatorVectorState H ξ T.toCLM) :=
    continuous_const.mul (operatorVectorState_wotContinuous H ξ)
  have hclosed : IsClosed {T : H →WOT[ℂ] H |
      operatorVectorState H ξ (z * T.toCLM) =
        c * operatorVectorState H ξ T.toCLM} := isClosed_eq hleft hright
  have hsubset : Set.range (fun a : A ↦ ContinuousLinearMapWOT.ofCLM (π a)) ⊆
      {T : H →WOT[ℂ] H | operatorVectorState H ξ (z * T.toCLM) =
        c * operatorVectorState H ξ T.toCLM} := by
    rintro _ ⟨a, rfl⟩
    exact hzsource a
  have hzall (T : H →L[ℂ] H) (hT : T ∈ M) :
      operatorVectorState H ξ (z * T) = c * operatorVectorState H ξ T :=
    closure_minimal hsubset hclosed (hdense T hT)
  let w : H →L[ℂ] H := z - c • 1
  have hw : w ∈ M :=
    sub_mem hz (M.toStarSubalgebra.smul_mem (one_mem _) c)
  have hstarw : star w ∈ M := star_mem hw
  have hnull : operatorVectorState H ξ (w * star w) = 0 := by
    change operatorVectorState H ξ ((z - c • 1) * star w) = 0
    rw [sub_mul, smul_mul_assoc, one_mul, map_sub, map_smul]
    exact sub_eq_zero.mpr (hzall (star w) hstarw)
  have hstarzero : star w = 0 := hfaithful (star w) hstarw (by
    simpa only [star_star] using hnull)
  have hwzero : w = 0 := by
    simpa only [star_star, star_zero] using congrArg star hstarzero
  exact ⟨c, sub_eq_zero.mp hwzero⟩

end VonNeumannAlgebra
