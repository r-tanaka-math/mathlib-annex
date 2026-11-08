import MathlibAnnex.Analysis.VonNeumannAlgebra.NormalFunctional
import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeII1

/-!
# A typed consumer of the complete tracial-factor construction

The inputs are a weakly dense cyclic trace representation, uniqueness of
the normalized continuous trace on its source, and infinite dimension of
the represented algebra. Normality, faithfulness, factoriality and finiteness
are conclusions. This is a generic consumer, independent of any CAR model.
-/

set_option autoImplicit false

open Set Topology
open scoped CStarAlgebra ComplexOrder InnerProduct

open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.CStarAlgebra.TensorAveraging

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example {A : Type v} [CStarAlgebra A]
    (M : VonNeumannAlgebra H) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ξ : H) (hξ : ‖ξ‖ = 1) (hπ : ∀ a : A, π a ∈ M)
    (hdense : ∀ T ∈ M, ContinuousLinearMapWOT.ofCLM T ∈
      closure (Set.range (fun a : A ↦ ContinuousLinearMapWOT.ofCLM (π a))))
    (hcyclic : DenseRange (fun a : A ↦ π a ξ))
    (τ : A →L[ℂ] ℂ) (hτ : ∀ a, τ a = operatorVectorState H ξ (π a))
    (hτone : τ 1 = 1) (hτtrace : ∀ a b, τ (a * b) = τ (b * a))
    (hunique : ∀ f : A →L[ℂ] ℂ, f 1 = 1 →
      (∀ a b, f (a * b) = f (b * a)) → f = τ)
    (hinfinite : ¬ FiniteDimensional ℂ M.toStarSubalgebra) :
    ∃ φ : M.toStarSubalgebra →L[ℂ] ℂ,
      (∀ a, φ a = inner ℂ ξ ((a : H →L[ℂ] H) ξ)) ∧
      φ 1 = 1 ∧
      (∀ a b, φ (a * b) = φ (b * a)) ∧
      (∀ a, φ (star a * a) = 0 ↔ a = 0) ∧
      M.IsNormalPositiveFunctional φ ∧ M.IsFactor ∧ M.IsFinite ∧ M.IsTypeII1 := by
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
    exact M.vectorFunctional_mul_comm_of_wotDense (Set.range π) ξ
      hdense' hsource hP hQ
  have hcyclicM : DenseRange
      (fun a : M.toStarSubalgebra ↦ (a : H →L[ℂ] H) ξ) := by
    refine Dense.mono ?_ hcyclic
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨π a, hπ a⟩, rfl⟩
  have hfaithful (T : H →L[ℂ] H) (hT : T ∈ M) :
      operatorVectorState H ξ (star T * T) = 0 → T = 0 :=
    (M.vectorFunctional_star_mul_self_eq_zero_iff ξ hξ htrace hcyclicM hT).mp
  have hfactor : M.IsFactor :=
    M.isFactor_of_unique_trace_of_wotDense π ξ hξ hπ hdense hcyclic
      τ hτ hτone hτtrace hunique
  have hfinite : M.IsFinite :=
    M.isFinite_of_faithful_tracial (operatorVectorState H ξ).toLinearMap htrace hfaithful
  let φ : M.toStarSubalgebra →L[ℂ] ℂ :=
    Representation.vectorFunctional M.toStarSubalgebra.subtype ξ
  refine ⟨φ, (fun _ ↦ rfl), Representation.vectorFunctional_one _ hξ,
    (fun a b ↦ htrace a a.property b b.property), ?_,
    M.isNormalPositiveFunctional_vectorFunctional ξ, hfactor, hfinite,
    ⟨hfactor, hfinite, hinfinite⟩⟩
  intro a
  constructor
  · intro ha
    exact Subtype.ext (hfaithful a a.property ha)
  · rintro rfl
    simp
