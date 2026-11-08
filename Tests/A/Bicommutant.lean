import MathlibAnnex.Analysis.VonNeumannAlgebra.Bicommutant
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Typed consumers of the general bicommutant theorem

The tests cover arbitrary star subalgebras, represented ranges, the scalar
subalgebra, all bounded operators, finite-dimensional matrix actions, and
the zero Hilbert space. They do not assume irreducibility.
-/

set_option autoImplicit false

open Set Topology

namespace VonNeumannAlgebraExamples

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem sot_closure_eq (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H) ⁻¹'
        closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
          (S : Set (H →L[ℂ] H))) =
      (VonNeumannAlgebra.generated S : Set (H →L[ℂ] H)) := by
  ext T
  exact (VonNeumannAlgebra.mem_generated_iff_mem_sotClosure S T).symm

theorem wot_closure_eq (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    ContinuousLinearMapWOT.ofCLM ⁻¹'
        closure (ContinuousLinearMapWOT.ofCLM '' (S : Set (H →L[ℂ] H))) =
      (VonNeumannAlgebra.generated S : Set (H →L[ℂ] H)) := by
  ext T
  exact (VonNeumannAlgebra.mem_generated_iff_mem_wotClosure S T).symm

theorem represented_wot_closure {A : Type*} [CStarAlgebra A]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    T ∈ VonNeumannAlgebra.generated π.range ↔
      ContinuousLinearMapWOT.ofCLM T ∈
        closure (Set.range fun a : A ↦ ContinuousLinearMapWOT.ofCLM (π a)) := by
  have hr : ContinuousLinearMapWOT.ofCLM '' (π.range : Set (H →L[ℂ] H)) =
      Set.range (fun a : A ↦ ContinuousLinearMapWOT.ofCLM (π a)) := by
    ext U
    constructor
    · rintro ⟨V, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨π a, ⟨a, rfl⟩, rfl⟩
  simpa only [hr] using VonNeumannAlgebra.mem_generated_iff_mem_wotClosure π.range T

theorem scalar_subalgebra_wot_closure (T : H →L[ℂ] H) :
    T ∈ VonNeumannAlgebra.generated (⊥ : StarSubalgebra ℂ (H →L[ℂ] H)) ↔
      ContinuousLinearMapWOT.ofCLM T ∈
        closure (ContinuousLinearMapWOT.ofCLM ''
          ((⊥ : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H))) :=
  VonNeumannAlgebra.mem_generated_iff_mem_wotClosure _ T

theorem scalar_operator_mem_sot_closure (c : ℂ) :
    ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
        (algebraMap ℂ (H →L[ℂ] H) c) ∈
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((⊥ : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H))) := by
  apply (VonNeumannAlgebra.mem_generated_iff_mem_sotClosure _ _).mp
  exact VonNeumannAlgebra.subset_generated _
    ((⊥ : StarSubalgebra ℂ (H →L[ℂ] H)).algebraMap_mem c)

theorem full_algebra_wot_closure (T : H →L[ℂ] H) :
    ContinuousLinearMapWOT.ofCLM T ∈
      closure (ContinuousLinearMapWOT.ofCLM ''
        ((⊤ : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H))) := by
  apply (VonNeumannAlgebra.mem_generated_iff_mem_wotClosure _ _).mp
  exact VonNeumannAlgebra.subset_generated _ (by trivial)

theorem generated_contains_every_operator_of_subsingleton [Subsingleton H]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    T ∈ VonNeumannAlgebra.generated S := by
  have hT : T = 0 := ContinuousLinearMap.ext fun _ ↦ Subsingleton.elim _ _
  rw [hT]
  exact VonNeumannAlgebra.subset_generated S S.zero_mem'

theorem zero_space_wot_closure
    (S : StarSubalgebra ℂ
      (EuclideanSpace ℂ (Fin 0) →L[ℂ] EuclideanSpace ℂ (Fin 0)))
    (T : EuclideanSpace ℂ (Fin 0) →L[ℂ] EuclideanSpace ℂ (Fin 0)) :
    ContinuousLinearMapWOT.ofCLM T ∈
      closure (ContinuousLinearMapWOT.ofCLM ''
        (S : Set (EuclideanSpace ℂ (Fin 0) →L[ℂ] EuclideanSpace ℂ (Fin 0)))) :=
  (VonNeumannAlgebra.mem_generated_iff_mem_wotClosure S T).mp
    (generated_contains_every_operator_of_subsingleton S T)

theorem matrix_bicommutant (n : ℕ)
    (S : StarSubalgebra ℂ
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
    (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) A ∈ Set.centralizer (Set.centralizer
        (S : Set (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))) ↔
      ContinuousLinearMapWOT.ofCLM (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) A) ∈
        closure (ContinuousLinearMapWOT.ofCLM ''
          (S : Set (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))) :=
  (VonNeumannAlgebra.mem_generated_iff S (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) A)).symm.trans
    (VonNeumannAlgebra.mem_generated_iff_mem_wotClosure S (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) A))

theorem finite_vector_approximation
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : T ∈ VonNeumannAlgebra.generated S)
    {I : Type*} [Fintype I] [DecidableEq I] (ξ : I → H)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A ∈ S, ∀ i, ‖A (ξ i) - T (ξ i)‖ < ε :=
  S.exists_forall_apply_sub_norm_lt_of_mem_bicommutant
    ((VonNeumannAlgebra.mem_generated_iff S T).mp hT) ξ hε

end VonNeumannAlgebraExamples
