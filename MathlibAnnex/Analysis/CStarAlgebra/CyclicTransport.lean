import MathlibAnnex.Analysis.CStarAlgebra.Cyclic
import MathlibAnnex.Analysis.InnerProductSpace.DenseTransport

/-!
# Pointed cyclic transport

Equality of vector states gives equality of the full orbit Gram kernel.  The
dense transport theorem then supplies a unique unitary carrying orbit to
orbit; multiplication yields intertwining on the dense cyclic subspace and
continuity extends it everywhere.
-/

set_option autoImplicit false

open scoped InnerProduct

namespace StarAlgHom

variable {A H K : Type*}
variable [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem existsUnique_pointedCyclicTransport
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (ξ : H) (η : K)
    (hπ : DenseRange (orbitMap π ξ)) (hσ : DenseRange (orbitMap σ η))
    (hstate : ∀ a, inner ℂ ξ (π a ξ) = inner ℂ η (σ a η)) :
    ∃! W : H ≃ₗᵢ[ℂ] K,
      (∀ a, W (π a ξ) = σ a η) ∧
      W ξ = η ∧
      ∀ a, (W : H →L[ℂ] K).comp (π a) = (σ a).comp (W : H →L[ℂ] K) := by
  have hgram : ∀ a b, inner ℂ ((orbitMap π ξ) a) ((orbitMap π ξ) b) =
      inner ℂ ((orbitMap σ η) a) ((orbitMap σ η) b) := by
    intro a b
    simp only [orbitMap]
    have hπadj : ContinuousLinearMap.adjoint (π a) = π (star a) := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    have hσadj : ContinuousLinearMap.adjoint (σ a) = σ (star a) := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    have hπmul : π (star a * b) ξ = π (star a) (π b ξ) := by
      rw [map_mul]
      rfl
    have hσmul : σ (star a * b) η = σ (star a) (σ b η) := by
      rw [map_mul]
      rfl
    calc
      inner ℂ (π a ξ) (π b ξ) = inner ℂ ξ (π (star a * b) ξ) := by
        rw [← ContinuousLinearMap.adjoint_inner_right]
        rw [hπadj, hπmul]
      _ = inner ℂ η (σ (star a * b) η) := hstate _
      _ = inner ℂ (σ a η) (σ b η) := by
        rw [← ContinuousLinearMap.adjoint_inner_right]
        rw [hσadj, hσmul]
  obtain ⟨W, hW, hWuniq⟩ := LinearMap.existsUnique_linearIsometryEquiv_of_inner_eq
    (orbitMap π ξ) (orbitMap σ η) hπ hσ hgram
  have hW' : ∀ a, W (π a ξ) = σ a η := by
    intro a
    have ha := hW a
    change W (π a ξ) = σ a η at ha
    exact ha
  have hintertwine : ∀ a,
      (W : H →L[ℂ] K).comp (π a) = (σ a).comp (W : H →L[ℂ] K) := by
    intro a
    apply ContinuousLinearMap.ext
    intro x
    exact hπ.induction_on x (isClosed_eq
      ((W : H →L[ℂ] K).comp (π a)).continuous
      ((σ a).comp (W : H →L[ℂ] K)).continuous) fun b ↦ by
        change W (π a (π b ξ)) = σ a (W (π b ξ))
        have hπmul : π (a * b) ξ = π a (π b ξ) := by
          rw [map_mul]
          rfl
        have hσmul : σ (a * b) η = σ a (σ b η) := by
          rw [map_mul]
          rfl
        calc
          W (π a (π b ξ)) = W (π (a * b) ξ) := congrArg W hπmul.symm
          _ = σ (a * b) η := hW' _
          _ = σ a (σ b η) := hσmul
          _ = σ a (W (π b ξ)) := congrArg (σ a) (hW' b).symm
  have hpoint : W ξ = η := by
    simpa using hW' (1 : A)
  refine ⟨W, ⟨hW', hpoint, hintertwine⟩, ?_⟩
  intro W' hW'
  exact hWuniq W' hW'.1

end StarAlgHom
