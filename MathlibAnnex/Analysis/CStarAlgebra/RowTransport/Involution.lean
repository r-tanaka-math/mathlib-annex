import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.Gram
import MathlibAnnex.Analysis.CStarAlgebra.ExactInterpolation
import MathlibAnnex.Analysis.InnerProductSpace.GramPerturbation

/-!
Finite orthogonal-family involution lifting.  The Gram perturbation theorem
does not assume a common rank; the required projection is positive and is
interpolated sharply on the requested finite span.
-/

set_option autoImplicit false

noncomputable section

open MathlibAnnex.InnerProductSpace
open MathlibAnnex.Analysis.InnerProductSpace

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uA uH

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

/-- Close orthogonal finite families admit one positive contraction whose
represented action nearly fixes their differences and nearly kills their
sums.  The conclusion survives rank loss and repeated/zero row vectors. -/
theorem StarAlgHom.exists_positive_contraction_of_orthogonal_gram
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (v w : Fin n → H),
        (∑ i, ‖v i‖ ^ 2) ≤ 1 → (∑ i, ‖w i‖ ^ 2) ≤ 1 →
        (∀ i j, inner ℂ (v i) (w j) = 0) →
        (∀ i j, ‖inner ℂ (v i) (v j) - inner ℂ (w i) (w j)‖ < δ) →
        ∃ h : A, 0 ≤ h ∧ ‖h‖ ≤ 1 ∧
          (∀ i, ‖pi h (v i - w i) - (v i - w i)‖ < τ) ∧
          (∀ i, ‖pi h (v i + w i)‖ < τ) := by
  obtain ⟨δ, hδ, hgram⟩ :=
    exists_delta_orthogonalGramPerturbation (n := n) hτ
  refine ⟨δ, hδ, ?_⟩
  intro v w hv hw horth hclose
  obtain ⟨U, hUv, hUw, hU2, hfinite⟩ :=
    hgram v w hv hw horth hclose
  let P : H →L[ℂ] H := U.involutionProjection
  have hP : IsStarProjection P :=
    U.isStarProjection_involutionProjection hU2
  letI : FiniteDimensional ℂ
      (LinearMap.range P.toLinearMap) :=
    U.finiteDimensional_range_involutionProjection
  let S : Submodule ℂ H :=
    Submodule.span ℂ (Set.range v ∪ Set.range w)
  letI : FiniteDimensional ℂ S :=
    FiniteDimensional.span_of_finite ℂ
      ((Set.finite_range v).union (Set.finite_range w))
  let E : Submodule ℂ H := S ⊔ LinearMap.range P.toLinearMap
  letI : FiniteDimensional ℂ E := inferInstance
  have hvE (i : Fin n) : v i ∈ E :=
    Submodule.mem_sup_left
      (Submodule.subset_span (Or.inl (Set.mem_range_self i)))
  have hwE (i : Fin n) : w i ∈ E :=
    Submodule.mem_sup_left
      (Submodule.subset_span (Or.inr (Set.mem_range_self i)))
  obtain ⟨h, hh, hhnorm, heq⟩ :=
    exists_positive_contraction_eq_on pi hpi E P hP.nonneg hP.norm_le
  refine ⟨h, hh, hhnorm, ?_, ?_⟩
  · intro i
    have heqv := heq (v i) (hvE i)
    have heqw := heq (w i) (hwE i)
    have heqdiff : pi h (v i - w i) = P (v i - w i) := by
      rw [map_sub, map_sub, heqv, heqw]
    rw [heqdiff]
    exact (LinearIsometryEquiv.norm_involutionProjection_sub_sub_le
      U (v i) (w i)).trans_lt (by
      have h1 := hUv i
      have h2 := hUw i
      linarith)
  · intro i
    have heqv := heq (v i) (hvE i)
    have heqw := heq (w i) (hwE i)
    have heqsum : pi h (v i + w i) = P (v i + w i) := by
      rw [map_add, map_add, heqv, heqw]
    rw [heqsum]
    exact (LinearIsometryEquiv.norm_involutionProjection_add_le
      U (v i) (w i)).trans_lt (by
      have h1 := hUv i
      have h2 := hUw i
      linarith)

end MathlibAnnex.Analysis.CStarAlgebra
