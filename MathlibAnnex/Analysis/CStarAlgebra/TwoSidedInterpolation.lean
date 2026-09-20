import MathlibAnnex.Analysis.CStarAlgebra.Representation.MatrixTwo
import MathlibAnnex.Analysis.CStarAlgebra.ExactInterpolation

/-!
# Sharp simultaneous interpolation of an operator and its adjoint

The two-by-two amplification is irreducible.  Apply the already established
sharp self-adjoint Kadison theorem to `[[0,T],[T*,0]]`, on both copies of the
requested finite-dimensional subspace.  The off-diagonal entry of the single
self-adjoint witness gives one `a` with `‖a‖ ≤ ‖T‖`, exact forward action and
exact adjoint action.  No new transitivity or approximation axiom is used.

Controller-authored candidate; compilation is a separate qualification gate.
-/

set_option autoImplicit false

open scoped ENNReal lp InnerProduct
open MathlibAnnex.Analysis.InnerProductSpace

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

/-- A single sharp-norm witness interpolates `T` and `T*` simultaneously. -/
theorem exists_norm_le_and_both_eq_on
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) :
    ∃ a : A, ‖a‖ ≤ ‖T‖ ∧
      (∀ x : H, x ∈ E → pi a x = T x) ∧
      (∀ x : H, x ∈ E → pi (star a) x = (star T) x) := by
  classical
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : Nontrivial (HilbertTwo H) := nontrivial_hilbertTwo
  let e0 : H →L[ℂ] HilbertTwo H :=
    coordinateEmbedding (H := fun _ : Fin 2 => H) (0 : Fin 2)
  let e1 : H →L[ℂ] HilbertTwo H :=
    coordinateEmbedding (H := fun _ : Fin 2 => H) (1 : Fin 2)
  let F : Submodule ℂ (HilbertTwo H) :=
    E.map e0.toLinearMap ⊔ E.map e1.toLinearMap
  haveI : FiniteDimensional ℂ F := by
    dsimp [F]
    infer_instance
  let rho := matrixTwoRepresentation pi
  obtain ⟨b, hbself, hbnorm, hbaction⟩ :=
    exists_selfAdjoint_norm_le_and_eq_on rho
      (isIrreducible_matrixTwoRepresentation pi hpi) F
      (twoDilation T) (isSelfAdjoint_twoDilation T)
  have hb10 : b (1 : Fin 2) (0 : Fin 2) = star (b 0 1) := by
    have h := congrArg
      (fun m : CStarMatrix (Fin 2) (Fin 2) A => m 1 0) hbself
    simpa only [CStarMatrix.star_apply] using h.symm
  refine ⟨b 0 1, CStarMatrix.norm_entry_le_norm.trans
      (hbnorm.trans (norm_twoDilation_le T)), ?_, ?_⟩
  · intro x hx
    have hxF : e1 x ∈ F := by
      exact (show E.map e1.toLinearMap ≤ F from le_sup_right)
        ⟨x, hx, rfl⟩
    have h := congrArg (fun y : HilbertTwo H => y 0) (hbaction (e1 x) hxF)
    simpa [rho, e1, matrixTwoRepresentation_apply, coordinateEmbedding_apply,
      lp.coeFn_single, Pi.single_apply] using h
  · intro x hx
    have hxF : e0 x ∈ F := by
      exact (show E.map e0.toLinearMap ≤ F from le_sup_left)
        ⟨x, hx, rfl⟩
    have h := congrArg (fun y : HilbertTwo H => y 1) (hbaction (e0 x) hxF)
    have h' : pi (b 1 0) x = (star T) x := by
      simpa [rho, e0, matrixTwoRepresentation_apply, coordinateEmbedding_apply,
        lp.coeFn_single, Pi.single_apply] using h
    simpa only [hb10] using h'

/-- Finite-set formulation, including the empty set and the zero operator. -/
theorem exists_norm_le_and_both_eq_finset
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    (s : Finset H) (T : H →L[ℂ] H) :
    ∃ a : A, ‖a‖ ≤ ‖T‖ ∧
      (∀ x ∈ s, pi a x = T x) ∧
      (∀ x ∈ s, pi (star a) x = (star T) x) := by
  classical
  let E := Submodule.span ℂ (s : Set H)
  haveI : FiniteDimensional ℂ E :=
    FiniteDimensional.span_of_finite ℂ s.finite_toSet
  obtain ⟨a, ha, hf, hs⟩ := exists_norm_le_and_both_eq_on pi hpi E T
  refine ⟨a, ha, ?_, ?_⟩
  · intro x hx
    exact hf x (Submodule.subset_span hx)
  · intro x hx
    exact hs x (Submodule.subset_span hx)

/-- Finite-family formulation: the same witness serves every index and both
adjoint directions, with no loss in the norm budget. -/
theorem exists_norm_le_and_both_eq_family
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    {I : Type*} [Fintype I] (xi : I → H) (T : H →L[ℂ] H) :
    ∃ a : A, ‖a‖ ≤ ‖T‖ ∧
      (∀ i, pi a (xi i) = T (xi i)) ∧
      (∀ i, pi (star a) (xi i) = (star T) (xi i)) := by
  classical
  obtain ⟨a, ha, hf, hs⟩ :=
    exists_norm_le_and_both_eq_finset pi hpi (Finset.univ.image xi) T
  refine ⟨a, ha, ?_, ?_⟩
  · intro i
    exact hf (xi i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  · intro i
    exact hs (xi i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- Contractive finite simultaneous strong-star approximation as an immediate
consequence of exact interpolation, not an added density assumption. -/
theorem exists_contraction_finite_both_apply_approx
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    {I : Type*} [Fintype I] (xi : I → H)
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) {eps : ℝ} (heps : 0 < eps) :
    ∃ a : A, ‖a‖ ≤ 1 ∧ ∀ i,
      ‖(pi a - T) (xi i)‖ < eps ∧
      ‖(pi (star a) - star T) (xi i)‖ < eps := by
  obtain ⟨a, ha, hf, hs⟩ := exists_norm_le_and_both_eq_family pi hpi xi T
  refine ⟨a, ha.trans hT, ?_⟩
  intro i
  simpa only [ContinuousLinearMap.sub_apply, hf i, hs i,
    sub_self, norm_zero] using And.intro heps heps

end MathlibAnnex.Analysis.CStarAlgebra
