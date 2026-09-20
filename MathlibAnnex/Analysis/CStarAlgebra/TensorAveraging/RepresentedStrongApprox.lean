import MathlibAnnex.Analysis.CStarAlgebra.Kadison

/-!
# Finite strong-star approximation on the self-adjoint unit ball

The existing quantitative Kadison theorem controls a finite Hilbert sum.
Here it is converted to simultaneous per-vector estimates in the same
irreducible representation.  Since both operators are self-adjoint, these
are also their adjoint estimates.  Arbitrary isometries, as required for
the projective-tensor convex-closure step, are a separate open extension.
-/

set_option autoImplicit false
open scoped InnerProduct CStarAlgebra ENNReal lp
open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.Analysis.InnerProductSpace

namespace MathlibAnnex.CStarAlgebra.TensorAveraging

variable {A H : Type*} [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Nontrivial H]

theorem irreducible_selfAdjoint_contract_finite_strongStar_approx
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    {I : Type*} [Fintype I] [DecidableEq I]
    (ξ : I → H) (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hTnorm : ‖T‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 1 ∧
      ∀ i : I, ‖(pi a - T) (ξ i)‖ < ε := by
  obtain ⟨a, ha, hanorm, hsum⟩ :=
    pi.exists_selfAdjoint_norm_le_one_atomic_apply_sub_norm_lt_of_irreducible'
      hpi ξ T hT hTnorm hε
  refine ⟨a, ha, hanorm, ?_⟩
  intro i
  have hcoord := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (atomicRepresentation (fun _ : I => pi) a (finiteHilbertSum ξ) -
      diagonal (fun _ : I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
        (finiteHilbertSum ξ)) i
  have h := hcoord.trans_lt hsum
  simpa [atomicRepresentation_apply, finiteHilbertSum_apply, diagonal_apply] using h

/-- The same finite-vector contraction lift controls the forward and adjoint
actions simultaneously; both are the same estimate in this self-adjoint case. -/
theorem irreducible_selfAdjoint_contract_finite_both_apply_approx
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    {I : Type*} [Fintype I] [DecidableEq I]
    (ξ : I → H) (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hTnorm : ‖T‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 1 ∧
      ∀ i : I, ‖(pi a - T) (ξ i)‖ < ε ∧
        ‖(star (pi a) - star T) (ξ i)‖ < ε := by
  obtain ⟨a, ha, hanorm, hforward⟩ :=
    irreducible_selfAdjoint_contract_finite_strongStar_approx
      pi hpi ξ T hT hTnorm hε
  refine ⟨a, ha, hanorm, fun i => ⟨hforward i, ?_⟩⟩
  rw [ha.map pi, hT]
  exact hforward i

/-- A proper isometry cannot be approximated in strong-star topology by
unitaries at a nonzero vector in the kernel of its adjoint.  This rules out
the tempting unitary-only shortcut in the represented closure argument. -/
theorem unitary_star_approx_obstruction
    (U : unitary (H →L[ℂ] H)) (S : H →L[ℂ] H) (ξ : H)
    (hker : (star S) ξ = 0) :
    ‖(star (U : H →L[ℂ] H) - star S) ξ‖ = ‖ξ‖ := by
  simp only [ContinuousLinearMap.sub_apply, hker, sub_zero]
  exact Unitary.norm_map (star U) ξ

end MathlibAnnex.CStarAlgebra.TensorAveraging
