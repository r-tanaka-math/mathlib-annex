import Mathlib.Topology.Bases
import Mathlib.Analysis.InnerProductSpace.Adjoint
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.CharacterEigenvector

/-!
# Countability of unitization characters represented by a non-unital algebra

Characters other than the scalar character of the unitization give mutually
orthogonal unit vectors.  Separability therefore makes that complement
countable; adjoining the scalar character makes the full character space
countable as well.
-/

set_option autoImplicit false

open Function Metric Set
open scoped ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace NonUnitalCStarRepresentation

/-- The non-scalar characters of a closed unital star subalgebra of a
minimal unitization. -/
abbrev NonScalarCharacterSpace
    (D : StarSubalgebra ℂ (Unitization ℂ A))
    [IsClosed (D : Set (Unitization ℂ A))] :=
  {chi : WeakDual.characterSpace ℂ D //
    chi ≠ infinityCharacterOn (A := A) D}

/-- The non-scalar characters of a closed star subalgebra of the unitization
are countable when they are represented in a separable singleton model. -/
theorem countable_nonScalarCharacterSpace_of_singleton [Nontrivial A]
    [TopologicalSpace.SeparableSpace H]
    (pi : NonUnitalCStarRepresentation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (D : StarSubalgebra ℂ (Unitization ℂ A))
    [IsClosed (D : Set (Unitization ℂ A))] :
    Countable (NonScalarCharacterSpace (A := A) D) := by
  choose eta heta_norm heta_eigen using
    fun chi : NonScalarCharacterSpace (A := A) D =>
      exists_unit_eigenvector_of_character_ne_infinity pi hsingle D chi.1 chi.2
  have horth : Pairwise fun chi psi : NonScalarCharacterSpace (A := A) D =>
      inner ℂ (eta chi) (eta psi) = 0 := by
    intro chi psi hne
    obtain ⟨d, hd⟩ : ∃ d : D, chi.1 d ≠ psi.1 d := by
      by_contra hall
      push Not at hall
      apply hne
      apply Subtype.ext
      exact WeakDual.CharacterSpace.ext hall
    have hadj : ContinuousLinearMap.adjoint (pi.unitization (d : Unitization ℂ A)) =
        pi.unitization (star (d : Unitization ℂ A)) := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    have heq := (pi.unitization (d : Unitization ℂ A)).adjoint_inner_right
      (eta chi) (eta psi)
    rw [hadj] at heq
    change inner ℂ (eta chi)
        (pi.unitization ((star d : D) : Unitization ℂ A) (eta psi)) =
      inner ℂ (pi.unitization (d : Unitization ℂ A) (eta chi)) (eta psi) at heq
    rw [heta_eigen psi (star d), heta_eigen chi d] at heq
    simp only [inner_smul_left, inner_smul_right, map_star] at heq
    by_contra hinner
    have hstar : star (psi.1 d) = star (chi.1 d) :=
      mul_right_cancel₀ hinner heq
    exact hd (star_injective hstar).symm
  have hdist (chi psi : NonScalarCharacterSpace (A := A) D) (hne : chi ≠ psi) :
      1 ≤ dist (eta chi) (eta psi) := by
    rw [dist_eq_norm]
    have hsq := norm_sub_mul_self (𝕜 := ℂ) (eta chi) (eta psi)
    rw [horth hne, map_zero, heta_norm chi, heta_norm psi] at hsq
    norm_num at hsq
    nlinarith [norm_nonneg (eta chi - eta psi)]
  have hballs : Pairwise (Disjoint on
      fun chi : NonScalarCharacterSpace (A := A) D =>
        ball (eta chi) (1 / 3 : ℝ)) := by
    intro chi psi hne
    apply ball_disjoint_ball
    have := hdist chi psi hne
    norm_num at this ⊢
    linarith
  exact hballs.countable_of_isOpen_disjoint
    (fun _ => isOpen_ball)
    (fun chi => ⟨eta chi, mem_ball_self (by norm_num)⟩)

/-- The whole character space is countable: it consists of the preceding
complement and the one scalar character. -/
theorem countable_characterSpace_of_nonUnital_singleton [Nontrivial A]
    [TopologicalSpace.SeparableSpace H]
    (pi : NonUnitalCStarRepresentation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (D : StarSubalgebra ℂ (Unitization ℂ A))
    [IsClosed (D : Set (Unitization ℂ A))] :
    Countable (WeakDual.characterSpace ℂ D) := by
  let X := WeakDual.characterSpace ℂ D
  let chiInf : X := infinityCharacterOn (A := A) D
  let Y := {chi : X // chi ≠ chiInf}
  have hY : Countable Y :=
    countable_nonScalarCharacterSpace_of_singleton pi hsingle D
  letI : Countable Y := hY
  let f : Y ⊕ Unit → X := Sum.elim Subtype.val (fun _ => chiInf)
  have hf : Surjective f := by
    intro chi
    by_cases hchi : chi = chiInf
    · exact ⟨Sum.inr (), by simp [f, hchi]⟩
    · exact ⟨Sum.inl ⟨chi, hchi⟩, rfl⟩
  exact hf.countable

end NonUnitalCStarRepresentation

end MathlibAnnex.Analysis.CStarAlgebra
