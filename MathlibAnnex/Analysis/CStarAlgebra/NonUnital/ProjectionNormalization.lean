import MathlibAnnex.Analysis.CStarAlgebra.ProjectionNormalization
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.Representation
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Adapters

/-!
# Bilateral normalization for a genuinely nonunital domain

The near-identity multiplier lives in the unitization.  Its sandwich of an
original-algebra element has zero scalar coordinate and returns to that
algebra without subtracting a scalar and losing positivity.
-/

set_option autoImplicit false

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uA uH

namespace NonUnitalCStarRepresentation

theorem exists_near_one_positive_normalizer_on_projection
    {A : Type uA} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (P : H →L[ℂ] H) (hP : IsStarProjection P)
    [FiniteDimensional ℂ P.range]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ a : A, 0 ≤ a → ‖a‖ ≤ 1 →
        ‖(1 - pi a) * P‖ < δ →
        ∃ b : Unitization ℂ A,
          ‖b - 1‖ < ε ∧
          (∃ d : A, 0 ≤ d ∧ ‖d‖ ≤ 1 ∧ pi d * P = P ∧
            (d : Unitization ℂ A) = b * (a : Unitization ℂ A) * star b) := by
  letI : Nontrivial H := pi.nontrivial_of_isNonzero hpi.1
  have hunit : StarAlgHom.IsIrreducible pi.unitization :=
    Representation.isIrreducible_starAlgHom pi.unitization
      (isIrreducible_unitization pi hpi)
  obtain ⟨δ, hδ, hnormal⟩ :=
    MathlibAnnex.Analysis.CStarAlgebra.exists_near_one_positive_normalizer_on_projection
      pi.unitization hunit P hP hε
  refine ⟨δ, hδ, ?_⟩
  intro a ha hanorm happrox
  have haU : 0 ≤ (a : Unitization ℂ A) :=
    Unitization.inr_nonneg_iff.mpr ha
  have hanormU : ‖(a : Unitization ℂ A)‖ ≤ 1 := by
    simpa only [Unitization.norm_inr] using hanorm
  have happroxU : ‖(1 - pi.unitization (a : Unitization ℂ A)) * P‖ < δ := by
    simpa using happrox
  obtain ⟨b, hbnear, hbpos, hbnorm, hbexact⟩ :=
    hnormal (a : Unitization ℂ A) haU hanormU happroxU
  let w : Unitization ℂ A := b * (a : Unitization ℂ A) * star b
  have hwfst : w.fst = 0 := by simp [w]
  let d : A := w.snd
  have hw : (d : Unitization ℂ A) = w := by
    apply Unitization.ext
    · simpa [d] using hwfst.symm
    · rfl
  have hdpos : 0 ≤ d := by
    apply Unitization.inr_nonneg_iff.mp
    rw [hw]
    exact hbpos
  have hdnorm : ‖d‖ ≤ 1 := by
    have hn := hbnorm
    change ‖w‖ ≤ 1 at hn
    rw [← hw, Unitization.norm_inr] at hn
    exact hn
  have hdexact : pi d * P = P := by
    have he := hbexact
    change pi.unitization w * P = P at he
    rw [← hw] at he
    simpa using he
  exact ⟨b, hbnear, d, hdpos, hdnorm, hdexact, hw⟩

end NonUnitalCStarRepresentation

end MathlibAnnex.Analysis.CStarAlgebra
