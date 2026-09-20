import MathlibAnnex.Analysis.CStarAlgebra.CloseProjections
import MathlibAnnex.Analysis.CStarAlgebra.ShellMatching
import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.KishimotoOzawaSakai

/-!
# Conditional exact matching of a source shell

KOS remains an explicit argument.  Approximate innerness is invoked on the
singleton finite set containing the root shell; the near-projection theorem
then turns that approximation into exact matching.
-/

set_option autoImplicit false

namespace MathlibAnnex.CStarAlgebra

open MathlibAnnex.CStarAlgebra

universe u v

/-- Exact shell matching for one projection from point-norm approximate innerness of a
fixed automorphism. -/
theorem exists_shell_of_approximately_inner
    (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
    (alpha : A ≃⋆ₐ[ℂ] A)
    (happrox : ∀ (F : Finset A) (epsilon : ℝ), 0 < epsilon →
      ∃ g : unitary A, ∀ a ∈ F,
        ‖alpha a - (g : A) * a * star (g : A)‖ < epsilon)
    (f : A) (hf : IsStarProjection f) :
    ∃ w : A, star w * w = alpha f ∧ w * star w = f := by
  classical
  obtain ⟨g, hg⟩ := happrox {f} 1 zero_lt_one
  have hclose : ‖alpha f - (g : A) * f * star (g : A)‖ < 1 :=
    hg f (by simp)
  have he : IsStarProjection (alpha f) := hf.map alpha
  have hr : IsStarProjection ((g : A) * f * star (g : A)) :=
    hf.unitary_conjugate g
  obtain ⟨t, ht⟩ :=
    he.exists_unitary_conjugate_of_norm_sub_lt_one hr hclose
  let w := matchedLink g t (alpha f)
  exact ⟨w, matchedLink_supports g t (alpha f) f he ht⟩

/-- A fixed approximately inner automorphism simultaneously determines exact links for
an arbitrary set-indexed family of projections. -/
theorem exists_shell_family_of_approximately_inner
    (A : Type u) {ι : Type v}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
    (alpha : A ≃⋆ₐ[ℂ] A)
    (happrox : ∀ (F : Finset A) (epsilon : ℝ), 0 < epsilon →
      ∃ g : unitary A, ∀ a ∈ F,
        ‖alpha a - (g : A) * a * star (g : A)‖ < epsilon)
    (f : ι → A) (hf : ∀ i, IsStarProjection (f i)) :
    ∃ w : ι → A, ∀ i,
      star (w i) * w i = alpha (f i) ∧ w i * star (w i) = f i := by
  classical
  have hlinks (i : ι) : ∃ w : A,
      star w * w = alpha (f i) ∧ w * star w = f i :=
    exists_shell_of_approximately_inner A alpha happrox (f i) (hf i)
  exact ⟨fun i => Classical.choose (hlinks i),
    fun i => Classical.choose_spec (hlinks i)⟩

/-- KOS supplies one automorphism for the state pair; all projection shells are then
matched using that same automorphism.  Only the approximating unitary varies with `n`. -/
theorem exists_shell_family_of_kishimotoOzawaSakai (hKOS : KishimotoOzawaSakaiProperty.{u})
    (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [TopologicalSpace.SeparableSpace A]
    (hsimple : IsSimpleCStarAlgebra A)
    (phi_i phi_o : A →L[ℂ] ℂ)
    (hpure_i : IsPureState A phi_i) (hpure_o : IsPureState A phi_o)
    (f : ℕ → A) (hf : ∀ n, IsStarProjection (f n)) :
    ∃ alpha : A ≃⋆ₐ[ℂ] A,
      (∀ a : A, phi_i (alpha a) = phi_o a) ∧
      ∃ w : ℕ → A, ∀ n,
        star (w n) * w n = alpha (f n) ∧ w n * star (w n) = f n := by
  classical
  letI : Nontrivial A := hsimple.1
  obtain ⟨alpha, hstate, happrox⟩ :=
    hKOS A hsimple phi_i phi_o hpure_i hpure_o
  have hlinks : ∀ n, ∃ w : A,
      star w * w = alpha (f n) ∧ w * star w = f n := by
    intro n
    obtain ⟨g, hg⟩ := happrox {f n} 1 zero_lt_one
    have hclose : ‖alpha (f n) - (g : A) * f n * star (g : A)‖ < 1 := by
      exact hg (f n) (by simp)
    have he : IsStarProjection (alpha (f n)) := (hf n).map alpha
    have hr : IsStarProjection ((g : A) * f n * star (g : A)) :=
      (hf n).unitary_conjugate g
    obtain ⟨t, ht⟩ :=
      he.exists_unitary_conjugate_of_norm_sub_lt_one hr hclose
    let w := matchedLink g t (alpha (f n))
    exact ⟨w, matchedLink_supports g t (alpha (f n)) (f n) he ht⟩
  let w : ℕ → A := fun n => Classical.choose (hlinks n)
  exact ⟨alpha, hstate, w, fun n => Classical.choose_spec (hlinks n)⟩

theorem exists_shell_link_of_kishimotoOzawaSakai (hKOS : KishimotoOzawaSakaiProperty.{u})
    (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [TopologicalSpace.SeparableSpace A]
    (hsimple : IsSimpleCStarAlgebra A)
    (phi_i phi_o : A →L[ℂ] ℂ)
    (hpure_i : IsPureState A phi_i) (hpure_o : IsPureState A phi_o)
    (f : A) (hf : IsStarProjection f) :
    ∃ alpha : A ≃⋆ₐ[ℂ] A,
      (∀ a : A, phi_i (alpha a) = phi_o a) ∧
      ∃ w : A, star w * w = alpha f ∧ w * star w = f := by
  classical
  letI : Nontrivial A := hsimple.1
  obtain ⟨alpha, hstate, happrox⟩ :=
    hKOS A hsimple phi_i phi_o hpure_i hpure_o
  obtain ⟨g, hg⟩ := happrox {f} 1 zero_lt_one
  have hclose : ‖alpha f - (g : A) * f * star (g : A)‖ < 1 := by
    exact hg f (by simp)
  have he : IsStarProjection (alpha f) := hf.map alpha
  have hr : IsStarProjection ((g : A) * f * star (g : A)) :=
    hf.unitary_conjugate g
  obtain ⟨t, ht⟩ :=
    he.exists_unitary_conjugate_of_norm_sub_lt_one hr hclose
  let w := matchedLink g t (alpha f)
  have hw := matchedLink_supports g t (alpha f) f he ht
  exact ⟨alpha, hstate, w, hw⟩

end MathlibAnnex.CStarAlgebra
