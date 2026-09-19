import MathlibAnnex.Analysis.CStarAlgebra.State.Ideal

/-!
# A single unitary-equivalence class of irreducible representations
-/

set_option autoImplicit false

open scoped ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Representation

/-- The represented irreducible is a model for every irreducible
representation.  Faithfulness is deliberately not part of this predicate. -/
def IsSingletonIrreducibleModel (pi : Representation A H) : Prop :=
  pi.IsIrreducible ∧
    ∀ (K : Type w) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K] (rho : Representation A K),
      rho.IsIrreducible → pi.UnitaryEquivalent rho

/-- Once faithfulness has been proved separately, a singleton irreducible
model forces closed-two-sided-ideal simplicity. -/
theorem isSimpleCStarAlgebra_of_singleton_of_injective [Nontrivial A]
    (pi : Representation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (hinj : Function.Injective pi) : IsSimpleCStarAlgebra A := by
  refine ⟨inferInstance, ?_⟩
  intro I hclosed
  by_cases hI : I = ⊤
  · exact Or.inr hI
  · left
    apply le_antisymm
    · intro x hx
      obtain ⟨phi, hphi, _hpure, hirr, hann⟩ :=
        exists_irreducibleGNS_annihilating I hI hclosed
      let f : A →ₚ[ℂ] ℂ := positiveLinearMapOfMemStateSpace phi hphi
      obtain ⟨U, hU⟩ := hsingle.2 f.GNS f.gnsStarAlgHom hirr
      have hpi : pi x = 0 := by
        apply ContinuousLinearMap.ext
        intro y
        apply U.injective
        calc
          U (pi x y) = f.gnsStarAlgHom x (U y) := hU x y
          _ = 0 := by rw [hann x hx]; rfl
          _ = U 0 := (map_zero U).symm
      exact hinj (by simpa using hpi)
    · exact bot_le

end Representation

end MathlibAnnex.Analysis.CStarAlgebra
