import MathlibAnnex.Analysis.CStarAlgebra.Representation.VectorFunctional
import Mathlib.RingTheory.TwoSidedIdeal.Kernel

/-!
# Faithfulness from the closed-ideal dichotomy

Irreducibility is unnecessary here: a unital representation on a nonzero
Hilbert space has proper kernel. This small lemma keeps the faithful-model
argument independent of any separable irreducible-representation claim.
-/

set_option autoImplicit false

namespace MathlibAnnex.Analysis.CStarAlgebra.Representation

universe u v
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

/-- Every unital representation of an algebra with no nontrivial closed
two-sided ideals is faithful, provided its Hilbert space is nonzero. -/
theorem injective_of_closed_ideal_dichotomy
    (hA : ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤)
    (ρ : Representation A H) : Function.Injective ρ := by
  let I : TwoSidedIdeal A := TwoSidedIdeal.ker ρ.toRingHom
  have hclosed : IsClosed (I : Set A) := by
    have hset : (I : Set A) =
        (continuousLinearMap ρ) ⁻¹' ({0} : Set (H →L[ℂ] H)) := by
      ext a
      exact TwoSidedIdeal.mem_ker ρ.toRingHom
    rw [hset]
    exact isClosed_singleton.preimage (continuousLinearMap ρ).continuous
  rcases hA I hclosed with hbot | htop
  · exact (TwoSidedIdeal.ker_eq_bot ρ.toRingHom).mp hbot
  · have hone : (1 : A) ∈ I := by rw [htop]; trivial
    have hzero := (TwoSidedIdeal.mem_ker ρ.toRingHom).mp hone
    have hbad : (1 : H →L[ℂ] H) = 0 := by simpa only [map_one] using hzero
    exact (one_ne_zero hbad).elim

end MathlibAnnex.Analysis.CStarAlgebra.Representation
