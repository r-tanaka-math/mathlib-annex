import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.Representation
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! A full bounded-operator image has no nonzero proper reducing subspace. -/

set_option autoImplicit false

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uA uH

namespace NonUnitalCStarRepresentation

theorem irreducible_of_surjective
    {A : Type uA} [NonUnitalCStarAlgebra A]
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    (pi : NonUnitalCStarRepresentation A H)
    (hsurj : Function.Surjective pi) : pi.IsIrreducible := by
  constructor
  · obtain ⟨a, ha⟩ := hsurj (1 : H →L[ℂ] H)
    exact ⟨a, by rw [ha]; exact one_ne_zero⟩
  · intro K hK
    by_cases hbot : K = ⊥
    · exact Or.inl hbot
    right
    obtain ⟨x, hxK, hxne⟩ := K.exists_mem_ne_zero_of_ne_bot hbot
    apply Submodule.eq_top_iff'.mpr
    intro y
    obtain ⟨a, ha⟩ := hsurj (InnerProductSpace.rankOne ℂ y x)
    have hxy : (InnerProductSpace.rankOne ℂ y x) x ∈ K := by
      rw [← ha]
      exact (hK.2 a x hxK).1
    rw [InnerProductSpace.rankOne_apply] at hxy
    exact (K.smul_mem_iff (inner_self_ne_zero.mpr hxne)).mp hxy

end NonUnitalCStarRepresentation

end MathlibAnnex.Analysis.CStarAlgebra
