import Mathlib.LinearAlgebra.Complex.Module
import MathlibAnnex.Analysis.CStarAlgebra.ExactInterpolation
import MathlibAnnex.Analysis.CStarAlgebra.Representation.FiniteDimension

/-!
# Full operator image in finite dimension
-/

set_option autoImplicit false

open scoped ComplexOrder ComplexStarModule

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Representation

/-- Exact interpolation on the whole finite-dimensional Hilbert space gives
an algebra preimage of every self-adjoint operator. -/
theorem exists_preimage_of_isSelfAdjoint [Nontrivial H]
    [FiniteDimensional ℂ H]
    (pi : Representation A H) (hirr : pi.IsIrreducible)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    ∃ a : A, pi a = T := by
  obtain ⟨a, _ha, _hanorm, hexact⟩ :=
    exists_selfAdjoint_norm_le_two_mul_and_eq_on pi
      (isIrreducible_starAlgHom pi hirr) (⊤ : Submodule ℂ H) T hT
  refine ⟨a, ContinuousLinearMap.ext fun x => ?_⟩
  exact hexact x (by trivial)

/-- An irreducible representation on a nonzero finite-dimensional Hilbert
space has full operator image. -/
theorem surjective_of_irreducible_of_finiteDimensional [Nontrivial H]
    [FiniteDimensional ℂ H]
    (pi : Representation A H) (hirr : pi.IsIrreducible) :
    Function.Surjective pi := by
  intro T
  obtain ⟨a, ha⟩ :=
    exists_preimage_of_isSelfAdjoint pi hirr
      (ℜ T : H →L[ℂ] H) (ℜ T).prop
  obtain ⟨b, hb⟩ :=
    exists_preimage_of_isSelfAdjoint pi hirr
      (ℑ T : H →L[ℂ] H) (ℑ T).prop
  refine ⟨a + Complex.I • b, ?_⟩
  calc
    pi (a + Complex.I • b) = pi a + Complex.I • pi b := by simp
    _ = (ℜ T : H →L[ℂ] H) + Complex.I • (ℑ T : H →L[ℂ] H) := by
      rw [ha, hb]
    _ = T := realPart_add_I_smul_imaginaryPart T

/-- For a separable singleton irreducible model, the represented operators
are exactly the compact operators.  In fact the Hilbert space is finite-
dimensional and the represented image is all bounded operators. -/
theorem isCompactOperatorModel_of_singleton [Nontrivial A]
    [TopologicalSpace.SeparableSpace H]
    (pi : Representation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi) :
    IsCompactOperatorModel pi.toNonUnitalStarAlgHom := by
  letI : Nontrivial H := nontrivial_of_isNonzero pi hsingle.1.1
  letI : FiniteDimensional ℂ H :=
    finiteDimensional_space_of_singleton pi hsingle
  refine ⟨injective_of_singleton pi hsingle, ?_, ?_⟩
  · intro a
    change IsCompactOperator (pi a)
    exact isCompactOperator_of_locallyCompactSpace_rng (pi a)
  · intro T _hT
    exact surjective_of_irreducible_of_finiteDimensional pi hsingle.1 T

/-- The faithful/full-compact-image conclusion for a separable singleton
irreducible model of a nonzero unital C-star algebra. -/
theorem faithful_and_compactOperatorModel_of_singleton [Nontrivial A]
    [TopologicalSpace.SeparableSpace H]
    (pi : Representation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi) :
    Function.Injective pi ∧
      IsCompactOperatorModel pi.toNonUnitalStarAlgHom :=
  ⟨injective_of_singleton pi hsingle,
    isCompactOperatorModel_of_singleton pi hsingle⟩

end Representation

end MathlibAnnex.Analysis.CStarAlgebra
