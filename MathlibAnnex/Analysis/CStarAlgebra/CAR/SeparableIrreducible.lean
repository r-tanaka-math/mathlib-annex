import MathlibAnnex.Analysis.CStarAlgebra.CAR.AtomicCounterexample
import MathlibAnnex.Analysis.CStarAlgebra.Representation.OrdinarySingleton

/-!
# Excluding separable irreducible representations of the CAR main target

The ordinary endpoint captures a representation on any independent Hilbert
universe.  Comparing two such captures through the fixed ambient inclusion
gives the raw singleton hypothesis needed by the finite-dimensionality
theorem, without assuming that an input nonunital representation preserves
the unit.
-/

set_option autoImplicit false

noncomputable section

namespace MathlibAnnex.CStarAlgebra.CAR

open MathlibAnnex.Analysis.CStarAlgebra

universe v

/-- The main target admits no nonzero irreducible ordinary representation on
a separable complete complex Hilbert space.  The input representation is not
assumed to preserve the unit. -/
theorem not_isIrreducible_of_separable
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (rho : NonUnitalRepresentation (A := AtomicCounterexampleAlgebra) (H := H)) :
    ¬ rho.IsIrreducible := by
  intro hrho
  let pi : Representation AtomicCounterexampleAlgebra H := rho.toUnital hrho
  have hpi : Representation.IsIrreducible pi :=
    NonUnitalRepresentation.isIrreducible_toUnital rho hrho
  have hambient_pi : atomicCounterexampleRepresentation.UnitaryEquivalent pi := by
    obtain ⟨U, hU⟩ := (atomicCounterexampleEndpoint.{v}).captures_nonunital H rho hrho
    refine ⟨U, ?_⟩
    intro a x
    simpa [atomicCounterexampleRepresentation, pi] using hU a x
  have hsingleton :
      Representation.IsSingletonIrreducibleModelAmongNonUnital.{0, v, 0} pi := by
    refine ⟨hpi, ?_⟩
    intro K _ _ _ sigma hsigma
    have hambient_sigma :
        atomicCounterexampleRepresentation.UnitaryEquivalent (sigma.toUnital hsigma) := by
      obtain ⟨U, hU⟩ := (atomicCounterexampleEndpoint.{0}).captures_nonunital K sigma hsigma
      refine ⟨U, ?_⟩
      intro a x
      change U (atomicCounterexampleRepresentation a x) = sigma a (U x)
      simpa [atomicCounterexampleRepresentation] using hU a x
    exact Representation.unitaryEquivalent_trans
      (Representation.unitaryEquivalent_symm hambient_pi) hambient_sigma
  exact (atomicCounterexampleEndpoint.{v}).not_finiteDimensional_target
    (Representation.finiteDimensional_algebra_of_singleton_amongNonUnital
      pi hsingleton)

end MathlibAnnex.CStarAlgebra.CAR
