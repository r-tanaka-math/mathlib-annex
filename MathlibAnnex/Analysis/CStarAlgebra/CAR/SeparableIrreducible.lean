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

universe u v w

/-- Compose two captures and the existing finite-dimensionality theorem before
specializing the concrete CAR algebra or ambient Hilbert carrier. -/
private theorem not_isIrreducible_of_two_capture_models
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
    {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (ambient : Representation A F)
    (hmodelH : Representation.IsUniqueIrreducibleModelAmongNonUnital.{u, w, v} ambient)
    (hmodelA : Representation.IsUniqueIrreducibleModelAmongNonUnital.{u, w, u} ambient)
    (hinfinite : ¬ FiniteDimensional ℂ A)
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (rho : NonUnitalRepresentation (A := A) (H := H)) : ¬ rho.IsIrreducible := by
  intro hrho
  let pi : Representation A H := rho.toUnital hrho
  have hpi : Representation.IsIrreducible pi :=
    NonUnitalRepresentation.isIrreducible_toUnital rho hrho
  have hambient_pi : ambient.UnitaryEquivalent pi := hmodelH.2.2 H rho hrho
  have hsingleton : Representation.IsSingletonIrreducibleModelAmongNonUnital.{u, v, u} pi := by
    refine ⟨hpi, ?_⟩
    intro K _ _ _ sigma hsigma
    exact Representation.unitaryEquivalent_trans
      (Representation.unitaryEquivalent_symm hambient_pi) (hmodelA.2.2 K sigma hsigma)
  exact hinfinite (Representation.finiteDimensional_algebra_of_singleton_amongNonUnital
    pi hsingleton)

/-- The main target admits no nonzero irreducible ordinary representation on
a separable complete complex Hilbert space.  The input representation is not
assumed to preserve the unit. -/
theorem not_isIrreducible_of_separable
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (rho : NonUnitalRepresentation (A := AtomicCounterexampleAlgebra) (H := H)) :
    ¬ rho.IsIrreducible := by
  exact not_isIrreducible_of_two_capture_models
    (shellFamilyInclusion homogeneityShellFamily)
    (isUniqueIrreducibleModelAmongNonUnital_shellFamilyInclusion.{v} homogeneityShellFamily)
    (isUniqueIrreducibleModelAmongNonUnital_shellFamilyInclusion.{0} homogeneityShellFamily)
    (not_finiteDimensional_shellFamilyTarget homogeneityShellFamily) rho

end MathlibAnnex.CStarAlgebra.CAR
