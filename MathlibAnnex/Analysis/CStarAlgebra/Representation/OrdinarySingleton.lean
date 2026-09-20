import MathlibAnnex.Analysis.CStarAlgebra.Representation.FullImage
import MathlibAnnex.Analysis.CStarAlgebra.Representation.NonUnital

/-!
# Singleton models quantified over ordinary possibly nonunital representations

The represented algebra in this file is unital, but competitors are ordinary
star-algebra maps which are not assumed to preserve the unit.  Nonzero
irreducibility forces such a competitor to preserve the unit.
-/

set_option autoImplicit false

open scoped ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace NonUnitalRepresentation

/-- Forgetting unitality preserves the explicitly nonzero irreducibility
predicate. -/
theorem isIrreducible_toNonUnitalStarAlgHom
    (pi : Representation A H) (hirr : pi.IsIrreducible) :
    IsIrreducible pi.toNonUnitalStarAlgHom := by
  exact ⟨hirr.1, hirr.2⟩

end NonUnitalRepresentation

namespace Representation

/-- Raw singleton-spectrum hypothesis for a unital algebra, with every
ordinary nonzero irreducible representation included and no faithfulness
built into the definition. -/
def IsSingletonIrreducibleModelAmongNonUnital
    (pi : Representation A H) : Prop :=
  pi.IsIrreducible ∧
    ∀ (K : Type w) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K] (rho : NonUnitalRepresentation (A := A) (H := K)),
      ∀ hrho : rho.IsIrreducible,
        pi.UnitaryEquivalent (rho.toUnital hrho)

/-- Quantifying over possibly nonunital competitors implies the corresponding
raw singleton statement for unital representations. -/
theorem IsSingletonIrreducibleModelAmongNonUnital.isSingletonIrreducibleModel
    {pi : Representation A H}
    (hpi : IsSingletonIrreducibleModelAmongNonUnital.{u, v, w} pi) :
    IsSingletonIrreducibleModel.{u, v, w} pi := by
  refine ⟨hpi.1, ?_⟩
  intro K _ _ _ rho hrho
  let rhoNU : NonUnitalRepresentation (A := A) (H := K) :=
    rho.toNonUnitalStarAlgHom
  have hrhoNU : rhoNU.IsIrreducible :=
    NonUnitalRepresentation.isIrreducible_toNonUnitalStarAlgHom rho hrho
  obtain ⟨U, hU⟩ := hpi.2 K rhoNU hrhoNU
  refine ⟨U, ?_⟩
  intro a x
  simpa [rhoNU] using hU a x

/-- Conversely, a raw singleton statement for unital representations covers
all nonzero irreducible possibly nonunital competitors. -/
theorem IsSingletonIrreducibleModel.isSingletonIrreducibleModelAmongNonUnital
    {pi : Representation A H}
    (hpi : IsSingletonIrreducibleModel.{u, v, w} pi) :
    IsSingletonIrreducibleModelAmongNonUnital.{u, v, w} pi := by
  refine ⟨hpi.1, ?_⟩
  intro K _ _ _ rho hrho
  exact hpi.2 K (rho.toUnital hrho)
    (NonUnitalRepresentation.isIrreducible_toUnital rho hrho)

/-- Unital Rosenberg conclusion with the quantifier ranging over ordinary
possibly nonunital nonzero irreducible representations. -/
theorem faithful_and_compactOperatorModel_of_singleton_amongNonUnital
    [Nontrivial A] [TopologicalSpace.SeparableSpace H]
    (pi : Representation A H)
    (hsingle : IsSingletonIrreducibleModelAmongNonUnital.{u, v, u} pi) :
    Function.Injective pi ∧
      IsCompactOperatorModel pi.toNonUnitalStarAlgHom :=
  faithful_and_compactOperatorModel_of_singleton pi
    hsingle.isSingletonIrreducibleModel

/-- The representation space is finite-dimensional under the ordinary
possibly nonunital singleton quantifier. -/
theorem finiteDimensional_space_of_singleton_amongNonUnital
    [Nontrivial A] [TopologicalSpace.SeparableSpace H]
    (pi : Representation A H)
    (hsingle : IsSingletonIrreducibleModelAmongNonUnital.{u, v, u} pi) :
    FiniteDimensional ℂ H :=
  finiteDimensional_space_of_singleton pi hsingle.isSingletonIrreducibleModel

/-- The unital algebra is finite-dimensional under the ordinary possibly
nonunital singleton quantifier. -/
theorem finiteDimensional_algebra_of_singleton_amongNonUnital
    [Nontrivial A] [TopologicalSpace.SeparableSpace H]
    (pi : Representation A H)
    (hsingle : IsSingletonIrreducibleModelAmongNonUnital.{u, v, u} pi) :
    FiniteDimensional ℂ A :=
  finiteDimensional_algebra_of_singleton pi hsingle.isSingletonIrreducibleModel

/-- A nonzero infinite-dimensional unital C-star algebra cannot have a
separable nonzero irreducible representation representing its only ordinary
unitary-equivalence class. -/
theorem not_singleton_amongNonUnital_of_infiniteDimensional
    [Nontrivial A] (hA : ¬ FiniteDimensional ℂ A)
    [TopologicalSpace.SeparableSpace H]
    (pi : Representation A H) :
    ¬ IsSingletonIrreducibleModelAmongNonUnital.{u, v, u} pi := by
  intro hsingle
  exact hA (finiteDimensional_algebra_of_singleton_amongNonUnital pi hsingle)

end Representation

end MathlibAnnex.Analysis.CStarAlgebra
