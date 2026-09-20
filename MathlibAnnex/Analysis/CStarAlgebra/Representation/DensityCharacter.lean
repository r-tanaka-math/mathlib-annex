import MathlibAnnex.Topology.DensityCharacter
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.DensityLowerBound
import MathlibAnnex.Analysis.CStarAlgebra.Representation.OrdinarySingleton

/-!
# Exact density and the continuum-hypothesis obstruction

The reverse implication is for an arbitrary ordinary singleton model, not just
the fixed CAR construction and not just separably represented algebras.
The algebra and displayed Hilbert universes are independent. The singleton
quantifier uses the algebra universe, as in its existing provider API.
-/
set_option autoImplicit false
open scoped Cardinal ComplexOrder
namespace MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.Topology
universe u v

/-- Translate the existing ordinary-competitor singleton predicate into the
genuinely nonunital-domain representation API without changing its quantifier. -/
theorem Representation.IsSingletonIrreducibleModelAmongNonUnital.isSingletonIrreducibleModel_toNonUnitalStarAlgHom
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {pi : Representation A H}
    (hpi : Representation.IsSingletonIrreducibleModelAmongNonUnital.{u, v, u} pi) :
    NonUnitalCStarRepresentation.IsSingletonIrreducibleModel.{u, v, u}
      pi.toNonUnitalStarAlgHom := by
  refine ⟨?_, ?_⟩
  · exact NonUnitalRepresentation.isIrreducible_toNonUnitalStarAlgHom pi hpi.1
  · intro K _ _ _ rho hrho
    obtain ⟨U, hU⟩ := hpi.2 K rho hrho
    exact ⟨U, fun a x => hU a x⟩

/-- Any possibly nonunital counterexample of exact norm density aleph one
forces the continuum hypothesis. No separable representation is assumed. -/
theorem NonUnitalCStarRepresentation.continuum_eq_aleph_one_of_singleton_of_not_isCompactOperatorModel_of_hasDensityCharacter
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Nontrivial A] {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (pi : NonUnitalCStarRepresentation A H)
    (hpi : NonUnitalCStarRepresentation.IsSingletonIrreducibleModel.{u, v, u} pi)
    (hnot : ¬ IsCompactOperatorModel pi)
    (hd : HasDensityCharacter A (Cardinal.aleph 1)) :
    (Cardinal.continuum : Cardinal.{u}) = Cardinal.aleph 1 := by
  obtain ⟨s, hs, hsc⟩ := hd.1
  have hle :=
    NonUnitalCStarRepresentation.continuum_le_cardinalMk_dense_algebra_of_singleton_of_not_isCompactOperatorModel
      pi hpi hnot s hs
  exact le_antisymm (hsc ▸ hle) Cardinal.aleph_one_le_continuum

/-- An ordinary Naimark counterexample with exact norm density κ.

The source algebra need not have a unit; irreducibility includes nonzeroness.
The statement ranges over carriers and competitors in the indicated universe,
following the existing singleton API. It includes no separability hypothesis. -/
def ExistsNaimarkCounterexampleOfDensity (κ : Cardinal.{u}) : Prop :=
  ∃ (A : Type u) (iA : NonUnitalCStarAlgebra A),
    letI := iA
    ∃ (oA : PartialOrder A),
      letI := oA
      ∃ (sA : StarOrderedRing A) (nA : Nontrivial A),
        letI := sA
        letI := nA
        ∃ (H : Type u) (nH : NormedAddCommGroup H),
          letI := nH
          ∃ (iH : InnerProductSpace ℂ H),
            letI := iH
            ∃ (cH : CompleteSpace H),
              letI := cH
              ∃ pi : NonUnitalCStarRepresentation A H,
                NonUnitalCStarRepresentation.IsSingletonIrreducibleModel.{u, u, u} pi ∧
                (¬ IsCompactOperatorModel pi) ∧ HasDensityCharacter A κ

/-- The density-aleph-one existence statement implies CH in any carrier universe. -/
theorem continuum_eq_aleph_one_of_existsNaimarkCounterexampleOfDensity
    (h : ExistsNaimarkCounterexampleOfDensity (Cardinal.aleph 1 : Cardinal.{u})) :
    (Cardinal.continuum : Cardinal.{u}) = Cardinal.aleph 1 := by
  obtain ⟨A, iA, oA, sA, nA, H, nH, iH, cH, pi, hpi, hnot, hd⟩ := h
  letI := iA
  letI := oA
  letI := sA
  letI := nA
  letI := nH
  letI := iH
  letI := cH
  exact NonUnitalCStarRepresentation.continuum_eq_aleph_one_of_singleton_of_not_isCompactOperatorModel_of_hasDensityCharacter
    pi hpi hnot hd

end MathlibAnnex.Analysis.CStarAlgebra
