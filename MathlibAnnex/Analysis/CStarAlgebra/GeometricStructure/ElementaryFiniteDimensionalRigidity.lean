/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.CompactRepresentationRigidity
import MathlibAnnex.Analysis.CStarAlgebra.Representation.ElementaryCompact
import MathlibAnnex.Analysis.CStarAlgebra.Representation.FiniteDimensionalCompact

/-!
# Elementary and finite-dimensional geometric structure rigidity

The one-sided compact representation theorem yields two symmetric corollaries.
An exact elementary model supplies the actual representation
`NonUnitalCStarRepresentation.ofCompactOperatorEquiv`. A finite-dimensional
algebra supplies the already constructed finite separating GNS sum. The other
algebra is not assumed compact, elementary, or finite-dimensional.

The elementary existence statement spells out the paper's definition: there
is a complete complex Hilbert space and a star equivalence with its compact
operator algebra. Its Hilbert carrier and structures are explicitly quantified;
the two possible model universes are independent of both algebra universes.
No new predicate named `IsElementary` is introduced, and no equivalence with
an independently axiomatized elementary-algebra predicate is presumed. A given
exact representation model is also supported without replacing its action.

The finite-dimensional disjunction is a proposition. Each branch installs
only the finite-dimensional instance that the branch actually supplies.
Finite GNS separation, compactness, and all model and density inputs are proved
by the existing producers, not supplied as extra hypotheses of the corollaries.

Zero algebras and zero Hilbert models are allowed. No unit, nontriviality,
nonempty spectrum, countability, or separability is assumed. Auxiliary spectral
orders are local to the proof that uses the finite GNS representation.

All conclusions concern existence of a star equivalence. They do not say that
such an equivalence induces a specified nonlinear GSS homeomorphism, or that
the star equivalence is unique. The forward implications use the full closure
homeomorphism induced by a star equivalence, not a finite-closure replacement.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w z

variable {A : Type u} {B : Type v}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

section GivenModel

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A specified exact compact-operator model supplies the same actual faithful
compact representation to the general rigidity theorem. No model or compactness
of the other algebra is required, and the zero model is not excluded. -/
theorem nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_compactOperatorEquiv
    (E : A ≃⋆ₐ[ℂ] ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) :
    Nonempty (A ≃⋆ₐ[ℂ] B) ↔
      Nonempty (ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
        (NormedSpace.geometricStructureClosure ℂ B)) := by
  exact nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_isCompactlyRepresented
    (NonUnitalCStarRepresentation.ofCompactOperatorEquiv E)
    (NonUnitalCStarRepresentation.isCompactlyRepresented_ofCompactOperatorEquiv E)

/-- The given-representation version uses the original exact model `pi` itself.
Its established injectivity and pointwise compactness are the two inputs to
the general theorem; no second representation is chosen. -/
theorem nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_isCompactOperatorModel
    (pi : NonUnitalCStarRepresentation A H) (hpi : IsCompactOperatorModel pi) :
    Nonempty (A ≃⋆ₐ[ℂ] B) ↔
      Nonempty (ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
        (NormedSpace.geometricStructureClosure ℂ B)) := by
  exact nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_isCompactlyRepresented
    pi ⟨hpi.1, hpi.2.1⟩

end GivenModel

/-- Either algebra may have an elementary model, with its Hilbert carrier and
structures explicitly quantified in independently specified universes. This is
the model-existence formulation of elementary, not an additional model premise
attached to an unrelated elementary predicate. The right branch uses the inverse
GSS homeomorphism and then reverses the resulting star equivalence. -/
theorem nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_exists_compactOperatorEquiv
    (hModel :
      (∃ (H : Type w) (normed : NormedAddCommGroup H),
        letI : NormedAddCommGroup H := normed
        ∃ inner : InnerProductSpace ℂ H,
          letI : InnerProductSpace ℂ H := inner
          ∃ complete : CompleteSpace H,
            letI : CompleteSpace H := complete
            Nonempty (A ≃⋆ₐ[ℂ] ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H)) ∨
      (∃ (K : Type z) (normed : NormedAddCommGroup K),
        letI : NormedAddCommGroup K := normed
        ∃ inner : InnerProductSpace ℂ K,
          letI : InnerProductSpace ℂ K := inner
          ∃ complete : CompleteSpace K,
            letI : CompleteSpace K := complete
            Nonempty (B ≃⋆ₐ[ℂ] ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K))) :
    Nonempty (A ≃⋆ₐ[ℂ] B) ↔
      Nonempty (ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
        (NormedSpace.geometricStructureClosure ℂ B)) := by
  constructor
  · rintro ⟨E⟩
    exact ⟨geometricStructureHomeomorphOfStarAlgEquiv E⟩
  · rintro ⟨e⟩
    rcases hModel with hA | hB
    · rcases hA with ⟨H, normed, inner, complete, ⟨E⟩⟩
      letI : NormedAddCommGroup H := normed
      letI : InnerProductSpace ℂ H := inner
      letI : CompleteSpace H := complete
      exact
        (nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_compactOperatorEquiv
          (B := B) E).mpr ⟨e⟩
    · rcases hB with ⟨K, normed, inner, complete, ⟨E⟩⟩
      letI : NormedAddCommGroup K := normed
      letI : InnerProductSpace ℂ K := inner
      letI : CompleteSpace K := complete
      obtain ⟨F⟩ :=
        (nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_compactOperatorEquiv
          (B := A) E).mpr ⟨e.symm⟩
      exact ⟨F.symm⟩

/-- Finite-dimensionality of the source alone supplies a finite separating GNS
selection and its actual faithful compact action. Neither the selection nor
its separating or compactness properties are hypotheses of this theorem. -/
theorem nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_finiteDimensional
    [FiniteDimensional ℂ A] :
    Nonempty (A ≃⋆ₐ[ℂ] B) ↔
      Nonempty (ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
        (NormedSpace.geometricStructureClosure ℂ B)) := by
  letI : PartialOrder A := _root_.CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := _root_.CStarAlgebra.spectralOrderedRing A
  obtain ⟨s, hs⟩ :=
    PrimitiveSpectrum.exists_finset_isCompactlyRepresented_finiteGNSRepresentation (A := A)
  exact nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_isCompactlyRepresented
    (PrimitiveSpectrum.finiteGNSRepresentation (A := A) s) hs

/-- The symmetric finite-dimensional corollary, including the zero algebra.
Only one of the two finite-dimensional instances is installed in each branch.
The specified nonlinear GSS homeomorphism is used to prove existence, not
claimed to be the map induced by the resulting star equivalence. -/
theorem nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_finiteDimensional_or
    (hfinite : FiniteDimensional ℂ A ∨ FiniteDimensional ℂ B) :
    Nonempty (A ≃⋆ₐ[ℂ] B) ↔
      Nonempty (ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
        (NormedSpace.geometricStructureClosure ℂ B)) := by
  constructor
  · rintro ⟨E⟩
    exact ⟨geometricStructureHomeomorphOfStarAlgEquiv E⟩
  · rintro ⟨e⟩
    rcases hfinite with hA | hB
    · letI : FiniteDimensional ℂ A := hA
      exact
        (nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_finiteDimensional
          (A := A) (B := B)).mpr ⟨e⟩
    · letI : FiniteDimensional ℂ B := hB
      obtain ⟨F⟩ :=
        (nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_finiteDimensional
          (A := B) (B := A)).mpr ⟨e.symm⟩
      exact ⟨F.symm⟩

end MathlibAnnex.Analysis.CStarAlgebra
