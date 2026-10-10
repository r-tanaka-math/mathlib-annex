/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.CompactDirectSumRigidity
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.CompactRepresentationTransport
import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.CompactlyRepresentedDecomposition
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.CompactRepresentationCharacterization
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.StarAlgEquiv

/-!
# One-sided compact representation rigidity of geometric structure spaces

If one nonunital complex C-star algebra has an actual faithful compact-valued
representation, a full geometric-structure closure homeomorphism to a second
algebra forces a star-algebra equivalence. Compact representability of the
second algebra is derived by transport to its already defined reduced atomic
representation, not required as an additional premise.

The two actual representations supply the canonical compact c₀ decompositions.
Their dependent fibers are the very cyclic subspaces used in those models.
Each fiber is nontrivial by its existing chosen nonzero cyclic vector. The
all-index given-model rigidity theorem handles empty and nonempty index types,
so no nontriviality, nonempty-index, unit, or separability premise is added.
Both spectral orders are fixed locally before any model fiber is used.

The final equivalence concerns existence: a star equivalence exists if and
only if a full GSS homeomorphism exists, provided either algebra admits a
faithful compact representation. The given-representation theorem permits
its Hilbert space to lie in an independent universe. The existential version
uses each algebra's own universe, exactly as in the compact-representation
characterization; its canonical reduced atomic witness is not obtained by
shrinking an arbitrary Hilbert space.

The star equivalence need not induce the specified nonlinear GSS
homeomorphism. Only existence of a star equivalence is concluded. Conversely,
a star equivalence supplies its own induced full GSS homeomorphism. No claim
about equality of these two geometric maps is made.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w

variable {A : Type u} {B : Type v}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A faithful compact-valued representation on one side and a full GSS
homeomorphism force a star equivalence. The target representation, both
compact models, and all fiber nontriviality proofs are produced internally.
The zero-algebra and empty-index cases use the existing all-index theorem. -/
theorem nonempty_starAlgEquiv_of_isCompactlyRepresented_of_geometricStructure_homeomorph
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented)
    (e : ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B)) :
    Nonempty (A ≃⋆ₐ[ℂ] B) := by
  letI : PartialOrder A := _root_.CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := _root_.CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder B := _root_.CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := _root_.CStarAlgebra.spectralOrderedRing B
  let rho : NonUnitalCStarRepresentation B (PrimitiveSpectrum.ReducedAtomicHilbertSpace B) :=
    PrimitiveSpectrum.reducedAtomicRepresentation (A := B)
  have hrho : rho.IsCompactlyRepresented :=
    PrimitiveSpectrum.isCompactlyRepresented_reducedAtomicRepresentation_of_geometricStructure_homeomorph
      e pi hpi
  let EA : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum
      (fun i : MinimalClosedStarIdeal A => i.CompactModelSpace pi hpi) :=
    pi.compactC0Decomposition hpi
  let EB : B ≃⋆ₐ[ℂ] CompactOperatorC0Sum
      (fun j : MinimalClosedStarIdeal B => j.CompactModelSpace rho hrho) :=
    rho.compactC0Decomposition hrho
  letI : ∀ i : MinimalClosedStarIdeal A, Nontrivial (i.CompactModelSpace pi hpi) :=
    fun i => MinimalClosedStarIdeal.instNontrivialCompactModelSpace i pi hpi
  letI : ∀ j : MinimalClosedStarIdeal B, Nontrivial (j.CompactModelSpace rho hrho) :=
    fun j => MinimalClosedStarIdeal.instNontrivialCompactModelSpace j rho hrho
  exact nonempty_starAlgEquiv_of_compact_direct_sum_models_of_geometricStructure_homeomorph
    (fun i : MinimalClosedStarIdeal A => i.CompactModelSpace pi hpi)
    (fun j : MinimalClosedStarIdeal B => j.CompactModelSpace rho hrho)
    EA EB e

/-- With an actual faithful compact representation of `A`, existence of a
star equivalence to `B` is equivalent to existence of a full GSS homeomorphism.
The reverse implication derives compact representability of `B`; it does not
assume that an arbitrary prescribed representation of `B` is compact. -/
theorem nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_isCompactlyRepresented
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) :
    Nonempty (A ≃⋆ₐ[ℂ] B) ↔
      Nonempty (ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
        (NormedSpace.geometricStructureClosure ℂ B)) := by
  constructor
  · rintro ⟨E⟩
    exact ⟨geometricStructureHomeomorphOfStarAlgEquiv E⟩
  · rintro ⟨e⟩
    exact nonempty_starAlgEquiv_of_isCompactlyRepresented_of_geometricStructure_homeomorph
      pi hpi e

/-- The one-sided compact GSS characterization. Either algebra may supply
existence of a faithful compact representation in its own universe, with the
Hilbert carrier and its structures explicitly quantified. The characterization
provides its same canonical reduced atomic witness; the right-hand branch
uses the inverse geometric homeomorphism and reverses the resulting star
equivalence. Neither algebra is assumed to be nonzero. -/
theorem nonempty_starAlgEquiv_iff_nonempty_geometricStructure_homeomorph_of_exists_isCompactlyRepresented
    (hCompact :
      (∃ (K : Type u) (normed : NormedAddCommGroup K),
        letI : NormedAddCommGroup K := normed
        ∃ inner : InnerProductSpace ℂ K,
          letI : InnerProductSpace ℂ K := inner
          ∃ complete : CompleteSpace K,
            letI : CompleteSpace K := complete
            ∃ pi : NonUnitalCStarRepresentation A K, pi.IsCompactlyRepresented) ∨
      (∃ (K : Type v) (normed : NormedAddCommGroup K),
        letI : NormedAddCommGroup K := normed
        ∃ inner : InnerProductSpace ℂ K,
          letI : InnerProductSpace ℂ K := inner
          ∃ complete : CompleteSpace K,
            letI : CompleteSpace K := complete
            ∃ pi : NonUnitalCStarRepresentation B K, pi.IsCompactlyRepresented)) :
    Nonempty (A ≃⋆ₐ[ℂ] B) ↔
      Nonempty (ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
        (NormedSpace.geometricStructureClosure ℂ B)) := by
  constructor
  · rintro ⟨E⟩
    exact ⟨geometricStructureHomeomorphOfStarAlgEquiv E⟩
  · rintro ⟨e⟩
    rcases hCompact with hA | hB
    · letI : PartialOrder A := _root_.CStarAlgebra.spectralOrder A
      letI : StarOrderedRing A := _root_.CStarAlgebra.spectralOrderedRing A
      have hAtomic :=
        (NonUnitalCStarRepresentation.exists_isCompactlyRepresented_iff_reducedAtomicRepresentation
          (A := A)).mp hA
      exact nonempty_starAlgEquiv_of_isCompactlyRepresented_of_geometricStructure_homeomorph
        (PrimitiveSpectrum.reducedAtomicRepresentation (A := A)) hAtomic e
    · letI : PartialOrder B := _root_.CStarAlgebra.spectralOrder B
      letI : StarOrderedRing B := _root_.CStarAlgebra.spectralOrderedRing B
      have hAtomic :=
        (NonUnitalCStarRepresentation.exists_isCompactlyRepresented_iff_reducedAtomicRepresentation
          (A := B)).mp hB
      obtain ⟨E⟩ :=
        nonempty_starAlgEquiv_of_isCompactlyRepresented_of_geometricStructure_homeomorph
          (PrimitiveSpectrum.reducedAtomicRepresentation (A := B)) hAtomic e.symm
      exact ⟨E.symm⟩

end MathlibAnnex.Analysis.CStarAlgebra
