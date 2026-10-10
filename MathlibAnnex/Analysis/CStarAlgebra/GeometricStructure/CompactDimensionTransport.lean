/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.CompactTrichotomyTransport
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartHilbertDimension
import MathlibAnnex.Analysis.InnerProductSpace.HilbertBasisCardinality

/-!
# Hilbert dimension in the compact-containing branch of Theorem 8.9

The proof keeps the faithful target representation and literal preimage
homeomorphism selected by `exists_faithful_normalPart_transport`.  It compares
the source Hilbert space with that one faithful image through the specified
GSS homeomorphism, and compares the target Hilbert space with the same image
through compact-ideal rigidity.  No replacement representation is chosen.

The result concerns indices of arbitrary actual Hilbert bases in independent
universes.  It is not a Hamel-rank comparison and does not assert that the
specified GSS homeomorphism is induced by an isometry.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set
open scoped Cardinal

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v uI uJ
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι : Type uI} {κ : Type uJ}

attribute [local instance] HomKernelQuotient.imageCStarAlgebra
  HomKernelQuotient.isClosed_image

variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable (T : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K))
variable [IsClosed (S : Set (H →L[ℂ] H))] [IsClosed (T : Set (K →L[ℂ] K))]
variable (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
variable (hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T))
variable (e : ClosureSpace.Homeomorph
  (NormedSpace.geometricStructureClosure ℂ S)
  (NormedSpace.geometricStructureClosure ℂ T))

local instance : NonUnitalCStarAlgebra T :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra T
    (h_closed := inferInstance)
local instance : PartialOrder T := _root_.CStarAlgebra.spectralOrder T
local instance : StarOrderedRing T := _root_.CStarAlgebra.spectralOrderedRing T

include hS hT e in
/-- If either concrete algebra contains every compact operator, then arbitrary
Hilbert bases of the two original Hilbert spaces have the same lifted
cardinality.  Both compact containments are derived through one and the same
faithful target image selected from the specified full GSS homeomorphism. -/
theorem hilbertBasis_lift_mk_eq_of_geometricStructure_homeomorph_of_compact_le
    (hcompact :
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ S ∨
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K ≤ T)
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K) :
    Cardinal.lift.{uJ} (#ι) = Cardinal.lift.{uI} (#κ) := by
  classical
  obtain ⟨phi, hfaith, r, _hpre, _hinv, himage⟩ :=
    exists_faithful_normalPart_transport S hS e
  let f := normalPartHomeomorphOfImage (e.trans r.symm) himage
  have hR : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype
      (NonUnitalStarAlgHom.range phi.gnsRepresentation)) :=
    (NonUnitalCStarRepresentation.isIrreducible_imageRepresentation_iff
      phi.gnsRepresentation).2 phi.isIrreducible_gnsRepresentation
  have hSR := compactOperatorStarSubalgebra_le_iff_of_normalPart_homeomorph
    S (NonUnitalStarAlgHom.range phi.gnsRepresentation) hS hR f
  have hTR := compactOperatorStarSubalgebra_le_iff_range_of_injective
    (hclosedT := by infer_instance) T hT phi.gnsRepresentation
      phi.isIrreducible_gnsRepresentation hfaith
  have htransport :
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ S ↔
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K ≤ T :=
    hSR.trans hTR.symm
  have hScompact : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ S :=
    hcompact.elim (fun h => h) htransport.mpr
  have hTcompact : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K ≤ T :=
    htransport.mp hScompact
  obtain ⟨basisIndex, d, _hd⟩ := exists_hilbertBasis ℂ phi.GNS
  have hHL : Nonempty (ι ≃ basisIndex) :=
    nonempty_hilbertBasis_index_equiv_of_normalPart_continuous
      S (NonUnitalStarAlgHom.range phi.gnsRepresentation) hS hR f.toFiniteHomeomorph
        f.continuous_toFun b d
  letI : Nontrivial K :=
    NonUnitalCStarRepresentation.nontrivial_of_isNonzero
      (NonUnitalStarSubalgebraClass.subtype T) hT.1
  obtain ⟨U, _hU⟩ := unitaryEquivalent_inclusion_of_injective
    T (by infer_instance) hTcompact phi.gnsRepresentation
      phi.isIrreducible_gnsRepresentation hfaith
  have hKL : Nonempty (κ ≃ basisIndex) :=
    Cardinal.lift_mk_eq'.mp
      (c.lift_mk_eq_of_continuous_linear_equiv d U.toContinuousLinearEquiv)
  obtain ⟨q⟩ := hHL
  obtain ⟨rι⟩ := hKL
  exact Cardinal.lift_mk_eq'.mpr ⟨q.trans rι.symm⟩

end MathlibAnnex.Analysis.CStarAlgebra
