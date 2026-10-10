/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.HilbertBasisCardinality
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartSemilinearBounded

/-!
# Hilbert-basis cardinality from a continuous finite normal-part homeomorphism

The infinite-dimensional case uses the SAME selected first lift and the
existing individual linear/conjugate-linear alternatives. Equality of the two
scalar types, operator-algebra inclusion, and the peer's terminal classification
are not used. The finite-dimensional case uses the received finite-dimensional
comparison and then actual finite Hilbert bases. In particular, dimensions one
and two do not pass through a projective fundamental theorem.

The conclusion compares the indices of arbitrary Hilbert bases in independent
universes. It does not claim that the selected map is an isometry, or that the
original closure-space equivalence has continuous inverse.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped Cardinal

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v uI uJ
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι : Type uI} {κ : Type uJ}
variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable (T : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K))
variable [IsClosed (S : Set (H →L[ℂ] H))] [IsClosed (T : Set (K →L[ℂ] K))]
variable (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
variable (hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T))
variable (e : ClosureSpace.FiniteHomeomorph
  ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
  ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)))

include hS hT in
/-- In the infinite-dimensional case, the received alternative supplies a
continuous linear or conjugate-linear bundle with exactly the selected first
map and exactly its inverse. The generic invariant is applied to that bundle. -/
theorem hilbertBasis_lift_mk_eq_of_normalPart_continuous_of_not_finiteDimensional
    (hH : ¬ FiniteDimensional ℂ H)
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv)
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K) :
    Cardinal.lift.{uJ} (#ι) = Cardinal.lift.{uI} (#κ) := by
  have hdim : 3 ≤ Module.rank ℂ H :=
    (three_le_rank_of_normalPart_finiteHomeomorph S T hS hT e hH).1
  rcases exists_continuousLinearEquiv_or_conj_eq_normalPartFirstSemilinearEquiv
      S T hS hT e hdim hH hcont with ⟨U, hU, hUinv⟩ | ⟨U, hU, hUinv⟩
  · exact b.lift_mk_eq_of_continuous_linear_equiv c U
  · exact b.lift_mk_eq_of_continuous_conjugate_linear_equiv c U

include hS hT in
/-- A finite normal-part homeomorphism that is fully continuous in the forward
direction preserves genuine Hilbert-basis index cardinality. The inverse is not
assumed fully continuous. Finite dimension, including dimension one and two,
is split off before the selected semilinear-lift argument. -/
theorem hilbertBasis_lift_mk_eq_of_normalPart_continuous
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv)
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K) :
    Cardinal.lift.{uJ} (#ι) = Cardinal.lift.{uI} (#κ) := by
  classical
  by_cases hH : FiniteDimensional ℂ H
  · have hd := finite_and_finrank_eq_of_normalPart_finiteHomeomorph
      S T hS hT e (Or.inl hH)
    letI : FiniteDimensional ℂ H := hd.1
    letI : FiniteDimensional ℂ K := hd.2.1
    exact b.lift_mk_eq_of_finrank_eq c hd.2.2
  · exact hilbertBasis_lift_mk_eq_of_normalPart_continuous_of_not_finiteDimensional
      S T hS hT e hH hcont b c

include hS hT in
/-- An actual equivalence of Hilbert-basis indices, as a consequence rather
than a supplied Hilbert-dimension label. -/
theorem nonempty_hilbertBasis_index_equiv_of_normalPart_continuous
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv)
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K) : Nonempty (ι ≃ κ) :=
  Cardinal.lift_mk_eq'.mp
    (hilbertBasis_lift_mk_eq_of_normalPart_continuous S T hS hT e hcont b c)

end MathlibAnnex.Analysis.CStarAlgebra
