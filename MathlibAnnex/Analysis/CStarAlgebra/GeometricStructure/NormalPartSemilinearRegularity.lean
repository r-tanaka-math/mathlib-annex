/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartSemilinearSubspace
import MathlibAnnex.Analysis.Normed.Module.SemilinearRegularity
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Regularity of the selected normal-part semilinear factors

The lifts are exactly those already selected in `NormalPartSemilinearRealization`.
The forward closure continuity of the specified normal-part map gives closed
images of target hyperplanes under their INVERSES. The generic regularity
theorem is therefore applied to those inverses with the inverse scalar maps.
The individual scalar classifications are recovered for the original maps.
No equality of the two scalar maps, reverse closure continuity, or reselection
of the vector-space maps is used. The infinite-dimensional premise is on H;
it is transported to K by the existing finite-dimensional comparison.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped ComplexConjugate

namespace MathlibAnnex.Analysis.CStarAlgebra

local instance (σ : ℂ ≃+* ℂ) : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv σ
local instance (σ : ℂ ≃+* ℂ) : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm σ

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable (T : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K))
variable [IsClosed (S : Set (H →L[ℂ] H))] [IsClosed (T : Set (K →L[ℂ] K))]
variable (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
variable (hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T))
variable (e : ClosureSpace.FiniteHomeomorph
  ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
  ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)))

include hS hT e

/-- Finite dimensionality of the target would contradict that of the source.
This uses the actual normal-part comparison, not the cardinality of its points. -/
theorem not_finiteDimensional_of_normalPart_finiteHomeomorph
    (hH : ¬ FiniteDimensional ℂ H) : ¬ FiniteDimensional ℂ K := by
  intro hK
  exact hH ((finite_and_finrank_eq_of_normalPart_finiteHomeomorph S T hS hT e
    (Or.inr hK)).1)

/-- Both algebraic ranks are infinite. This is not a Hilbert-basis cardinality
statement, nor an inference from a zero `finrank`. -/
theorem aleph0_le_rank_of_normalPart_finiteHomeomorph
    (hH : ¬ FiniteDimensional ℂ H) :
    Cardinal.aleph0 ≤ Module.rank ℂ H ∧ Cardinal.aleph0 ≤ Module.rank ℂ K := by
  constructor
  · apply le_of_not_gt
    intro h
    exact hH (Module.rank_lt_aleph0_iff.mp h)
  · apply le_of_not_gt
    intro h
    exact not_finiteDimensional_of_normalPart_finiteHomeomorph S T hS hT e hH
      (Module.rank_lt_aleph0_iff.mp h)

/-- The dimension-three inputs for the existing selected lifts follow from
infinite dimensionality; they are not new supplied hypotheses. -/
theorem three_le_rank_of_normalPart_finiteHomeomorph
    (hH : ¬ FiniteDimensional ℂ H) :
    3 ≤ Module.rank ℂ H ∧ 3 ≤ Module.rank ℂ K := by
  have h := aleph0_le_rank_of_normalPart_finiteHomeomorph S T hS hT e hH
  exact ⟨(show (3 : Cardinal.{u}) < Cardinal.aleph0 from
      Cardinal.natCast_lt_aleph0).le.trans h.1,
    (show (3 : Cardinal.{v}) < Cardinal.aleph0 from
      Cardinal.natCast_lt_aleph0).le.trans h.2⟩

variable (hdim : 3 ≤ Module.rank ℂ H)
variable (hH : ¬ FiniteDimensional ℂ H)
variable (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
  ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv)

include hH hcont

/-- Apply regularity to the inverse of the SAME selected first lift.
The scalar in this application is explicitly the inverse scalar equivalence. -/
theorem normalPartFirstSemilinearEquiv_symm_regularity :
    let σ := normalPartFirstScalarEquiv S T hS hT e hdim
    let U := normalPartFirstSemilinearEquiv S T hS hT e hdim
    (σ.symm = RingEquiv.refl ℂ ∨ σ.symm = starRingAut (R := ℂ)) ∧
      Continuous U.symm ∧ Continuous U ∧
      ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
        (∀ z, ‖U.symm z‖ ≤ C * ‖z‖) ∧ (∀ x, ‖U x‖ ≤ D * ‖x‖) := by
  let σ := normalPartFirstScalarEquiv S T hS hT e hdim
  let U := normalPartFirstSemilinearEquiv S T hS hT e hdim
  have hK := not_finiteDimensional_of_normalPart_finiteHomeomorph S T hS hT e hH
  have hclosed : ∀ N : Submodule ℂ K, IsCoatom N → IsClosed (N : Set K) →
      IsClosed (U.symm '' (N : Set K)) := by
    intro N _ hN
    exact isClosed_image_symm_normalPartFirstSemilinearEquiv
      S T hS hT e hdim hcont N hN
  convert LinearEquiv.regularity_of_isClosed_image_hyperplane
    (σ := σ.symm) U.symm hK hclosed using 1 <;> rfl

/-- Classification of the ORIGINAL first scalar map, obtained by taking the
inverse of the scalar classification for the inverse lift. -/
theorem normalPartFirstScalarEquiv_eq_refl_or_star :
    normalPartFirstScalarEquiv S T hS hT e hdim = RingEquiv.refl ℂ ∨
      normalPartFirstScalarEquiv S T hS hT e hdim = starRingAut (R := ℂ) := by
  have h := (normalPartFirstSemilinearEquiv_symm_regularity
    S T hS hT e hdim hH hcont).1
  rcases h with h | h
  · left
    simpa only [RingEquiv.symm_symm, RingEquiv.symm_refl] using
      congrArg (fun ρ : ℂ ≃+* ℂ => ρ.symm) h
  · right
    have hstar : (starRingAut (R := ℂ)).symm = starRingAut (R := ℂ) := by
      ext z
      rfl
    simpa only [RingEquiv.symm_symm, hstar] using
      congrArg (fun ρ : ℂ ≃+* ℂ => ρ.symm) h

/-- The first scalar map is continuous as a conclusion, not an input. -/
theorem continuous_normalPartFirstScalarEquiv :
    Continuous (normalPartFirstScalarEquiv S T hS hT e hdim) := by
  rcases normalPartFirstScalarEquiv_eq_refl_or_star
      S T hS hT e hdim hH hcont with h | h
  · rw [h]
    exact continuous_id
  · rw [h]
    change Continuous (star : ℂ → ℂ)
    exact continuous_star

/-- Continuity of the original selected first lift. -/
theorem continuous_normalPartFirstSemilinearEquiv :
    Continuous (normalPartFirstSemilinearEquiv S T hS hT e hdim) :=
  (normalPartFirstSemilinearEquiv_symm_regularity S T hS hT e hdim hH hcont).2.2.1

/-- Continuity of the inverse of the SAME selected first lift. -/
theorem continuous_symm_normalPartFirstSemilinearEquiv :
    Continuous (normalPartFirstSemilinearEquiv S T hS hT e hdim).symm :=
  (normalPartFirstSemilinearEquiv_symm_regularity S T hS hT e hdim hH hcont).2.1

/-- Positive norm bounds in the forward/inverse order of the original first
lift; the two constants supplied for the inverse application are interchanged. -/
theorem exists_bounds_normalPartFirstSemilinearEquiv :
    let U := normalPartFirstSemilinearEquiv S T hS hT e hdim
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      (∀ x, ‖U x‖ ≤ C * ‖x‖) ∧ (∀ z, ‖U.symm z‖ ≤ D * ‖z‖) := by
  obtain ⟨C, D, hC, hD, hi, hf⟩ :=
    (normalPartFirstSemilinearEquiv_symm_regularity S T hS hT e hdim hH hcont).2.2.2
  exact ⟨D, C, hD, hC, hf, hi⟩

/-- Apply regularity to the inverse of the SAME selected second lift.
The scalar in this application is explicitly the inverse scalar equivalence. -/
theorem normalPartSecondSemilinearEquiv_symm_regularity :
    let σ := normalPartSecondScalarEquiv S T hS hT e hdim
    let U := normalPartSecondSemilinearEquiv S T hS hT e hdim
    (σ.symm = RingEquiv.refl ℂ ∨ σ.symm = starRingAut (R := ℂ)) ∧
      Continuous U.symm ∧ Continuous U ∧
      ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
        (∀ z, ‖U.symm z‖ ≤ C * ‖z‖) ∧ (∀ x, ‖U x‖ ≤ D * ‖x‖) := by
  let σ := normalPartSecondScalarEquiv S T hS hT e hdim
  let U := normalPartSecondSemilinearEquiv S T hS hT e hdim
  have hK := not_finiteDimensional_of_normalPart_finiteHomeomorph S T hS hT e hH
  have hclosed : ∀ N : Submodule ℂ K, IsCoatom N → IsClosed (N : Set K) →
      IsClosed (U.symm '' (N : Set K)) := by
    intro N _ hN
    exact isClosed_image_symm_normalPartSecondSemilinearEquiv
      S T hS hT e hdim hcont N hN
  convert LinearEquiv.regularity_of_isClosed_image_hyperplane
    (σ := σ.symm) U.symm hK hclosed using 1 <;> rfl

/-- Classification of the ORIGINAL second scalar map, obtained by taking the
inverse of the scalar classification for the inverse lift. -/
theorem normalPartSecondScalarEquiv_eq_refl_or_star :
    normalPartSecondScalarEquiv S T hS hT e hdim = RingEquiv.refl ℂ ∨
      normalPartSecondScalarEquiv S T hS hT e hdim = starRingAut (R := ℂ) := by
  have h := (normalPartSecondSemilinearEquiv_symm_regularity
    S T hS hT e hdim hH hcont).1
  rcases h with h | h
  · left
    simpa only [RingEquiv.symm_symm, RingEquiv.symm_refl] using
      congrArg (fun ρ : ℂ ≃+* ℂ => ρ.symm) h
  · right
    have hstar : (starRingAut (R := ℂ)).symm = starRingAut (R := ℂ) := by
      ext z
      rfl
    simpa only [RingEquiv.symm_symm, hstar] using
      congrArg (fun ρ : ℂ ≃+* ℂ => ρ.symm) h

/-- The second scalar map is continuous as a conclusion, not an input. -/
theorem continuous_normalPartSecondScalarEquiv :
    Continuous (normalPartSecondScalarEquiv S T hS hT e hdim) := by
  rcases normalPartSecondScalarEquiv_eq_refl_or_star
      S T hS hT e hdim hH hcont with h | h
  · rw [h]
    exact continuous_id
  · rw [h]
    change Continuous (star : ℂ → ℂ)
    exact continuous_star

/-- Continuity of the original selected second lift. -/
theorem continuous_normalPartSecondSemilinearEquiv :
    Continuous (normalPartSecondSemilinearEquiv S T hS hT e hdim) :=
  (normalPartSecondSemilinearEquiv_symm_regularity S T hS hT e hdim hH hcont).2.2.1

/-- Continuity of the inverse of the SAME selected second lift. -/
theorem continuous_symm_normalPartSecondSemilinearEquiv :
    Continuous (normalPartSecondSemilinearEquiv S T hS hT e hdim).symm :=
  (normalPartSecondSemilinearEquiv_symm_regularity S T hS hT e hdim hH hcont).2.1

/-- Positive norm bounds in the forward/inverse order of the original second
lift; the two constants supplied for the inverse application are interchanged. -/
theorem exists_bounds_normalPartSecondSemilinearEquiv :
    let U := normalPartSecondSemilinearEquiv S T hS hT e hdim
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      (∀ x, ‖U x‖ ≤ C * ‖x‖) ∧ (∀ z, ‖U.symm z‖ ≤ D * ‖z‖) := by
  obtain ⟨C, D, hC, hD, hi, hf⟩ :=
    (normalPartSecondSemilinearEquiv_symm_regularity S T hS hT e hdim hH hcont).2.2.2
  exact ⟨D, C, hD, hC, hf, hi⟩

/-- Each selected scalar is individually identity or conjugation. The statement
intentionally retains all four possible pairs; same-type is a separate theorem. -/
theorem normalPart_semilinear_factors_scalar_types :
    (normalPartFirstScalarEquiv S T hS hT e hdim = RingEquiv.refl ℂ ∨
      normalPartFirstScalarEquiv S T hS hT e hdim = starRingAut (R := ℂ)) ∧
    (normalPartSecondScalarEquiv S T hS hT e hdim = RingEquiv.refl ℂ ∨
      normalPartSecondScalarEquiv S T hS hT e hdim = starRingAut (R := ℂ)) :=
  ⟨normalPartFirstScalarEquiv_eq_refl_or_star S T hS hT e hdim hH hcont,
    normalPartSecondScalarEquiv_eq_refl_or_star S T hS hT e hdim hH hcont⟩

/-- Four actual continuous functions, with no continuity assumption on e inverse. -/
theorem normalPart_semilinear_factors_continuous :
    Continuous (normalPartFirstSemilinearEquiv S T hS hT e hdim) ∧
    Continuous (normalPartFirstSemilinearEquiv S T hS hT e hdim).symm ∧
    Continuous (normalPartSecondSemilinearEquiv S T hS hT e hdim) ∧
    Continuous (normalPartSecondSemilinearEquiv S T hS hT e hdim).symm :=
  ⟨continuous_normalPartFirstSemilinearEquiv S T hS hT e hdim hH hcont,
    continuous_symm_normalPartFirstSemilinearEquiv S T hS hT e hdim hH hcont,
    continuous_normalPartSecondSemilinearEquiv S T hS hT e hdim hH hcont,
    continuous_symm_normalPartSecondSemilinearEquiv S T hS hT e hdim hH hcont⟩

end MathlibAnnex.Analysis.CStarAlgebra
