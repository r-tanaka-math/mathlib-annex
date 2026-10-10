/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.SimultaneousExactInterpolation
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.Representatives
import MathlibAnnex.Analysis.InnerProductSpace.CompactOperatorAlgebra
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import MathlibAnnex.Analysis.CStarAlgebra.Representation.FiniteDimensionalTransport

/-!
# Compact operators in actual irreducible representation ranges

The conditions in this file are representation-side conditions, not definitions
of a geometric structure space, nor a replacement for an independent type-I
condition. The finite-dimensional result is proved by exact interpolation in
the original nonunital algebra. Unitary transport uses an actual intertwining
linear isometry; equality of primitive kernels is not a substitute.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- An irreducible representation on a finite-dimensional Hilbert space has
full operator range, without assuming a unit in the original algebra. -/
theorem surjective_of_isIrreducible_of_finiteDimensional [FiniteDimensional ℂ H]
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    Function.Surjective pi := by
  have hs : ∀ T : H →L[ℂ] H, IsSelfAdjoint T → ∃ a : A, pi a = T := by
    intro T hT
    obtain ⟨a, _ha, _hn, he⟩ :=
      exists_selfAdjoint_norm_le_two_mul_forall_eq_on
        (I := Unit) (H := fun _ => H) (fun _ => pi) (fun _ => hpi)
        (fun i j hij => (hij (Subsingleton.elim i j)).elim)
        (fun _ => (⊤ : Submodule ℂ H)) (fun _ => T) (fun _ => hT)
        ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
    exact ⟨a, ContinuousLinearMap.ext (fun x => he () x (Submodule.mem_top))⟩
  intro T
  have hR : IsSelfAdjoint (T + star T) := by
    change star (T + star T) = T + star T
    rw [star_add, star_star, add_comm]
  have hI : IsSelfAdjoint (Complex.I • (T - star T)) := by
    change star (Complex.I • (T - star T)) = Complex.I • (T - star T)
    rw [star_smul, show star Complex.I = -Complex.I by simp, star_sub, star_star,
      neg_smul, smul_sub, smul_sub]
    abel
  obtain ⟨a, ha⟩ := hs (T + star T) hR
  obtain ⟨b, hb⟩ := hs (Complex.I • (T - star T)) hI
  refine ⟨(1 / 2 : ℂ) • a + (-Complex.I / 2) • b, ?_⟩
  rw [map_add, map_smul, map_smul, ha, hb, smul_smul]
  have hc : (-Complex.I / 2) * Complex.I = (1 / 2 : ℂ) := by
    calc
      (-Complex.I / 2) * Complex.I = -(Complex.I * Complex.I) / 2 := by ring
      _ = (1 / 2 : ℂ) := by rw [← pow_two, Complex.I_sq]; norm_num
  rw [hc, ← smul_add]
  have hsum : (T + star T) + (T - star T) = (2 : ℂ) • T := by
    rw [two_smul]
    abel
  rw [hsum, smul_smul]
  norm_num

/-- Compactness of each represented operator is invariant under an actual
unitary intertwiner, with the Hilbert universes independent. -/
theorem UnitaryEquivalent.isCompactOperator_iff
    {pi : NonUnitalCStarRepresentation A H} {rho : NonUnitalCStarRepresentation A K}
    (h : pi.UnitaryEquivalent rho) (a : A) :
    IsCompactOperator (pi a) ↔ IsCompactOperator (rho a) := by
  obtain ⟨U, hU⟩ := h
  have he : rho a = U.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      (pi a) ∘L U.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
    ext y
    simpa using (hU a (U.symm y)).symm
  have hi : pi a = U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      (rho a) ∘L U.toContinuousLinearEquiv.toContinuousLinearMap := by
    ext x
    apply U.injective
    simpa using hU a x
  constructor
  · intro ha
    rw [he]
    exact (ha.comp_clm U.symm.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
      U.toContinuousLinearEquiv.toContinuousLinearMap
  · intro ha
    rw [hi]
    exact (ha.comp_clm U.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
      U.symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- An actual unitary equivalence transports compact containment in the range.
The compact operator is explicitly conjugated and an actual algebra preimage
is then selected. Neither representation is assumed faithful. -/
theorem UnitaryEquivalent.compactOperatorStarSubalgebra_le_range
    {pi : NonUnitalCStarRepresentation A H} {rho : NonUnitalCStarRepresentation A K}
    (h : pi.UnitaryEquivalent rho)
    (hc : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ (NonUnitalStarAlgHom.range pi)) :
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K ≤ (NonUnitalStarAlgHom.range rho) := by
  obtain ⟨U, hU⟩ := h
  intro T hT
  let R : H →L[ℂ] H := U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    T ∘L U.toContinuousLinearEquiv.toContinuousLinearMap
  have hR : IsCompactOperator R :=
    (hT.comp_clm U.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
      U.symm.toContinuousLinearEquiv.toContinuousLinearMap
  obtain ⟨a, ha⟩ := (NonUnitalStarAlgHom.mem_range pi).1 (hc hR)
  apply (NonUnitalStarAlgHom.mem_range rho).2
  refine ⟨a, ?_⟩
  ext y
  calc
    rho a y = U (pi a (U.symm y)) := by simpa using (hU a (U.symm y)).symm
    _ = T y := by rw [ha]; simp [R]

/-- The representation-side GCR condition is preserved and reflected. -/
theorem UnitaryEquivalent.compactOperatorStarSubalgebra_le_range_iff
    {pi : NonUnitalCStarRepresentation A H} {rho : NonUnitalCStarRepresentation A K}
    (h : pi.UnitaryEquivalent rho) :
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ (NonUnitalStarAlgHom.range pi) ↔
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K ≤ (NonUnitalStarAlgHom.range rho) :=
  ⟨h.compactOperatorStarSubalgebra_le_range, h.symm.compactOperatorStarSubalgebra_le_range⟩

/-- Equality of an image with the compact operator algebra transports through
an actual unitary, without assuming either representation faithful. -/
theorem UnitaryEquivalent.range_eq_compactOperatorStarSubalgebra
    {pi : NonUnitalCStarRepresentation A H} {rho : NonUnitalCStarRepresentation A K}
    (h : pi.UnitaryEquivalent rho)
    (hp : (NonUnitalStarAlgHom.range pi) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) :
    (NonUnitalStarAlgHom.range rho) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K := by
  apply le_antisymm
  · intro T hT
    obtain ⟨a, rfl⟩ := (NonUnitalStarAlgHom.mem_range rho).1 hT
    exact (h.isCompactOperator_iff a).1 (by
      change pi a ∈ ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H
      rw [← hp]
      exact (NonUnitalStarAlgHom.mem_range pi).2 ⟨a, rfl⟩)
  · exact h.compactOperatorStarSubalgebra_le_range hp.ge

/-- The representation-side CCR condition is preserved and reflected. -/
theorem UnitaryEquivalent.range_eq_compactOperatorStarSubalgebra_iff
    {pi : NonUnitalCStarRepresentation A H} {rho : NonUnitalCStarRepresentation A K}
    (h : pi.UnitaryEquivalent rho) :
    (NonUnitalStarAlgHom.range pi) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ↔
      (NonUnitalStarAlgHom.range rho) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K :=
  ⟨h.range_eq_compactOperatorStarSubalgebra, h.symm.range_eq_compactOperatorStarSubalgebra⟩

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

namespace MathlibAnnex.Analysis.CStarAlgebra

universe v
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The concrete finite-dimensional irreducible algebra is all of B(H).
Dimensions one and two are included without projective semilinear realization. -/
theorem eq_top_of_isIrreducible_subtype_of_finiteDimensional [FiniteDimensional ℂ H]
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    [hclosed : IsClosed (S : Set (H →L[ℂ] H))]
    (hS : letI : NonUnitalCStarAlgebra S :=
        NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S (h_closed := hclosed)
      NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S)) : S = ⊤ := by
  letI : NonUnitalCStarAlgebra S :=
    NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S (h_closed := hclosed)
  apply SetLike.ext
  intro T
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨a, ha⟩ := NonUnitalCStarRepresentation.surjective_of_isIrreducible_of_finiteDimensional
      (NonUnitalStarSubalgebraClass.subtype S) hS T
    exact ha ▸ a.property

end MathlibAnnex.Analysis.CStarAlgebra
