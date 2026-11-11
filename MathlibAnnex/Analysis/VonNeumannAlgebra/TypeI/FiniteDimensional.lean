/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.

The natural-number minimization below adapts the proof route of
NonUnitalCStarRepresentation.exists_isMinimalStarProjection_le in
MathlibAnnex/Analysis/CStarAlgebra/Ideal/MinimalCompactCorner.lean at
5cbbf304e651c6c50163a59ba7f9fcf6c22eca4e. Retained upstream notice:
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka

Modification: minimize the ranges of left multiplication on the algebra
itself, not the ranges of represented operators on the ambient Hilbert
space. Equality of these internal ranges is converted to equality of
projections by multiplication, without a compact representation.
-/

import Mathlib.Data.Nat.Find
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeI.FiniteFactor

/-!
# Finite-dimensional von Neumann algebras and finite type II factors

Every nonzero projection in a finite-dimensional von Neumann algebra
dominates an internal minimal projection. The dimension used in the proof
is the dimension of the range of left multiplication on the algebra. The
ambient Hilbert space may have arbitrary dimension.

The existing von Neumann minimal-corner theorem makes these projections
abelian. Thus finite-dimensional von Neumann algebras are type I, including
the zero algebra. For nonzero type II algebras this excludes finite
dimensionality. Together with the existing forward bridge, this identifies
the accepted II₁ predicate with finite type II factorality.
-/

set_option autoImplicit false
noncomputable section

open MathlibAnnex.Analysis.CStarAlgebra
open scoped CStarAlgebra

namespace VonNeumannAlgebra

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Every nonzero projection of a finite-dimensional von Neumann algebra
dominates a minimal projection in the same algebra. The finite-dimensional
space is `M.toStarSubalgebra`, not the ambient representation space. -/
theorem exists_isMinimalStarProjection_le_of_finiteDimensional
    (M : VonNeumannAlgebra H) [FiniteDimensional ℂ M.toStarSubalgebra]
    {p : M.toStarSubalgebra} (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : M.toStarSubalgebra, IsMinimalStarProjection q ∧ q ≤ p := by
  classical
  let d : M.toStarSubalgebra → ℕ := fun q ↦
    Module.finrank ℂ (LinearMap.range (LinearMap.mulLeft ℂ q))
  let P : ℕ → Prop := fun n ↦
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≤ p ∧ d q = n
  have hP : ∃ n : ℕ, P n := ⟨d p, p, hp, hp0, le_rfl, rfl⟩
  obtain ⟨q, hq, hq0, hqp, hdq⟩ := Nat.find_spec hP
  refine ⟨q, ⟨hq, hq0, ?_⟩, hqp⟩
  intro r hr hr0 hrq
  have hqr : q * r = r := (hr.le_iff_mul_eq_right hq).mp hrq
  have hrq' : r * q = r := (hr.le_iff_mul_eq_left hq).mp hrq
  have hle : LinearMap.range (LinearMap.mulLeft ℂ r) ≤
      LinearMap.range (LinearMap.mulLeft ℂ q) := by
    rintro y ⟨x, rfl⟩
    refine ⟨r * x, ?_⟩
    change q * (r * x) = r * x
    rw [← mul_assoc, hqr]
  have hdim : Module.finrank ℂ (LinearMap.range (LinearMap.mulLeft ℂ q)) ≤
      Module.finrank ℂ (LinearMap.range (LinearMap.mulLeft ℂ r)) := by
    change d q ≤ d r
    rw [hdq]
    exact Nat.find_min' hP ⟨r, hr, hr0, hrq.trans hqp, rfl⟩
  have hrange : LinearMap.range (LinearMap.mulLeft ℂ r) =
      LinearMap.range (LinearMap.mulLeft ℂ q) :=
    Submodule.eq_of_le_of_finrank_le hle hdim
  have hqmem : q ∈ LinearMap.range (LinearMap.mulLeft ℂ r) := by
    rw [hrange]
    exact ⟨1, mul_one q⟩
  obtain ⟨x, hx⟩ := hqmem
  change r * x = q at hx
  calc
    r = r * q := hrq'.symm
    _ = r * (r * x) := by rw [hx]
    _ = (r * r) * x := (mul_assoc _ _ _).symm
    _ = r * x := by rw [hr.isIdempotentElem.eq]
    _ = q := hx

/-- A nonzero finite-dimensional von Neumann algebra contains a nonzero
minimal projection. Nontriviality concerns the algebra subtype. -/
theorem exists_isMinimalStarProjection_of_finiteDimensional
    (M : VonNeumannAlgebra H) [FiniteDimensional ℂ M.toStarSubalgebra]
    [Nontrivial M.toStarSubalgebra] :
    ∃ p : M.toStarSubalgebra, IsMinimalStarProjection p := by
  obtain ⟨p, hp, _⟩ :=
    exists_isMinimalStarProjection_le_of_finiteDimensional M
      (IsStarProjection.one M.toStarSubalgebra) one_ne_zero
  exact ⟨p, hp⟩

/-- A minimal projection in a von Neumann algebra is abelian. The scalar
corner statement is the existing von Neumann theorem; no scalar-corner
assertion for arbitrary C-star algebras is used. -/
theorem isAbelianProjection_of_isMinimalStarProjection
    (M : VonNeumannAlgebra H) {p : M.toStarSubalgebra}
    (hp : IsMinimalStarProjection p) : IsAbelianProjection M p := by
  refine ⟨hp.1, ?_⟩
  intro a b hpa hap hpb hbp
  obtain ⟨c, hc⟩ := exists_scalar_corner_of_minimal_projection M hp a
  obtain ⟨d, hd⟩ := exists_scalar_corner_of_minimal_projection M hp b
  have ha : a = c • p := by simpa only [hpa, hap] using hc
  have hb : b = d • p := by simpa only [hpb, hbp] using hd
  calc
    a * b = (c * d) • (p * p) := by
      rw [ha, hb, smul_mul_assoc, mul_smul_comm, smul_smul]
    _ = (d * c) • (p * p) := by rw [mul_comm c d]
    _ = b * a := by
      rw [ha, hb, smul_mul_assoc, mul_smul_comm, smul_smul]

/-- A nonzero finite-dimensional von Neumann algebra has a nonzero
internal abelian projection. Its representation may have infinite multiplicity. -/
theorem exists_isAbelianProjection_ne_zero_of_finiteDimensional
    (M : VonNeumannAlgebra H) [FiniteDimensional ℂ M.toStarSubalgebra]
    [Nontrivial M.toStarSubalgebra] :
    ∃ p : M.toStarSubalgebra, IsAbelianProjection M p ∧ p ≠ 0 := by
  obtain ⟨p, hp⟩ := exists_isMinimalStarProjection_of_finiteDimensional M
  exact ⟨p, isAbelianProjection_of_isMinimalStarProjection M hp, hp.2.1⟩

/-- Every finite-dimensional von Neumann algebra is type I. The zero
algebra is allowed because the definition only tests nonzero projections. -/
theorem isTypeI_of_finiteDimensional
    (M : VonNeumannAlgebra H) [FiniteDimensional ℂ M.toStarSubalgebra] :
    IsTypeI M := by
  intro p hp hp0
  obtain ⟨q, hq, hqp⟩ :=
    exists_isMinimalStarProjection_le_of_finiteDimensional M hp hp0
  exact ⟨q, isAbelianProjection_of_isMinimalStarProjection M hq, hq.2.1,
    (hq.1.le_iff_mul_eq_left hp).mp hqp⟩

/-- A nonzero type II von Neumann algebra is infinite-dimensional as an
algebra. The nonzero hypothesis excludes the permitted zero type II component. -/
theorem IsTypeII.not_finiteDimensional
    {M : VonNeumannAlgebra H} [Nontrivial M.toStarSubalgebra] (hM : IsTypeII M) :
    ¬ FiniteDimensional ℂ M.toStarSubalgebra := by
  intro hdim
  letI : FiniteDimensional ℂ M.toStarSubalgebra := hdim
  obtain ⟨p, hp, hp0⟩ := exists_isAbelianProjection_ne_zero_of_finiteDimensional M
  exact hp0 (hM.2 p hp (mul_one p))

/-- A finite type II factor satisfies the accepted II₁ predicate. The
factor's existing nonzero condition supplies the nontrivial algebra, and
the preceding theorem supplies the required algebraic infinite dimension. -/
theorem isTypeII1_of_isFactor_of_isFinite_of_isTypeII
    (M : VonNeumannAlgebra H) (hfactor : IsFactor M)
    (hfinite : IsFinite M) (htype : IsTypeII M) : IsTypeII1 M := by
  have hone : (1 : M.toStarSubalgebra) ≠ 0 := by
    intro h
    exact hfactor.1 (congrArg Subtype.val h)
  letI : Nontrivial M.toStarSubalgebra := ⟨⟨1, 0, hone⟩⟩
  exact ⟨hfactor, hfinite, htype.not_finiteDimensional⟩

/-- The accepted II₁ predicate is exactly finite type II factorality.
Both sides use the existing predicates without replacement definitions. -/
theorem isTypeII1_iff_isFactor_and_isFinite_and_isTypeII
    (M : VonNeumannAlgebra H) :
    IsTypeII1 M ↔ IsFactor M ∧ IsFinite M ∧ IsTypeII M := by
  constructor
  · intro hM
    exact ⟨hM.1, hM.2.1, hM.isTypeII⟩
  · rintro ⟨hfactor, hfinite, htype⟩
    exact isTypeII1_of_isFactor_of_isFinite_of_isTypeII M hfactor hfinite htype

/-- For a fixed finite factor, the accepted II₁ condition and the general
type II condition agree. -/
theorem isTypeII1_iff_isTypeII_of_isFactor_of_isFinite
    (M : VonNeumannAlgebra H) (hfactor : IsFactor M) (hfinite : IsFinite M) :
    IsTypeII1 M ↔ IsTypeII M :=
  ⟨fun hM ↦ hM.isTypeII,
    fun htype ↦ isTypeII1_of_isFactor_of_isFinite_of_isTypeII M hfactor hfinite htype⟩

end VonNeumannAlgebra

