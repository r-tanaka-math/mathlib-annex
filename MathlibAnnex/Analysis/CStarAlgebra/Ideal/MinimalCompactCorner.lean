/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactlyRepresented
import MathlibAnnex.Analysis.CStarAlgebra.Ideal.Unitization
import MathlibAnnex.Analysis.CStarAlgebra.Ideal.ClosedStarIdeal
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

/-!
# Minimal projections below finite-rank represented projections

A faithful compact representation first supplies a nonzero finite-rank
projection.  Among all nonzero source projections below it we minimize the
finite dimension of the represented range.  Projection order becomes range
inclusion under the representation, so a proper nonzero subprojection would
have strictly smaller represented rank.

The same argument is applied inside an arbitrary nonzero norm-closed C-star
subalgebra.  For a norm-closed two-sided C-star ideal, absorption shows that a
subprojection of an ideal projection remains in the ideal; hence minimality in
the ideal is minimality in the ambient algebra.  No ambient rank-one projection
is assumed to belong to the algebra.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open Set Module
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Minimality in the lattice of nonzero star projections. -/
def IsMinimalStarProjection (p : A) : Prop :=
  IsStarProjection p ∧ p ≠ 0 ∧
    ∀ q : A, IsStarProjection q → q ≠ 0 → q ≤ p → q = p

namespace IsMinimalStarProjection

variable {p : A}

theorem isStarProjection (hp : IsMinimalStarProjection p) : IsStarProjection p := hp.1

theorem ne_zero (hp : IsMinimalStarProjection p) : p ≠ 0 := hp.2.1

theorem eq_of_le (hp : IsMinimalStarProjection p) {q : A}
    (hq : IsStarProjection q) (hq0 : q ≠ 0) (hqp : q ≤ p) : q = p :=
  hp.2.2 q hq hq0 hqp

end IsMinimalStarProjection

namespace NonUnitalCStarRepresentation

/-- The natural-number rank of the represented range.  It is used only when
that range is known finite-dimensional. -/
def projectionRangeRank (pi : NonUnitalCStarRepresentation A H) (p : A) : ℕ :=
  Module.finrank ℂ (LinearMap.range (pi p).toLinearMap)

/-- Projection order gives inclusion of represented ranges. -/
theorem range_le_range_of_starProjection_le
    (pi : NonUnitalCStarRepresentation A H) {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hqp : q ≤ p) :
    LinearMap.range (pi q).toLinearMap ≤ LinearMap.range (pi p).toLinearMap := by
  have hmul : p * q = q := (hq.le_iff_mul_eq_right hp).1 hqp
  rintro y ⟨x, rfl⟩
  refine ⟨pi q x, ?_⟩
  change pi p (pi q x) = pi q x
  simpa [map_mul, ContinuousLinearMap.mul_apply] using
    congrArg (fun a : A => pi a x) hmul

/-- Equal ranges determine equal star projections under a faithful
representation. -/
theorem eq_of_range_eq_of_isStarProjection
    (pi : NonUnitalCStarRepresentation A H) (hpi : Function.Injective pi)
    {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hrange : LinearMap.range (pi p).toLinearMap =
      LinearMap.range (pi q).toLinearMap) : p = q := by
  apply hpi
  have hp' : IsStarProjection (pi p) := hp.map pi
  have hq' : IsStarProjection (pi q) := hq.map pi
  obtain ⟨hpRange, hpp⟩ :=
    isStarProjection_iff_eq_starProjection_range.mp hp'
  obtain ⟨hqRange, hqq⟩ :=
    isStarProjection_iff_eq_starProjection_range.mp hq'
  letI : (pi p).range.HasOrthogonalProjection := hpRange
  letI : (pi q).range.HasOrthogonalProjection := hqRange
  have hrange' : (pi p).range = (pi q).range := hrange
  calc
    pi p = (pi p).range.starProjection := hpp
    _ = (pi q).range.starProjection := by simp only [hrange']
    _ = pi q := hqq.symm

/-- A subprojection of a represented finite-rank projection is again
finite-rank. -/
theorem finiteDimensional_range_of_starProjection_le
    (pi : NonUnitalCStarRepresentation A H) {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hqp : q ≤ p)
    (hpfin : FiniteDimensional ℂ (LinearMap.range (pi p).toLinearMap)) :
    FiniteDimensional ℂ (LinearMap.range (pi q).toLinearMap) := by
  letI : FiniteDimensional ℂ (LinearMap.range (pi p).toLinearMap) := hpfin
  exact Submodule.finiteDimensional_of_le
    (pi.range_le_range_of_starProjection_le hp hq hqp)

/-- A nonzero finite-rank represented projection contains an ambient minimal
source projection.  The selected projection is obtained by minimizing the
represented finite rank, not by assuming a rank-one projection is already in
the image. -/
theorem exists_isMinimalStarProjection_le
    (pi : NonUnitalCStarRepresentation A H) (hpi : Function.Injective pi)
    {p : A} (hp : IsStarProjection p) (hp0 : p ≠ 0)
    (hpfin : FiniteDimensional ℂ (LinearMap.range (pi p).toLinearMap)) :
    ∃ q : A, IsMinimalStarProjection q ∧ q ≤ p ∧
      FiniteDimensional ℂ (LinearMap.range (pi q).toLinearMap) := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ q : A, IsStarProjection q ∧ q ≠ 0 ∧ q ≤ p ∧
      FiniteDimensional ℂ (LinearMap.range (pi q).toLinearMap) ∧
      pi.projectionRangeRank q = n
  have hP : ∃ n, P n := by
    refine ⟨pi.projectionRangeRank p, p, hp, hp0, le_rfl, hpfin, rfl⟩
  let n : ℕ := Nat.find hP
  obtain ⟨q, hq, hq0, hqp, hqfin, hqrank⟩ := Nat.find_spec hP
  have hqmin : IsMinimalStarProjection q := by
    refine ⟨hq, hq0, ?_⟩
    intro r hr hr0 hrq
    have hrp : r ≤ p := hrq.trans hqp
    have hrfin : FiniteDimensional ℂ (LinearMap.range (pi r).toLinearMap) :=
      pi.finiteDimensional_range_of_starProjection_le hq hr hrq hqfin
    have hle : LinearMap.range (pi r).toLinearMap ≤
        LinearMap.range (pi q).toLinearMap :=
      pi.range_le_range_of_starProjection_le hq hr hrq
    by_contra hrne
    have hltRange : LinearMap.range (pi r).toLinearMap <
        LinearMap.range (pi q).toLinearMap := by
      refine lt_of_le_of_ne hle ?_
      intro heq
      exact hrne (pi.eq_of_range_eq_of_isStarProjection hpi hr hq heq)
    letI : FiniteDimensional ℂ (LinearMap.range (pi q).toLinearMap) := hqfin
    have hlt : pi.projectionRangeRank r < pi.projectionRangeRank q := by
      unfold projectionRangeRank
      exact Submodule.finrank_lt_finrank_of_lt hltRange
    have hnle : n ≤ pi.projectionRangeRank r :=
      Nat.find_min' hP ⟨r, hr, hr0, hrp, hrfin, rfl⟩
    rw [hqrank] at hlt
    omega
  exact ⟨q, hqmin, hqp, hqfin⟩

end NonUnitalCStarRepresentation

namespace IsMinimalStarProjection

variable {p a : A}

/-- A positive element in the algebraic corner of a minimal projection is a
scalar multiple of that projection.  The scalar relation is proved inside a
faithful compact representation: a nonzero spectral projection of the corner
lies below the minimal projection, hence equals it, and the corresponding
eigenvalue equation determines the original source element by faithfulness. -/
theorem exists_eq_smul_of_nonneg_of_mem_corner
    (hp : IsMinimalStarProjection p)
    (pi : NonUnitalCStarRepresentation A H)
    (hpi : pi.IsCompactlyRepresented)
    (ha : 0 ≤ a) (hcorner : p * a * p = a) :
    ∃ c : ℂ, a = c • p := by
  by_cases ha0 : a = 0
  · exact ⟨0, by simp [ha0]⟩
  obtain ⟨q, hq, hq0, -, μ, -, hμ0, -, -, -, -, hTq⟩ :=
    pi.exists_nonzero_finite_rank_spectral_projection hpi.1 a ha ha0 (hpi.2 a)
  have hpp : p * p = p := hp.isStarProjection.isIdempotentElem.eq
  have hpa : p * a = a := by
    calc
      p * a = p * (p * a * p) := by rw [hcorner]
      _ = (p * p) * a * p := by simp only [mul_assoc]
      _ = p * a * p := by rw [hpp]
      _ = a := hcorner
  have hap : a * p = a := by
    calc
      a * p = (p * a * p) * p := by rw [hcorner]
      _ = p * a * (p * p) := by simp only [mul_assoc]
      _ = p * a * p := by rw [hpp]
      _ = a := hcorner
  have hpaMap : pi p * pi a = pi a := by
    simpa only [map_mul] using congrArg pi hpa
  have hμpq : μ • (pi p * pi q) = μ • pi q := by
    calc
      μ • (pi p * pi q) = pi p * (μ • pi q) := by rw [_root_.mul_smul_comm]
      _ = pi p * (pi a * pi q) := by rw [hTq]
      _ = (pi p * pi a) * pi q := by rw [mul_assoc]
      _ = pi a * pi q := by rw [hpaMap]
      _ = μ • pi q := hTq
  have hpqMap : pi p * pi q = pi q := by
    calc
      pi p * pi q = μ⁻¹ • (μ • (pi p * pi q)) := by
        rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
      _ = μ⁻¹ • (μ • pi q) := by rw [hμpq]
      _ = pi q := by
        rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  have hpq : p * q = q := by
    apply hpi.1
    simpa only [map_mul] using hpqMap
  have hqp : q ≤ p :=
    (hq.le_iff_mul_eq_right hp.isStarProjection).2 hpq
  have hqpEq : q = p := hp.eq_of_le hq hq0 hqp
  subst q
  have hapMap : pi a * pi p = pi a := by
    simpa only [map_mul] using congrArg pi hap
  have haMap : pi a = μ • pi p := hapMap.symm.trans hTq
  refine ⟨μ, hpi.1 ?_⟩
  simpa only [map_smul] using haMap


/-- A self-adjoint element in the corner of a minimal projection is a scalar
multiple of that projection.  This is reduced algebraically to the positive
corner theorem by taking the difference of the two positive squares
`(a + p)⁎(a + p)` and `(a - p)⁎(a - p)`. -/
theorem exists_eq_smul_of_isSelfAdjoint_of_mem_corner
    (hp : IsMinimalStarProjection p)
    (pi : NonUnitalCStarRepresentation A H)
    (hpi : pi.IsCompactlyRepresented)
    (ha : IsSelfAdjoint a) (hcorner : p * a * p = a) :
    ∃ c : ℂ, a = c • p := by
  have hpSelf : IsSelfAdjoint p := hp.isStarProjection.isSelfAdjoint
  have hpp : p * p = p := hp.isStarProjection.isIdempotentElem.eq
  have hpa : p * a = a := by
    calc
      p * a = p * (p * a * p) := by rw [hcorner]
      _ = (p * p) * a * p := by simp only [mul_assoc]
      _ = p * a * p := by rw [hpp]
      _ = a := hcorner
  have hap : a * p = a := by
    calc
      a * p = (p * a * p) * p := by rw [hcorner]
      _ = p * a * (p * p) := by simp only [mul_assoc]
      _ = p * a * p := by rw [hpp]
      _ = a := hcorner
  let u : A := a + p
  let v : A := a - p
  have huSelf : IsSelfAdjoint u := ha.add hpSelf
  have hvSelf : IsSelfAdjoint v := ha.sub hpSelf
  have hpu : p * u = u := by simp [u, mul_add, hpa, hpp]
  have hup : u * p = u := by simp [u, add_mul, hap, hpp]
  have hpv : p * v = v := by simp [v, mul_sub, hpa, hpp]
  have hvp : v * p = v := by simp [v, sub_mul, hap, hpp]
  have huCorner : p * (star u * u) * p = star u * u := by
    rw [huSelf.star_eq]
    calc
      p * (u * u) * p = (p * u) * (u * p) := by simp only [mul_assoc]
      _ = u * u := by rw [hpu, hup]
  have hvCorner : p * (star v * v) * p = star v * v := by
    rw [hvSelf.star_eq]
    calc
      p * (v * v) * p = (p * v) * (v * p) := by simp only [mul_assoc]
      _ = v * v := by rw [hpv, hvp]
  obtain ⟨c, hc⟩ := hp.exists_eq_smul_of_nonneg_of_mem_corner pi hpi
    (star_mul_self_nonneg u) huCorner
  obtain ⟨d, hd⟩ := hp.exists_eq_smul_of_nonneg_of_mem_corner pi hpi
    (star_mul_self_nonneg v) hvCorner
  have hdiff : star u * u - star v * v = (4 : ℂ) • a := by
    rw [huSelf.star_eq, hvSelf.star_eq]
    change (a + p) * (a + p) - (a - p) * (a - p) = (4 : ℂ) • a
    calc
      (a + p) * (a + p) - (a - p) * (a - p) =
          a * p + p * a + a * p + p * a := by noncomm_ring
      _ = (4 : ℂ) • a := by rw [hap, hpa]; module
  have hfour : (4 : ℂ) • a = (c - d) • p := by
    calc
      (4 : ℂ) • a = star u * u - star v * v := hdiff.symm
      _ = c • p - d • p := by rw [hc, hd]
      _ = (c - d) • p := by rw [sub_smul]
  refine ⟨(4 : ℂ)⁻¹ * (c - d), ?_⟩
  calc
    a = (4 : ℂ)⁻¹ • ((4 : ℂ) • a) := by
      rw [smul_smul]
      norm_num
    _ = (4 : ℂ)⁻¹ • ((c - d) • p) := by rw [hfour]
    _ = ((4 : ℂ)⁻¹ * (c - d)) • p := by rw [smul_smul]

/-- Every element in the corner of a minimal projection is a scalar multiple
of the projection.  The real and imaginary self-adjoint parts are treated by
the preceding square decomposition; compactness is used only through the
positive-corner spectral theorem. -/
theorem exists_eq_smul_of_mem_corner
    (hp : IsMinimalStarProjection p)
    (pi : NonUnitalCStarRepresentation A H)
    (hpi : pi.IsCompactlyRepresented)
    (hcorner : p * a * p = a) :
    ∃ c : ℂ, a = c • p := by
  have hpSelf : IsSelfAdjoint p := hp.isStarProjection.isSelfAdjoint
  have hstarCorner : p * star a * p = star a := by
    simpa only [star_mul, hpSelf.star_eq, mul_assoc] using congrArg star hcorner
  let r : A := a + star a
  let s : A := Complex.I • (a - star a)
  have hrSelf : IsSelfAdjoint r := by
    change star (a + star a) = a + star a
    rw [star_add, star_star, add_comm]
  have hsSelf : IsSelfAdjoint s := by
    change star (Complex.I • (a - star a)) = Complex.I • (a - star a)
    rw [star_smul, show star Complex.I = -Complex.I by simp, star_sub, star_star,
      neg_smul, smul_sub, smul_sub]
    abel
  have hrCorner : p * r * p = r := by
    simp only [r, mul_add, add_mul, hcorner, hstarCorner]
  have hsCorner : p * s * p = s := by
    simp only [s, _root_.mul_smul_comm, _root_.smul_mul_assoc, mul_sub, sub_mul,
      hcorner, hstarCorner]
  obtain ⟨c, hc⟩ := hp.exists_eq_smul_of_isSelfAdjoint_of_mem_corner
    pi hpi hrSelf hrCorner
  obtain ⟨d, hd⟩ := hp.exists_eq_smul_of_isSelfAdjoint_of_mem_corner
    pi hpi hsSelf hsCorner
  have hreconstruct : (1 / 2 : ℂ) • r + (-Complex.I / 2) • s = a := by
    dsimp only [r, s]
    rw [smul_smul]
    have hI : (-Complex.I / 2) * Complex.I = (1 / 2 : ℂ) := by
      calc
        (-Complex.I / 2) * Complex.I = -(Complex.I * Complex.I) / 2 := by ring
        _ = (1 / 2 : ℂ) := by rw [← pow_two, Complex.I_sq]; norm_num
    rw [hI, ← smul_add]
    have hsum : (a + star a) + (a - star a) = (2 : ℂ) • a := by
      rw [two_smul]
      abel
    rw [hsum, smul_smul]
    norm_num
  refine ⟨(1 / 2 : ℂ) * c + (-Complex.I / 2) * d, ?_⟩
  calc
    a = (1 / 2 : ℂ) • r + (-Complex.I / 2) • s := hreconstruct.symm
    _ = (1 / 2 : ℂ) • (c • p) + (-Complex.I / 2) • (d • p) := by rw [hc, hd]
    _ = ((1 / 2 : ℂ) * c + (-Complex.I / 2) * d) • p := by
      rw [smul_smul, smul_smul, add_smul]

end IsMinimalStarProjection

namespace NonUnitalStarSubalgebra

variable (B : NonUnitalStarSubalgebra ℂ A)

/-- Restriction of a representation to a concrete nonunital star
subalgebra.  This definition uses only the inherited algebraic structure; a
C-star instance is required only by theorems which apply analytic results to
the restricted map. -/
def restrictedRepresentation (pi : NonUnitalCStarRepresentation A H) :
    B →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
  pi.comp (NonUnitalStarSubalgebraClass.subtype B)

@[simp]
theorem restrictedRepresentation_apply
    (pi : NonUnitalCStarRepresentation A H) (b : B) :
    MathlibAnnex.Analysis.CStarAlgebra.NonUnitalStarSubalgebra.restrictedRepresentation
      B pi b = pi b.1 := rfl

section Closed

variable (hB : IsClosed (B : Set A))

/-- A nonzero norm-closed C-star subalgebra of a faithfully compactly
represented algebra contains a minimal projection in its own projection
lattice.  Its C-star structure and spectral order are the canonical structures
inherited from the closed concrete subalgebra. -/
theorem exists_isMinimalStarProjection
    (pi : NonUnitalCStarRepresentation A H)
    (hpi : pi.IsCompactlyRepresented)
    (hB0 : ∃ b : B, b ≠ 0) :
    letI : NonUnitalCStarAlgebra B :=
      _root_.NonUnitalStarSubalgebra.nonUnitalCStarAlgebra B (h_closed := hB)
    letI : PartialOrder B := _root_.CStarAlgebra.spectralOrder B
    letI : StarOrderedRing B := _root_.CStarAlgebra.spectralOrderedRing B
    ∃ p : B, IsMinimalStarProjection p ∧
      FiniteDimensional ℂ
        (LinearMap.range ((MathlibAnnex.Analysis.CStarAlgebra.NonUnitalStarSubalgebra.restrictedRepresentation
          B pi) p).toLinearMap) := by
  letI : NonUnitalCStarAlgebra B :=
    _root_.NonUnitalStarSubalgebra.nonUnitalCStarAlgebra B (h_closed := hB)
  letI : PartialOrder B := _root_.CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := _root_.CStarAlgebra.spectralOrderedRing B
  let rho : NonUnitalCStarRepresentation B H :=
    MathlibAnnex.Analysis.CStarAlgebra.NonUnitalStarSubalgebra.restrictedRepresentation B pi
  have hrho : rho.IsCompactlyRepresented := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact hpi.1 hxy
    · intro x
      exact hpi.2 x.1
  obtain ⟨x, hx0⟩ := hB0
  let a : B := star x * x
  have ha : @LE.le B (_root_.CStarAlgebra.spectralOrder B).toLE 0 a :=
    star_mul_self_nonneg x
  have ha0 : a ≠ 0 := by
    intro h
    exact hx0 (_root_.star_mul_self_eq_zero.mp h)
  obtain ⟨p, hp, hp0, hpfin⟩ :=
    rho.exists_nonzero_finite_rank_projection_of_isCompactlyRepresented hrho a ha ha0
  obtain ⟨q, hq, -, hqfin⟩ :=
    rho.exists_isMinimalStarProjection_le hrho.1 hp hp0 hpfin
  exact ⟨q, hq, hqfin⟩

end Closed

end NonUnitalStarSubalgebra


namespace ClosedStarIdeal


/-- A subprojection of an ideal projection belongs to the ideal. -/
theorem mem_of_starProjection_le (I : ClosedStarIdeal A) {p q : A}
    (hp : p ∈ I.toNonUnitalStarSubalgebra)
    (hpProj : IsStarProjection p) (hqProj : IsStarProjection q) (hqp : q ≤ p) :
    q ∈ I.toNonUnitalStarSubalgebra := by
  have hmul : p * q = q := (hqProj.le_iff_mul_eq_right hpProj).1 hqp
  rw [← hmul]
  exact I.mul_mem_right q hp

/-- Every nonzero closed C-star ideal in a faithfully compactly represented
algebra contains a projection which is minimal in the ambient algebra. -/
theorem exists_isMinimalStarProjection_mem
    (I : ClosedStarIdeal A)
    (pi : NonUnitalCStarRepresentation A H)
    (hpi : pi.IsCompactlyRepresented)
    (hI0 : ∃ x : I.toNonUnitalStarSubalgebra, x ≠ 0) :
    ∃ p : A, p ∈ I.toNonUnitalStarSubalgebra ∧
      IsMinimalStarProjection p ∧
      FiniteDimensional ℂ (LinearMap.range (pi p).toLinearMap) := by
  letI : PartialOrder I.toNonUnitalStarSubalgebra :=
    _root_.CStarAlgebra.spectralOrder I.toNonUnitalStarSubalgebra
  letI : StarOrderedRing I.toNonUnitalStarSubalgebra :=
    _root_.CStarAlgebra.spectralOrderedRing I.toNonUnitalStarSubalgebra
  obtain ⟨p, hpmin, hpfin⟩ :=
    MathlibAnnex.Analysis.CStarAlgebra.NonUnitalStarSubalgebra.exists_isMinimalStarProjection
      I.toNonUnitalStarSubalgebra I.isClosed_carrier pi hpi hI0
  have hpAmbient : IsStarProjection (p : A) :=
    hpmin.isStarProjection.map (NonUnitalStarSubalgebraClass.subtype _)
  refine ⟨p.1, p.2, ?_, ?_⟩
  · refine ⟨hpAmbient, ?_, ?_⟩
    · intro hp0
      exact hpmin.ne_zero (Subtype.ext hp0)
    · intro q hq hq0 hqp
      have hqI : q ∈ I.toNonUnitalStarSubalgebra :=
        I.mem_of_starProjection_le p.2 hpAmbient hq hqp
      let qI : I.toNonUnitalStarSubalgebra := ⟨q, hqI⟩
      have hqIProj : IsStarProjection qI := by
        constructor
        · apply Subtype.ext
          exact hq.isIdempotentElem.eq
        · apply Subtype.ext
          exact hq.isSelfAdjoint
      have hqI0 : qI ≠ 0 := by
        intro h
        exact hq0 (congrArg Subtype.val h)
      have hpq : (p : A) * q = q :=
        (hq.le_iff_mul_eq_right hpAmbient).1 hqp
      have hpqI : p * qI = qI := by
        apply Subtype.ext
        exact hpq
      have hqIp : @LE.le I.toNonUnitalStarSubalgebra
          (_root_.CStarAlgebra.spectralOrder I.toNonUnitalStarSubalgebra).toLE qI p :=
        (hqIProj.le_iff_mul_eq_right hpmin.isStarProjection).2 hpqI
      exact congrArg Subtype.val (hpmin.eq_of_le hqIProj hqI0 hqIp)
  · have hmap :
        MathlibAnnex.Analysis.CStarAlgebra.NonUnitalStarSubalgebra.restrictedRepresentation
          I.toNonUnitalStarSubalgebra pi p = pi p.1 := rfl
    rw [hmap] at hpfin
    exact hpfin

end ClosedStarIdeal

end MathlibAnnex.Analysis.CStarAlgebra
