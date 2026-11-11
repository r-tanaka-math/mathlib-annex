/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Tactic.NoncommRing
import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.Support

/-!
# Quantitative spectral cutoffs in a concrete von Neumann algebra

The cutoff is the existing left support of `(h - ε • 1)⁺`.  Its positive
lower bound is proved from the orthogonality of positive and negative parts,
not inferred from support alone.  Completing the corner by `1 - p` gives an
actual invertible element of the original algebra and a concrete inverse
identity.  All operators remain in the specified von Neumann algebra.

The support carrier and kernel theorem are reused from `Projection.Support`.
The positive-part decomposition, norm/order comparison and strict-positivity
invertibility theorem are Mathlib APIs.  The cutoff argument implements the
quantitative step of the supplied minimal-column proof route.
-/

set_option autoImplicit false
noncomputable section

open ContinuousLinearMap
open scoped CStarAlgebra

namespace VonNeumannAlgebra

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Right support preserves the right annihilator.  This follows from the
actual represented kernel equality, with no closed-range assumption on `x`. -/
theorem rightSupport_mul_eq_zero_iff (M : VonNeumannAlgebra H)
    (x y : M.toStarSubalgebra) :
    rightSupport M x * y = 0 ↔ x * y = 0 := by
  constructor
  · intro h
    calc
      x * y = (x * rightSupport M x) * y := by rw [mul_rightSupport]
      _ = x * (rightSupport M x * y) := mul_assoc _ _ _
      _ = 0 := by rw [h, mul_zero]
  · intro h
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro ξ
    change (rightSupport M x : H →L[ℂ] H) ((y : H →L[ℂ] H) ξ) = 0
    have hker : (y : H →L[ℂ] H) ξ ∈ (x : H →L[ℂ] H).ker := by
      change (x : H →L[ℂ] H) ((y : H →L[ℂ] H) ξ) = 0
      exact congrArg (fun z : M.toStarSubalgebra ↦ (z : H →L[ℂ] H) ξ) h
    have hker' : (y : H →L[ℂ] H) ξ ∈
        (rightSupport M x : H →L[ℂ] H).ker := by
      rw [ker_rightSupport]
      exact hker
    exact hker'

/-- The support of the positive part kills the negative part, so multiplying
the original selfadjoint element by that support gives its positive part. -/
theorem leftSupport_posPart_mul (M : VonNeumannAlgebra H)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    leftSupport M x⁺ * x = x⁺ := by
  have hr : rightSupport M x⁺ = leftSupport M x⁺ := by
    rw [rightSupport, (CFC.posPart_nonneg x).star_eq]
  have hneg : leftSupport M x⁺ * x⁻ = 0 := by
    rw [← hr, rightSupport_mul_eq_zero_iff]
    exact CFC.posPart_mul_negPart x
  calc
    leftSupport M x⁺ * x = leftSupport M x⁺ * (x⁺ - x⁻) :=
      congrArg (fun z ↦ leftSupport M x⁺ * z) (CFC.posPart_sub_negPart x hx).symm
    _ = x⁺ := by rw [mul_sub, leftSupport_mul, hneg, sub_zero]

/-- The support of `(h - ε • 1)⁺`; for selfadjoint `h` this is its strict
positive spectral cutoff at the real level `ε`. -/
def spectralCutoff (M : VonNeumannAlgebra H) (h : M.toStarSubalgebra)
    (ε : ℝ) : M.toStarSubalgebra :=
  leftSupport M (h - ε • 1)⁺

/-- The cutoff is a star projection in the same algebra. -/
theorem isStarProjection_spectralCutoff (M : VonNeumannAlgebra H)
    (h : M.toStarSubalgebra) (ε : ℝ) :
    IsStarProjection (spectralCutoff M h ε) :=
  isStarProjection_leftSupport M _

/-- On the cutoff, `h` is exactly its scalar lower level plus the positive
part of the shifted element. -/
theorem spectralCutoff_mul (M : VonNeumannAlgebra H)
    (h : M.toStarSubalgebra) (ε : ℝ) (hh : IsSelfAdjoint h) :
    spectralCutoff M h ε * h =
      ε • spectralCutoff M h ε + (h - ε • 1)⁺ := by
  have hx : IsSelfAdjoint (h - ε • (1 : M.toStarSubalgebra)) := by
    change star (h - ε • (1 : M.toStarSubalgebra)) = _
    simp only [star_sub, hh.star_eq, star_smul, star_trivial, star_one]
  have heq := leftSupport_posPart_mul M (h - ε • 1) hx
  change spectralCutoff M h ε * (h - ε • 1) = (h - ε • 1)⁺ at heq
  rw [mul_sub, mul_smul_comm, mul_one] at heq
  simpa only [add_comm] using (sub_eq_iff_eq_add).1 heq

/-- The actual cutoff commutes with its selfadjoint source. -/
theorem commute_spectralCutoff (M : VonNeumannAlgebra H)
    (h : M.toStarSubalgebra) (ε : ℝ) (hh : IsSelfAdjoint h) :
    Commute (spectralCutoff M h ε) h := by
  have hp := isStarProjection_spectralCutoff M h ε
  have heq := spectralCutoff_mul M h ε hh
  have heq' : h * spectralCutoff M h ε =
      ε • spectralCutoff M h ε + (h - ε • 1)⁺ := by
    simpa only [star_mul, hh.star_eq, hp.isSelfAdjoint.star_eq, star_add,
      star_smul, star_trivial, (CFC.posPart_nonneg (h - ε • 1)).star_eq]
      using congrArg star heq
  exact heq.trans heq'.symm

/-- A positive operator dominates its cutoff multiplied by the cutoff level.
This is an order inequality in the actual von Neumann algebra subtype. -/
theorem smul_spectralCutoff_le (M : VonNeumannAlgebra H)
    (h : M.toStarSubalgebra) (ε : ℝ) (hh : 0 ≤ h) :
    ε • spectralCutoff M h ε ≤ h := by
  let p := spectralCutoff M h ε
  have hp : IsStarProjection p := isStarProjection_spectralCutoff M h ε
  have hc : Commute p h := commute_spectralCutoff M h ε hh.isSelfAdjoint
  have hph : p * h = ε • p + (h - ε • 1)⁺ :=
    spectralCutoff_mul M h ε hh.isSelfAdjoint
  have hphp : p * h * p = p * h := by
    rw [mul_assoc, ← hc.eq, ← mul_assoc, hp.isIdempotentElem.eq]
  have hsplit : p * h + (1 - p) * h * (1 - p) = h := by
    calc
      p * h + (1 - p) * h * (1 - p) = h - h * p + p * h * p := by
        noncomm_ring
      _ = h := by rw [hphp, hc.eq]; abel
  have hdiff : h - ε • p = (h - ε • 1)⁺ + (1 - p) * h * (1 - p) := by
    calc
      h - ε • p = (p * h + (1 - p) * h * (1 - p)) - ε • p :=
        congrArg (fun z ↦ z - ε • p) hsplit.symm
      _ = (h - ε • 1)⁺ + (1 - p) * h * (1 - p) := by rw [hph]; abel
  apply sub_nonneg.mp
  rw [hdiff]
  exact add_nonneg (CFC.posPart_nonneg _)
    (IsSelfAdjoint.conjugate_nonneg hh hp.one_sub.isSelfAdjoint)

/-- A cutoff below the norm of a nonnegative operator is nonzero.  The proof
uses norm/order comparison, not an assumed spectral projection witness. -/
theorem spectralCutoff_ne_zero (M : VonNeumannAlgebra H)
    (h : M.toStarSubalgebra) {ε : ℝ} (hε : 0 ≤ ε) (hεh : ε < ‖h‖)
    (hh : 0 ≤ h) : spectralCutoff M h ε ≠ 0 := by
  intro hp
  have hx : IsSelfAdjoint (h - ε • (1 : M.toStarSubalgebra)) := by
    change star (h - ε • (1 : M.toStarSubalgebra)) = _
    simp only [star_sub, hh.star_eq, star_smul, star_trivial, star_one]
  have hb : (h - ε • (1 : M.toStarSubalgebra))⁺ = 0 :=
    (leftSupport_eq_zero_iff M _).1 hp
  have hle : h ≤ ε • (1 : M.toStarSubalgebra) :=
    sub_nonpos.mp ((CFC.posPart_eq_zero_iff _ hx).1 hb)
  have hnorm : ‖h‖ ≤ ε := (CStarAlgebra.norm_le_iff_le_algebraMap h hε hh).2
    (by simpa only [Algebra.algebraMap_eq_smul_one] using hle)
  exact (not_le_of_gt hεh) hnorm

/-- Every nonzero positive element has a nonzero internal projection on which
it has a quantitative strictly positive lower bound.  There is no hypothesis
that the support of the original element is bounded below. -/
theorem exists_nonzero_projection_smul_le (M : VonNeumannAlgebra H)
    (h : M.toStarSubalgebra) (hh : 0 ≤ h) (hne : h ≠ 0) :
    ∃ (ε : ℝ) (p : M.toStarSubalgebra), 0 < ε ∧ IsStarProjection p ∧
      p ≠ 0 ∧ Commute p h ∧ ε • p ≤ h := by
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hne
  refine ⟨‖h‖ / 2, spectralCutoff M h (‖h‖ / 2), half_pos hn,
    isStarProjection_spectralCutoff M h _, ?_,
    commute_spectralCutoff M h _ hh.isSelfAdjoint, smul_spectralCutoff_le M h _ hh⟩
  exact spectralCutoff_ne_zero M h (half_pos hn).le (half_lt_self hn) hh

/-- Completing a quantitatively positive corner by the complementary
projection gives an invertible element of the same unital algebra. -/
theorem isUnit_sandwich_add_one_sub (M : VonNeumannAlgebra H)
    {p h : M.toStarSubalgebra} (hp : IsStarProjection p)
    {ε : ℝ} (hε : 0 < ε) (hle : ε • p ≤ h) :
    IsUnit (p * h * p + (1 - p)) := by
  have hcompressed : ε • p ≤ p * h * p := by
    simpa only [hp.isSelfAdjoint.star_eq, mul_smul_comm, smul_mul_assoc,
      hp.isIdempotentElem.eq] using star_left_conjugate_le_conjugate hle p
  have hfirst : min ε 1 • p ≤ p * h * p :=
    (smul_le_smul_of_nonneg_right (min_le_left ε 1) hp.nonneg).trans hcompressed
  have hsecond : min ε 1 • (1 - p) ≤ 1 - p := by
    simpa only [one_smul] using
      smul_le_smul_of_nonneg_right (min_le_right ε 1) hp.one_sub.nonneg
  have hbound : algebraMap ℝ M.toStarSubalgebra (min ε 1) ≤
      p * h * p + (1 - p) := by
    have hpcomp : p + (1 - p) = 1 := by abel
    simpa only [← smul_add, hpcomp, Algebra.algebraMap_eq_smul_one]
      using add_le_add hfirst hsecond
  exact CStarAlgebra.isUnit_of_le _ hbound
    (isStrictlyPositive_algebraMap (lt_min hε zero_lt_one))

/-- The ambient inverse of the completed corner acts as the inverse of `h`
on the actual corner.  The inverse and all products are internal to `M`. -/
theorem ringInverse_sandwich_add_one_sub_mul (M : VonNeumannAlgebra H)
    {p h : M.toStarSubalgebra} (hp : IsStarProjection p)
    (hu : IsUnit (p * h * p + (1 - p))) :
    Ring.inverse (p * h * p + (1 - p)) * p * h * p = p := by
  have hcp : (p * h * p + (1 - p)) * p = p * h * p := by
    simp only [add_mul, sub_mul, one_mul, mul_assoc,
      hp.isIdempotentElem.eq, sub_self, add_zero]
  calc
    Ring.inverse (p * h * p + (1 - p)) * p * h * p =
        Ring.inverse (p * h * p + (1 - p)) * (p * h * p) := by
      simp only [mul_assoc]
    _ = Ring.inverse (p * h * p + (1 - p)) *
        ((p * h * p + (1 - p)) * p) := by rw [hcp]
    _ = p := Ring.inverse_mul_cancel_left _ _ hu

/-- The same inverse formula solves left multiplication by `h` on every
element of the actual corner, using only its left absorption equation. -/
theorem ringInverse_sandwich_add_one_sub_mul_of_mul_eq_right
    (M : VonNeumannAlgebra H) {p h a : M.toStarSubalgebra}
    (hp : IsStarProjection p) (hu : IsUnit (p * h * p + (1 - p)))
    (hpa : p * a = a) :
    Ring.inverse (p * h * p + (1 - p)) * p * h * a = a := by
  calc
    Ring.inverse (p * h * p + (1 - p)) * p * h * a =
        Ring.inverse (p * h * p + (1 - p)) * p * h * (p * a) := by rw [hpa]
    _ = (Ring.inverse (p * h * p + (1 - p)) * p * h * p) * a := by
      simp only [mul_assoc]
    _ = a := by rw [ringInverse_sandwich_add_one_sub_mul M hp hu, hpa]

end VonNeumannAlgebra
