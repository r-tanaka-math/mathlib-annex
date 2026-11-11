/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.CentralSupport
import MathlibAnnex.Analysis.VonNeumannAlgebra.PolarDecomposition

/-!
# Central overlap and equivalent subprojections

Nonorthogonal central supports produce a nonzero algebraic corner overlap.
Polar decomposition of that overlap gives nonzero equivalent subprojections
inside the specified algebra. These are local comparison results; no global
comparison theorem or maximal family is assumed in a definition.
-/

set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra

namespace VonNeumannAlgebra

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Central supports are orthogonal exactly when the algebraic corner
between the two elements vanishes. Both elements may be arbitrary. -/
theorem centralSupport_mul_eq_zero_iff (M : VonNeumannAlgebra H)
    (p q : M.toStarSubalgebra) :
    centralSupport M p * centralSupport M q = 0 ↔
      ∀ a : M.toStarSubalgebra, p * a * q = 0 := by
  constructor
  · intro h
    have hpc : p * centralSupport M q = 0 := by
      calc
        p * centralSupport M q = (p * centralSupport M p) * centralSupport M q := by
          rw [self_mul_centralSupport]
        _ = p * (centralSupport M p * centralSupport M q) := mul_assoc _ _ _
        _ = 0 := by rw [h, mul_zero]
    intro a
    exact (mul_centralHull_eq_zero_iff M {q} p).mp hpc q (Set.mem_singleton q) a
  · intro h
    have hpc : p * centralSupport M q = 0 := by
      apply (mul_centralHull_eq_zero_iff M {q} p).mpr
      intro q' hq' a
      have hq'q : q' = q := Set.mem_singleton_iff.mp hq'
      simpa only [hq'q] using h a
    have hcp : centralSupport M q * p = 0 :=
      (centralSupport_commute M q p).symm.trans hpc
    have hcentral (a : M.toStarSubalgebra) :
        a * (1 - centralSupport M q) = (1 - centralSupport M q) * a := by
      rw [mul_sub, sub_mul, mul_one, one_mul, centralSupport_commute M q a]
    have hfix : (1 - centralSupport M q) * p = p := by
      rw [sub_mul, one_mul, hcp, sub_zero]
    have hle := centralSupport_le M (isStarProjection_centralSupport M q).one_sub
      hcentral hfix
    have heq : centralSupport M p - centralSupport M p * centralSupport M q =
        centralSupport M p := by simpa only [mul_sub, mul_one] using hle
    simpa only [sub_eq_self] using heq

/-- A nonzero overlap of central supports supplies nonzero equivalent
subprojections. The partial-isometry witness of their equivalence lies in
`M.toStarSubalgebra`, not merely in the ambient operator algebra. -/
theorem exists_nonzero_equivalent_subprojections_of_centralSupport_mul_ne_zero
    (M : VonNeumannAlgebra H) {p q : M.toStarSubalgebra}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hcentral : centralSupport M p * centralSupport M q ≠ 0) :
    ∃ p' q' : M.toStarSubalgebra,
      MurrayVonNeumannEquivalent p' q' ∧ p' ≠ 0 ∧ q' ≠ 0 ∧ p' ≤ p ∧ q' ≤ q := by
  classical
  have hoverlap : ¬ ∀ a : M.toStarSubalgebra, p * a * q = 0 := by
    intro h
    exact hcentral ((centralSupport_mul_eq_zero_iff M p q).mpr h)
  obtain ⟨a, ha⟩ := not_forall.mp hoverlap
  let x : M.toStarSubalgebra := p * a * q
  have hx0 : x ≠ 0 := ha
  have hpx : p * x = x := by
    change p * (p * a * q) = p * a * q
    calc
      p * (p * a * q) = (p * p) * a * q := by simp only [mul_assoc]
      _ = p * a * q := by rw [hp.isIdempotentElem.eq]
  have hxq : x * q = x := by
    change (p * a * q) * q = p * a * q
    rw [mul_assoc, hq.isIdempotentElem.eq]
  refine ⟨leftSupport M x, rightSupport M x,
    (murrayVonNeumannEquivalent_supports M x).symm, ?_, ?_,
    (leftSupport_le_iff M x hp).mpr hpx, (rightSupport_le_iff M x hq).mpr hxq⟩
  · intro h
    exact hx0 ((leftSupport_eq_zero_iff M x).mp h)
  · intro h
    exact hx0 ((rightSupport_eq_zero_iff M x).mp h)

/-- If two projections have no nonzero equivalent subprojections,
their central supports are orthogonal. -/
theorem centralSupport_mul_eq_zero_of_no_nonzero_equivalent_subprojections
    (M : VonNeumannAlgebra H) {p q : M.toStarSubalgebra}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hdisjoint : ∀ p' q' : M.toStarSubalgebra,
      MurrayVonNeumannEquivalent p' q' → p' ≤ p → q' ≤ q → p' = 0) :
    centralSupport M p * centralSupport M q = 0 := by
  by_contra h
  obtain ⟨p', q', heq, hp'0, _, hp'p, hq'q⟩ :=
    exists_nonzero_equivalent_subprojections_of_centralSupport_mul_ne_zero M hp hq h
  exact hp'0 (hdisjoint p' q' heq hp'p hq'q)

end VonNeumannAlgebra
