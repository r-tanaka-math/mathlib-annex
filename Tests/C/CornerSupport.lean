import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.Corner
import MathlibAnnex.Analysis.VonNeumannAlgebra.PolarDecomposition

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open VonNeumannAlgebra
open scoped CStarAlgebra

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Closedness supplies completeness through Mathlib's existing
nonunital star-subalgebra instance. -/
example (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra)
    (hp : IsStarProjection p) : NonUnitalCStarAlgebra (corner M p hp) := inferInstance

/-- The actual corner identity has underlying value p, and acts on both
sides within the corner subtype. -/
example (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra)
    (hp : IsStarProjection p) :
    ∃ e : corner M p hp, (e : M.toStarSubalgebra) = p ∧
      ∀ x : corner M p hp, e * x = x ∧ x * e = x := by
  exact ⟨cornerUnit M p hp, rfl,
    fun x ↦ ⟨cornerUnit_mul M p hp x, mul_cornerUnit M p hp x⟩⟩

/-- A witness can be reflected into this particular corner because both
endpoint projections lie in it. The result carries the corner subtype. -/
example (M : VonNeumannAlgebra H) (e : M.toStarSubalgebra)
    (he : IsStarProjection e) (p q : corner M e he)
    (h : MurrayVonNeumannEquivalent (p : M.toStarSubalgebra) (q : M.toStarSubalgebra)) :
    ∃ v : corner M e he, v * star v * v = v ∧
      star v * v = p ∧ v * star v = q := by
  exact ((murrayVonNeumannEquivalent_corner_iff M e he p q).2 h).2.2

/-- The same distinction applies to a subequivalence witness. -/
example (M : VonNeumannAlgebra H) (e : M.toStarSubalgebra)
    (he : IsStarProjection e) (p q : corner M e he)
    (h : MurrayVonNeumannSubequivalent
      (p : M.toStarSubalgebra) (q : M.toStarSubalgebra)) :
    ∃ r : corner M e he, MurrayVonNeumannEquivalent p r ∧ r * q = r := by
  exact ((murrayVonNeumannSubequivalent_corner_iff M e he p q).2 h).2

/-- Two-sided support bounds for a nonzero element give nonzero equivalent
subprojections in the prescribed containing algebra. This is the polar
consumer needed for compression arguments. -/
example (M : VonNeumannAlgebra H) (x q r : M.toStarSubalgebra)
    (hq : IsStarProjection q) (hr : IsStarProjection r)
    (hx : x ≠ 0) (hleft : r * x = x) (hright : x * q = x) :
    ∃ p s : M.toStarSubalgebra,
      IsStarProjection p ∧ IsStarProjection s ∧ p ≤ q ∧ s ≤ r ∧
      p ≠ 0 ∧ s ≠ 0 ∧ MurrayVonNeumannEquivalent p s := by
  refine ⟨rightSupport M x, leftSupport M x,
    isStarProjection_rightSupport M x, isStarProjection_leftSupport M x,
    (rightSupport_le_iff M x hq).2 hright,
    (leftSupport_le_iff M x hr).2 hleft, ?_, ?_,
    murrayVonNeumannEquivalent_supports M x⟩
  · exact fun h ↦ hx ((rightSupport_eq_zero_iff M x).1 h)
  · exact fun h ↦ hx ((leftSupport_eq_zero_iff M x).1 h)

/-- The factorization and both support identities use a single witness
whose type is M itself. -/
example (M : VonNeumannAlgebra H) (x : M.toStarSubalgebra) :
    ∃ v : M.toStarSubalgebra,
      v * star v * v = v ∧ v * CFC.abs x = x ∧
      star v * v = rightSupport M x ∧ v * star v = leftSupport M x := by
  exact exists_polar_decomposition M x

/-- Equivalent projections transport their actual corner identities. -/
example (M : VonNeumannAlgebra H) {p q : M.toStarSubalgebra}
    (h : MurrayVonNeumannEquivalent p q) :
    ∃ f : corner M p h.1 ≃⋆ₐ[ℂ] corner M q h.2.1,
      f (cornerUnit M p h.1) = cornerUnit M q h.2.1 := by
  obtain ⟨v, hv, hi, hf⟩ := h.2.2
  exact ⟨cornerEquiv M h.1 h.2.1 v hv hi hf,
    cornerEquiv_unit M h.1 h.2.1 v hv hi hf⟩
