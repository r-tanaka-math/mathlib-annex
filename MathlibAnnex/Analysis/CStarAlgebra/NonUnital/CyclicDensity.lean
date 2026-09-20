import Mathlib.Tactic.FunProp
import MathlibAnnex.Topology.MetricSpace.DenseCardinality
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.CompactRange

/-!
# Dense orbits for nonunital irreducible representations

To avoid an approximate-identity development, begin with a nonzero vector
`pi a x`.  Its unitization orbit is dense, and each point of that orbit is
already in the original algebra's orbit of `x`.
-/

set_option autoImplicit false

open Set Metric
open scoped Cardinal CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace NonUnitalCStarRepresentation

/-- A nonzero represented value gives a vector whose original-algebra orbit
is dense.  The source need not have a unit. -/
theorem denseRange_apply_of_isIrreducible_of_apply_ne_zero
    (pi : NonUnitalCStarRepresentation A H) (hirr : pi.IsIrreducible)
    {a : A} {x : H} (hax : pi a x ≠ 0) :
    DenseRange (fun b : A => pi b x) := by
  have horbit : DenseRange (fun z : Unitization ℂ A => pi.unitization z (pi a x)) :=
    Representation.denseRange_orbitMap_of_isIrreducible pi.unitization
      (isIrreducible_unitization pi hirr) hax
  rw [Metric.denseRange_iff] at horbit ⊢
  intro y ε hε
  obtain ⟨z, hz⟩ := horbit y ε hε
  induction z using Unitization.ind with
  | inl_add_inr c b =>
      refine ⟨c • a + b * a, ?_⟩
      simpa [unitization, map_add, map_smul, map_mul, mul_apply_eq_comp] using hz

/-- Every nonzero irreducible representation has a dense orbit of the
original nonunital algebra. -/
theorem exists_denseRange_apply_of_isIrreducible
    (pi : NonUnitalCStarRepresentation A H) (hirr : pi.IsIrreducible) :
    ∃ x : H, DenseRange (fun a : A => pi a x) := by
  obtain ⟨a, ha⟩ := hirr.1
  obtain ⟨x, hx⟩ : ∃ x : H, pi a x ≠ 0 := by
    by_contra h
    apply ha
    ext x
    change pi a x = 0
    by_contra hx
    exact h ⟨x, hx⟩
  exact ⟨x, denseRange_apply_of_isIrreducible_of_apply_ne_zero pi hirr hx⟩

/-- A continuous orbit map transports a small dense subset of the algebra
to a small dense subset of the irreducible representation space. -/
theorem exists_dense_cardinalMk_lt_continuum_of_isIrreducible
    (pi : NonUnitalCStarRepresentation A H) (hirr : pi.IsIrreducible)
    (s : Set A) (hs : Dense s) (hcard : #s < Cardinal.continuum) :
    ∃ t : Set H, Dense t ∧ #t < Cardinal.continuum := by
  obtain ⟨x, hx⟩ := exists_denseRange_apply_of_isIrreducible pi hirr
  have hcont : Continuous (fun a : A => pi a x) :=
    (ContinuousLinearMap.apply ℂ H x).continuous.comp (map_continuous pi)
  exact MathlibAnnex.Topology.exists_dense_cardinalMk_lt_continuum_of_continuous_denseRange
    (fun a : A => pi a x) hcont hx s hs hcard

end NonUnitalCStarRepresentation
end MathlibAnnex.Analysis.CStarAlgebra
