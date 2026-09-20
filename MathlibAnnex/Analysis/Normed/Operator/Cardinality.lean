import Mathlib.Analysis.InnerProductSpace.Adjoint
import MathlibAnnex.Topology.MetricSpace.SeparableCardinality

/-!
# Cardinality of operators on a separable normed space

An operator is determined by its values on a countable dense sequence.
This is a cardinality argument, not norm separability of the operator algebra.
-/
set_option autoImplicit false
open Function Set TopologicalSpace
open scoped Cardinal
namespace MathlibAnnex
universe u

/-- Endomorphisms of a separable complex normed space form a set of cardinality
at most the continuum. Completeness and finite dimensionality are not needed. -/
theorem cardinalMk_continuousLinearMap_le_continuum
    (H : Type u) [NormedAddCommGroup H] [NormedSpace ℂ H] [SeparableSpace H] :
    #(H →L[ℂ] H) ≤ Cardinal.continuum := by
  let f : (H →L[ℂ] H) → ℕ → H := fun T n => T (denseSeq H n)
  have hf : Injective f := by
    intro T S h
    apply ContinuousLinearMap.ext
    intro x
    exact (denseRange_denseSeq H).induction_on x
      (isClosed_eq T.continuous S.continuous) (fun n => congrFun h n)
  apply Topology.cardinalMk_le_continuum_of_injective f hf
  have hH := Topology.cardinalMk_le_continuum_of_separableSpace H
  have hpow : (#H) ^ Cardinal.aleph0 ≤ Cardinal.continuum ^ Cardinal.aleph0 :=
    Cardinal.power_le_power_right hH
  simpa [Cardinal.mk_arrow] using hpow

end MathlibAnnex
