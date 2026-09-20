import MathlibAnnex.Analysis.Normed.Sphere.RadialExtension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Tactic

/-!
# Finite-dimensional consequences of a unit-sphere isometry

A bijective isometry between the unit spheres extends to a homeomorphism of the
ambient real normed spaces.  Local compactness and Riesz's theorem transfer
finite-dimensionality from either ambient space to the other.  If both spaces
are finite-dimensional, the two `finrank`s agree by the Hausdorff-dimension
comparison supplied by the forward and inverse `3`-Lipschitz radial maps.

This file uses Mathlib's root-level `dimH` directly.  It retains
`Module.finrank_pos_iff` as the designated positivity provider and therefore
introduces neither a Hausdorff-dimension compatibility alias nor a wrapper
theorem for positivity of `finrank`.
-/

noncomputable section

open Set Function
open scoped ENNReal

namespace MathlibAnnex
namespace Sphere

universe u v

variable {X : Type u} {Y : Type v}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- If the domain ambient space is finite-dimensional, then the codomain
ambient space is finite-dimensional. -/
theorem finiteDimensional_codomain
    [FiniteDimensional ℝ X]
    (e : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1) :
    FiniteDimensional ℝ Y := by
  let h : X ≃ₜ Y := radialExtensionHomeomorph e
  letI : ProperSpace X := FiniteDimensional.proper_real X
  letI : LocallyCompactSpace Y :=
    h.locallyCompactSpace_iff.mp (inferInstance : LocallyCompactSpace X)
  exact FiniteDimensional.of_locallyCompactSpace ℝ

/-- If the codomain ambient space is finite-dimensional, then the domain
ambient space is finite-dimensional. -/
theorem finiteDimensional_domain
    [FiniteDimensional ℝ Y]
    (e : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1) :
    FiniteDimensional ℝ X :=
  finiteDimensional_codomain e.symm

private theorem dimH_univ_le
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (e : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1) :
    _root_.dimH (Set.univ : Set Y) ≤ _root_.dimH (Set.univ : Set X) := by
  have h := (lipschitzWith_radialExtension e).dimH_range_le
  rw [Set.range_eq_univ.mpr (radialExtension_surjective e)] at h
  exact h

private theorem dimH_univ_ge
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (e : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1) :
    _root_.dimH (Set.univ : Set X) ≤ _root_.dimH (Set.univ : Set Y) :=
  dimH_univ_le e.symm

private theorem dimH_univ_eq
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (e : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1) :
    _root_.dimH (Set.univ : Set X) = _root_.dimH (Set.univ : Set Y) :=
  le_antisymm (dimH_univ_ge e) (dimH_univ_le e)

/-- A bijective isometry between unit spheres of finite-dimensional real normed
spaces forces equality of the ambient real dimensions. -/
theorem finrank_eq
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (e : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1) :
    Module.finrank ℝ X = Module.finrank ℝ Y := by
  have h := dimH_univ_eq e
  rw [Real.dimH_univ_eq_finrank X, Real.dimH_univ_eq_finrank Y] at h
  exact_mod_cast h

end Sphere
end MathlibAnnex
