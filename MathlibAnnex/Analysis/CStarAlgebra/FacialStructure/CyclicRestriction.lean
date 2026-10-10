/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.MatrixCoefficient
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Cyclic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Tactic

/-!
# Restriction to the closed orbit of the original nonunital algebra

The cyclic subspace is the norm closure of `pi(A) x`, not the orbit of the
unitization. The source vector need not initially belong to it. The action
on its orthogonal projection has exactly the original orbit.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def orbitContinuousMap (pi : NonUnitalCStarRepresentation A H) :
    A →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := pi, map_add' := map_add pi, map_smul' := map_smul pi }
    1 (fun a => by
      change ‖pi a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le pi a)

/-- The bounded orbit map for the original algebra. -/
def orbitMap (pi : NonUnitalCStarRepresentation A H) (x : H) : A →L[ℂ] H :=
  (ContinuousLinearMap.apply ℂ H x).comp (orbitContinuousMap pi)

@[simp]
theorem orbitMap_apply (pi : NonUnitalCStarRepresentation A H) (x : H) (a : A) :
    orbitMap pi x a = pi a x := rfl

/-- Norm closure of the original-algebra orbit, with no nondegeneracy premise. -/
def cyclicSubspace (pi : NonUnitalCStarRepresentation A H) (x : H) : Submodule ℂ H :=
  (LinearMap.range (orbitMap pi x).toLinearMap).topologicalClosure

theorem isClosed_cyclicSubspace (pi : NonUnitalCStarRepresentation A H) (x : H) :
    IsClosed (cyclicSubspace pi x : Set H) :=
  (LinearMap.range (orbitMap pi x).toLinearMap).isClosed_topologicalClosure

instance instCompleteSpaceCyclicSubspace (pi : NonUnitalCStarRepresentation A H) (x : H) :
    CompleteSpace (cyclicSubspace pi x) := by
  letI : IsClosed (cyclicSubspace pi x : Set H) := isClosed_cyclicSubspace pi x
  infer_instance

theorem apply_mem_cyclicSubspace (pi : NonUnitalCStarRepresentation A H) (x : H) (a : A) :
    pi a x ∈ cyclicSubspace pi x :=
  (LinearMap.range (orbitMap pi x).toLinearMap).le_topologicalClosure
    (LinearMap.mem_range_self (orbitMap pi x).toLinearMap a)

/-- Closure of the original orbit is reducing, also for a degenerate representation. -/
theorem reduces_cyclicSubspace (pi : NonUnitalCStarRepresentation A H) (x : H) :
    pi.Reduces (cyclicSubspace pi x) := by
  have hinv (a : A) (y : H) (hy : y ∈ cyclicSubspace pi x) :
      pi a y ∈ cyclicSubspace pi x := by
    change y ∈ closure (LinearMap.range (orbitMap pi x).toLinearMap) at hy
    change pi a y ∈ closure (LinearMap.range (orbitMap pi x).toLinearMap)
    apply (show Set.MapsTo (pi a) (LinearMap.range (orbitMap pi x).toLinearMap)
        (LinearMap.range (orbitMap pi x).toLinearMap) from ?_).closure (pi a).continuous hy
    rintro _ ⟨b, rfl⟩
    refine ⟨a * b, ?_⟩
    change pi (a * b) x = pi a (pi b x)
    exact congrArg (fun T : H →L[ℂ] H => T x) (map_mul pi a b)
  refine ⟨isClosed_cyclicSubspace pi x, fun a y hy => ⟨hinv a y hy, ?_⟩⟩
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  exact hinv (star a) y hy

/-- Genuine restriction of a star representation to a closed reducing subspace. -/
def reducingRestriction (pi : NonUnitalCStarRepresentation A H)
    (M : Submodule ℂ H) [CompleteSpace M] (hM : pi.Reduces M) :
    NonUnitalCStarRepresentation A M where
  toFun a := (pi a).restrict (fun z hz => (hM.2 a z hz).1)
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro z
    apply Subtype.ext
    change pi 0 (z : H) = 0
    simp
  map_add' a b := by
    apply ContinuousLinearMap.ext
    intro z
    apply Subtype.ext
    change pi (a + b) (z : H) = pi a z + pi b z
    simp
  map_mul' a b := by
    apply ContinuousLinearMap.ext
    intro z
    apply Subtype.ext
    change pi (a * b) (z : H) = pi a (pi b z)
    rw [map_mul]
    rfl
  map_smul' c a := by
    apply ContinuousLinearMap.ext
    intro z
    apply Subtype.ext
    change pi (c • a) (z : H) = c • pi a z
    rw [map_smul]
    rfl
  map_star' a := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    apply ContinuousLinearMap.ext
    intro z
    apply ext_inner_right ℂ
    intro w
    rw [ContinuousLinearMap.adjoint_inner_left]
    change inner ℂ (pi (star a) (z : H)) (w : H) = inner ℂ (z : H) (pi a (w : H))
    rw [map_star, ContinuousLinearMap.star_eq_adjoint]
    exact ContinuousLinearMap.adjoint_inner_left (pi a) (w : H) (z : H)

@[simp]
theorem reducingRestriction_apply (pi : NonUnitalCStarRepresentation A H)
    (M : Submodule ℂ H) [CompleteSpace M] (hM : pi.Reduces M) (a : A) (z : M) :
    (reducingRestriction pi M hM a z : H) = pi a z := rfl

/-- The actual representation on the closure of the original orbit. -/
def cyclicRestriction (pi : NonUnitalCStarRepresentation A H) (x : H) :
    NonUnitalCStarRepresentation A (cyclicSubspace pi x) :=
  reducingRestriction pi (cyclicSubspace pi x) (reduces_cyclicSubspace pi x)

/-- Compressing the source vector leaves every original-algebra orbit value unchanged. -/
theorem apply_starProjection_cyclicSubspace (pi : NonUnitalCStarRepresentation A H)
    (x : H) (a : A) :
    pi a ((cyclicSubspace pi x).starProjection x) = pi a x := by
  let M := cyclicSubspace pi x
  have hcomm := Representation.starProjection_commutes_of_reduces pi.unitization M
    (reduces_unitization_of_reduces pi M (reduces_cyclicSubspace pi x)) (Unitization.inr a)
  have h := congrArg (fun T : H →L[ℂ] H => T x) hcomm
  have hfix : M.starProjection (pi a x) = pi a x :=
    M.starProjection_eq_self_iff.mpr (apply_mem_cyclicSubspace pi x a)
  have hcomm' : M.starProjection (pi a x) = pi a (M.starProjection x) := by
    simpa only [unitization_inr, ContinuousLinearMap.mul_apply] using h
  exact hcomm'.symm.trans hfix

/-- The projected source is cyclic for the original algebra in the restricted space. -/
theorem denseRange_cyclicRestriction (pi : NonUnitalCStarRepresentation A H) (x : H) :
    DenseRange (fun a : A => cyclicRestriction pi x a
      ((cyclicSubspace pi x).orthogonalProjectionOnto x)) := by
  apply Metric.denseRange_iff.mpr
  intro z epsilon hepsilon
  have hz : (z : H) ∈ closure (Set.range (orbitMap pi x)) := z.property
  obtain ⟨v, hv, hdist⟩ := Metric.mem_closure_iff.mp hz epsilon hepsilon
  obtain ⟨a, rfl⟩ := hv
  refine ⟨a, ?_⟩
  have hval : (cyclicRestriction pi x a
      ((cyclicSubspace pi x).orthogonalProjectionOnto x) : H) = pi a x :=
    apply_starProjection_cyclicSubspace pi x a
  change dist (z : H) (cyclicRestriction pi x a
    ((cyclicSubspace pi x).orthogonalProjectionOnto x) : H) < epsilon
  rw [hval]
  simpa only [orbitMap_apply, dist_comm] using hdist

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
