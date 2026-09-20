import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import MathlibAnnex.Analysis.CStarAlgebra.Cyclic
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Cyclic
import MathlibAnnex.Analysis.CStarAlgebra.Representation.VectorFunctional

/-!
# Restricting a representation to a cyclic reducing subspace

The construction stays in an arbitrary Hilbert-space universe.  Closedness is
used only to install completeness on the subtype; no finite-dimensional or
separability hypothesis is introduced.
-/

set_option autoImplicit false

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Representation

/-- Restriction of a star representation to a complete reducing subspace. -/
noncomputable def restrictToReducing (pi : Representation A H)
    (M : Submodule ℂ H) [CompleteSpace M] (hM : pi.Reduces M) :
    Representation A M where
  toFun a := (pi a).restrict (fun x hx ↦ (hM.2 a x hx).1)
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    ext
    simp
  map_mul' a b := by
    apply ContinuousLinearMap.ext
    intro x
    ext
    simp
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro x
    ext
    simp
  map_add' a b := by
    apply ContinuousLinearMap.ext
    intro x
    ext
    simp
  commutes' c := by
    apply ContinuousLinearMap.ext
    intro x
    ext
    change pi (algebraMap ℂ A c) x = c • (x : H)
    rw [← ContinuousLinearMap.algebraMap_apply (R := ℂ) (S := ℂ)
      (M := H)]
    exact congrArg (fun T : H →L[ℂ] H ↦ T (x : H)) ((pi).commutes c)
  map_star' a := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
    intro x y
    change inner ℂ (pi (star a) (x : H)) (y : H) =
      inner ℂ (x : H) (pi a (y : H))
    rw [map_star, ContinuousLinearMap.star_eq_adjoint]
    exact ContinuousLinearMap.adjoint_inner_left (pi a) (y : H) (x : H)

@[simp]
theorem restrictToReducing_apply_coe (pi : Representation A H)
    (M : Submodule ℂ H) [CompleteSpace M] (hM : pi.Reduces M)
    (a : A) (x : M) :
    ((restrictToReducing pi M hM a x : M) : H) = pi a (x : H) :=
  rfl

/-- Restriction does not change a vector coefficient. -/
theorem vectorFunctional_restrictToReducing (pi : Representation A H)
    (M : Submodule ℂ H) [CompleteSpace M] (hM : pi.Reduces M) (x : M) :
    vectorFunctional (restrictToReducing pi M hM) x =
      vectorFunctional pi (x : H) := by
  apply ContinuousLinearMap.ext
  intro a
  rfl

/-- The orbit of the generating vector is dense in its cyclic-subspace
restriction. -/
theorem denseRange_orbitMap_restrictCyclic (pi : Representation A H) (eta : H) :
    let M := cyclicSubspace pi eta
    letI : CompleteSpace M := (isClosed_cyclicSubspace pi eta).completeSpace_coe
    DenseRange (StarAlgHom.orbitMap
      (restrictToReducing pi M (reduces_cyclicSubspace pi eta))
      (⟨eta, self_mem_cyclicSubspace pi eta⟩ : M)) := by
  dsimp only
  rw [Metric.denseRange_iff]
  intro x eps heps
  have hx : (x : H) ∈ closure (Set.range (orbitLinearMap pi eta)) := by
    have hx' := x.property
    change (x : H) ∈ (cyclicSubspace pi eta : Set H) at hx'
    simpa only [Representation.cyclicSubspace,
      Submodule.topologicalClosure_coe, LinearMap.coe_range] using hx'
  obtain ⟨a, ha⟩ := Metric.mem_closure_range_iff.mp hx eps heps
  refine ⟨a, ?_⟩
  change dist (x : H) (pi a eta) < eps
  simpa [orbitLinearMap, StarAlgHom.orbitMap] using ha

end Representation

end MathlibAnnex.Analysis.CStarAlgebra
