import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.Normed.Module.Normalize
import MathlibAnnex.Analysis.CStarAlgebra.CyclicTransport
import MathlibAnnex.Analysis.CStarAlgebra.GNS.Adapters
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Adapters
import MathlibAnnex.Analysis.CStarAlgebra.Representation.VectorFunctional

/-!
# States and their cyclic GNS representations

This file gives neutral mathematical names to normalized positive continuous
functionals and records the elementary bridges to Mathlib's GNS construction.
It is independent of the legacy project namespace.
-/

set_option autoImplicit false

open Set
open scoped ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Normalized positive continuous complex-linear functionals. -/
def stateSpace (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    Set (A →L[ℂ] ℂ) :=
  {phi | (∀ a : A, 0 ≤ a → 0 ≤ phi a) ∧ phi 1 = 1}

/-- A pure state is an extreme point of the ordinary state space. -/
def IsPureState (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (phi : A →L[ℂ] ℂ) : Prop :=
  phi ∈ (stateSpace A).extremePoints ℝ

/-- Rebundle a state as the positive linear map used by the GNS construction. -/
def positiveLinearMapOfMemStateSpace
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A) : A →ₚ[ℂ] ℂ where
  toLinearMap := phi.toLinearMap
  monotone' := by
    intro a b hab
    apply sub_nonneg.mp
    change 0 ≤ phi b - phi a
    rw [← map_sub]
    exact hphi.1 (b - a) (sub_nonneg.mpr hab)

@[simp]
theorem positiveLinearMapOfMemStateSpace_apply
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A) (a : A) :
    positiveLinearMapOfMemStateSpace phi hphi a = phi a :=
  rfl

@[simp]
theorem positiveLinearMapOfMemStateSpace_one
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A) :
    positiveLinearMapOfMemStateSpace phi hphi 1 = 1 :=
  hphi.2

/-- The canonical vector of the GNS representation of a state. -/
noncomputable def stateGNSVector (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A) :
    (positiveLinearMapOfMemStateSpace phi hphi).GNS :=
  _root_.PositiveLinearMap.gnsCyclicVector (positiveLinearMapOfMemStateSpace phi hphi)

theorem norm_stateGNSVector (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A) :
    ‖stateGNSVector phi hphi‖ = 1 :=
  _root_.PositiveLinearMap.norm_gnsCyclicVector _
    (positiveLinearMapOfMemStateSpace_one phi hphi)

theorem inner_gnsStarAlgHom_stateGNSVector
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A) (a : A) :
    inner ℂ (stateGNSVector phi hphi)
      ((positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom a
        (stateGNSVector phi hphi)) = phi a := by
  exact _root_.PositiveLinearMap.inner_gnsCyclicVector_gnsStarAlgHom _ a

theorem denseRange_gnsStarAlgHom_stateGNSVector
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A) :
    DenseRange (fun a : A ↦
      (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom a
        (stateGNSVector phi hphi)) :=
  _root_.PositiveLinearMap.denseRange_gnsStarAlgHom_apply_gnsCyclicVector _

/-- A unit vector in a unital star representation defines a state. -/
theorem vectorFunctional_mem_stateSpace
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H) (hxi : ‖xi‖ = 1) :
    Representation.vectorFunctional pi xi ∈ stateSpace A := by
  refine ⟨?_, Representation.vectorFunctional_one pi hxi⟩
  intro a ha
  exact Representation.vectorFunctional_nonnegative pi xi ha

/-- The positive functional associated to a unit vector state. -/
noncomputable def vectorPositiveFunctional
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H) (hxi : ‖xi‖ = 1) : A →ₚ[ℂ] ℂ :=
  positiveLinearMapOfMemStateSpace (Representation.vectorFunctional pi xi)
    (vectorFunctional_mem_stateSpace pi xi hxi)

@[simp]
theorem vectorPositiveFunctional_apply
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H) (hxi : ‖xi‖ = 1) (a : A) :
    vectorPositiveFunctional pi xi hxi a = inner ℂ xi (pi a xi) :=
  rfl

/-- A unit cyclic representation is unitarily equivalent to the GNS model of
its vector state. -/
theorem vectorState_unitaryEquivalent_gns
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H) (hxi : ‖xi‖ = 1)
    (hcyclic : DenseRange (StarAlgHom.orbitMap pi xi)) :
    Representation.UnitaryEquivalent pi
      (vectorPositiveFunctional pi xi hxi).gnsStarAlgHom := by
  obtain ⟨W, hW, -⟩ := StarAlgHom.existsUnique_pointedCyclicTransport
    pi (vectorPositiveFunctional pi xi hxi).gnsStarAlgHom xi
    (_root_.PositiveLinearMap.gnsCyclicVector (vectorPositiveFunctional pi xi hxi))
    hcyclic
    (_root_.PositiveLinearMap.denseRange_gnsStarAlgHom_apply_gnsCyclicVector _)
    (fun a => by
      calc
        inner ℂ xi (pi a xi) = vectorPositiveFunctional pi xi hxi a :=
          (vectorPositiveFunctional_apply pi xi hxi a).symm
        _ = inner ℂ (_root_.PositiveLinearMap.gnsCyclicVector _)
            ((vectorPositiveFunctional pi xi hxi).gnsStarAlgHom a
              (_root_.PositiveLinearMap.gnsCyclicVector _)) :=
          (_root_.PositiveLinearMap.inner_gnsCyclicVector_gnsStarAlgHom _ a).symm)
  refine ⟨W, fun a x ↦ ?_⟩
  simpa using congrArg (fun T ↦ T x) (hW.2.2 a)

end MathlibAnnex.Analysis.CStarAlgebra
