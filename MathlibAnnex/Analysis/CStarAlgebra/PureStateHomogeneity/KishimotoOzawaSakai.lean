import Mathlib.Algebra.Star.Unitary
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.Topology.Bases

/-!
# Conditional KOS boundary

This file defines the one external mathematical proposition used by the source
construction.  It introduces no global postulate.
-/

set_option autoImplicit false

open Set
open scoped ComplexOrder

namespace MathlibAnnex.CStarAlgebra

universe u

/-- Normalized positive continuous complex-linear functionals. -/
def stateSpace (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    Set (A →L[ℂ] ℂ) :=
  {phi | (∀ a : A, 0 ≤ a → 0 ≤ phi a) ∧ phi 1 = 1}

/-- Rebundle a member of the state space as Mathlib's positive linear map,
the input expected by the existing GNS construction. -/
def positiveLinearMapOfMemStateSpace
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
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
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A) (a : A) :
    positiveLinearMapOfMemStateSpace phi hphi a = phi a :=
  rfl

@[simp]
theorem positiveLinearMapOfMemStateSpace_one
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A) :
    positiveLinearMapOfMemStateSpace phi hphi 1 = 1 :=
  hphi.2

/-- A pure state is an extreme point of the ordinary state space. -/
def IsPureState (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (phi : A →L[ℂ] ℂ) : Prop :=
  phi ∈ (stateSpace A).extremePoints ℝ

/-- Simplicity with respect to norm-closed two-sided ideals. -/
def IsSimpleCStarAlgebra (A : Type u) [CStarAlgebra A] : Prop :=
  Nontrivial A ∧
    ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤

/-- The unital-simple approximately-inner consequence of KOS used here.
The state equation is `phi ∘ alpha = psi`; approximation is point-norm with
one unitary simultaneously serving every element of the finite set. -/
def KishimotoOzawaSakaiProperty : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [TopologicalSpace.SeparableSpace A],
    IsSimpleCStarAlgebra A →
    ∀ (phi psi : A →L[ℂ] ℂ), IsPureState A phi → IsPureState A psi →
      ∃ alpha : A ≃⋆ₐ[ℂ] A,
        (∀ a : A, phi (alpha a) = psi a) ∧
        ∀ (F : Finset A) (epsilon : ℝ), 0 < epsilon →
          ∃ v : unitary A, ∀ a ∈ F,
            ‖alpha a - (v : A) * a * star (v : A)‖ < epsilon

end MathlibAnnex.CStarAlgebra
