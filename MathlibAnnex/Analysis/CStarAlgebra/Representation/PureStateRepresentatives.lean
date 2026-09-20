import Mathlib.Data.Quot
import MathlibAnnex.Analysis.CStarAlgebra.GNSCyclic
import MathlibAnnex.Analysis.CStarAlgebra.Representation
import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.KishimotoOzawaSakai

/-!
# Set-indexed representatives of pure-state GNS classes

Pure states live in one ordinary continuous-dual type.  Quotienting that type
by unitary equivalence of its GNS representations therefore produces a genuine
set-sized index type.  A supplied root state is retained literally as the
representative of its class.

This file deliberately stops short of claiming coverage of arbitrary
irreducible representations: that additional statement requires the full
pure-state/GNS irreducibility bridge.
-/

set_option autoImplicit false

open Set
open scoped ComplexOrder

namespace MathlibAnnex.CStarAlgebra

universe u

variable (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A pure state, bundled inside the continuous dual. -/
abbrev PureState := {phi : A →L[ℂ] ℂ // IsPureState A phi}

namespace PureState

variable {A}

theorem mem_stateSpace (phi : PureState A) : phi.1 ∈ stateSpace A := by
  exact extremePoints_subset phi.2

/-- The positive-linear-map view used by Mathlib's GNS construction. -/
noncomputable def positiveFunctional (phi : PureState A) : A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ phi.1.toLinearMap phi.mem_stateSpace.1

@[simp]
theorem positiveFunctional_apply (phi : PureState A) (a : A) :
    phi.positiveFunctional a = phi.1 a := rfl

@[simp]
theorem positiveFunctional_one (phi : PureState A) :
    phi.positiveFunctional 1 = 1 :=
  phi.mem_stateSpace.2

/-- Equivalence of the GNS representations associated to two pure states. -/
def GNSEquivalent (phi psi : PureState A) : Prop :=
  StarAlgHom.UnitaryEquivalent phi.positiveFunctional.gnsStarAlgHom
    psi.positiveFunctional.gnsStarAlgHom

theorem GNSEquivalent.refl (phi : PureState A) : phi.GNSEquivalent phi :=
  StarAlgHom.unitaryEquivalent_refl _

theorem GNSEquivalent.symm {phi psi : PureState A} (h : phi.GNSEquivalent psi) :
    psi.GNSEquivalent phi :=
  StarAlgHom.UnitaryEquivalent.symm h

theorem GNSEquivalent.trans {phi psi chi : PureState A}
    (h₁ : phi.GNSEquivalent psi) (h₂ : psi.GNSEquivalent chi) :
    phi.GNSEquivalent chi :=
  StarAlgHom.UnitaryEquivalent.trans h₁ h₂

/-- The equivalence relation used for selecting GNS classes. -/
def gnsSetoid : Setoid (PureState A) where
  r := GNSEquivalent
  iseqv := ⟨GNSEquivalent.refl, GNSEquivalent.symm, GNSEquivalent.trans⟩

/-- The set-sized quotient of pure states by unitary equivalence of GNS representations. -/
abbrev GNSClass (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :=
  Quotient (gnsSetoid (A := A))

def classOf (phi : PureState A) : GNSClass A :=
  Quotient.mk (gnsSetoid (A := A)) phi

/-- Select one state per GNS class, but retain the requested root state literally. -/
noncomputable def representative (root : PureState A) (j : GNSClass A) : PureState A :=
  by
    classical
    exact if j = root.classOf then root else Quotient.out j

@[simp]
theorem classOf_representative (root : PureState A) (j : GNSClass A) :
    (representative root j).classOf = j := by
  classical
  by_cases h : j = root.classOf
  · simp [representative, h]
  · change Quotient.mk (gnsSetoid (A := A))
      (if j = root.classOf then root else Quotient.out j) = j
    rw [if_neg h]
    exact Quotient.out_eq j

@[simp]
theorem representative_root (root : PureState A) :
    representative root root.classOf = root := by
  classical
  simp [representative]

/-- Distinct selected indices have inequivalent GNS representations. -/
theorem representative_injective_on_classes (root : PureState A) {i j : GNSClass A}
    (h : (representative root i).GNSEquivalent (representative root j)) : i = j := by
  rw [← classOf_representative root i, ← classOf_representative root j]
  exact Quotient.sound h

/-- Every pure-state GNS class is represented by the selected family. -/
theorem representative_covers (root phi : PureState A) :
    (representative root phi.classOf).GNSEquivalent phi := by
  exact @Quotient.exact _ (gnsSetoid (A := A)) (representative root phi.classOf) phi
    (classOf_representative root phi.classOf)

/-- Every selected GNS cyclic vector has norm one. -/
theorem norm_representative_gnsCyclicVector (root : PureState A) (j : GNSClass A) :
    ‖(representative root j).positiveFunctional.gnsCyclicVector‖ = 1 := by
  exact (representative root j).positiveFunctional.norm_gnsCyclicVector
    (representative root j).positiveFunctional_one

/-- Every selected GNS algebra orbit is dense. -/
theorem denseRange_representative_gns_orbit (root : PureState A) (j : GNSClass A) :
    DenseRange (fun a : A ↦
      (representative root j).positiveFunctional.gnsStarAlgHom a
        (representative root j).positiveFunctional.gnsCyclicVector) := by
  exact (representative root j).positiveFunctional
    |>.denseRange_gnsStarAlgHom_apply_gnsCyclicVector

end PureState

end MathlibAnnex.CStarAlgebra
