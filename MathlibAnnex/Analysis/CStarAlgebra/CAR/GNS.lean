import MathlibAnnex.Analysis.CStarAlgebra.CAR.RootCorner
import MathlibAnnex.Analysis.CStarAlgebra.GNSCyclic

/-!
# GNS realization of the finite-stage root state

The root-coordinate positive functional constructed from the actual binary matrix
stages is represented by Mathlib's GNS representation and its canonical class of
the unit.  The vector is normalized, implements the state, and is cyclic.
-/

set_option autoImplicit false

open scoped ComplexOrder InnerProductSpace

namespace MathlibAnnex.CStarAlgebra.CAR

/-- The canonical cyclic vector for the root-coordinate state at a finite stage. -/
noncomputable def rootGNSVector (n : ℕ) : (rootPositiveFunctional n).GNS :=
  (rootPositiveFunctional n).gnsCyclicVector

@[simp]
theorem norm_rootGNSVector (n : ℕ) : ‖rootGNSVector n‖ = 1 := by
  exact (rootPositiveFunctional n).norm_gnsCyclicVector (rootPositiveFunctional_one n)

/-- The root state is the vector state of the canonical GNS vector. -/
@[simp]
theorem inner_rootGNSVector_representation (n : ℕ) (a : Stage n) :
    ⟪rootGNSVector n,
      (rootPositiveFunctional n).gnsStarAlgHom a (rootGNSVector n)⟫_ℂ = a 0 0 := by
  simpa [rootGNSVector] using
    (rootPositiveFunctional n).inner_gnsCyclicVector_gnsStarAlgHom a

/-- The represented algebra orbit of the root GNS vector is dense. -/
theorem denseRange_rootGNS_orbit (n : ℕ) :
    DenseRange (fun a : Stage n ↦
      (rootPositiveFunctional n).gnsStarAlgHom a (rootGNSVector n)) := by
  simpa [rootGNSVector] using
    (rootPositiveFunctional n).denseRange_gnsStarAlgHom_apply_gnsCyclicVector

end MathlibAnnex.CStarAlgebra.CAR
