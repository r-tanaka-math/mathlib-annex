import MathlibAnnex.Analysis.CStarAlgebra.GNS.Cyclic
import MathlibAnnex.Analysis.CStarAlgebra.GNSCyclic

/-! Exact adapters for the two inherited names of the canonical GNS vector. -/

set_option autoImplicit false

open scoped ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra.PositiveLinearMap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The project-local and Mathlib-namespace canonical vectors are the same
completion point, not merely unitarily equivalent choices. -/
theorem gnsCyclicVector_eq_root (f : A →ₚ[ℂ] ℂ) :
    gnsCyclicVector f = _root_.PositiveLinearMap.gnsCyclicVector f :=
  rfl

end MathlibAnnex.Analysis.CStarAlgebra.PositiveLinearMap
