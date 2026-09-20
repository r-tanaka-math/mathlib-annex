import MathlibAnnex.Analysis.CStarAlgebra.Schur

/-!
# The algebraic represented double commutant

An irreducible unital representation has scalar bounded commutant by the
existing arbitrary-dimensional Schur theorem.  Hence its double commutant
is all of `B(H)`.  This identifies the represented *algebraic* envelope used
for the main averaging route.  A strong/weak operator closure identification
and injectivity are separate analytical inputs, not consequences asserted
here.
-/

set_option autoImplicit false
open scoped InnerProduct

namespace MathlibAnnex.CStarAlgebra.TensorAveraging

variable {A H : Type*} [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Nontrivial H]

/-- Every operator belongs to the double centralizer of an irreducible
representation's image. -/
theorem irreducible_bicommutant_full
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi) :
    Set.centralizer (Set.centralizer (Set.range pi)) = Set.univ := by
  ext T
  constructor
  · intro _
    trivial
  · intro _ S hS
    have hcomm : StarAlgHom.InCommutant pi S := by
      intro a
      exact (hS (pi a) ⟨a, rfl⟩).symm
    obtain ⟨z, hz⟩ := StarAlgHom.eq_algebraMap_of_irreducible pi hpi S hcomm
    rw [hz]
    exact Algebra.commutes z T

end MathlibAnnex.CStarAlgebra.TensorAveraging
