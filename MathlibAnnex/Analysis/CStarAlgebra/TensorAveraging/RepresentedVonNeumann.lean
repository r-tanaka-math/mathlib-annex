import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.RepresentedEnvelope
import Mathlib.Analysis.VonNeumannAlgebra.Basic

/-!
# The represented concrete von Neumann envelope

Every concrete von Neumann algebra containing an irreducible represented
image is all of `B(H)`.  This uses the concrete algebra's defining
double-centralizer identity and Schur's lemma.  It does not construct
Haagerup's invariant mean or the missing normal extension of arbitrary
bilinear forms.
-/

set_option autoImplicit false
open scoped InnerProduct

namespace MathlibAnnex.CStarAlgebra.TensorAveraging

variable {A H : Type*} [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Nontrivial H]

theorem irreducible_containing_vonNeumann_full
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (S : VonNeumannAlgebra H)
    (hcontains : ∀ a : A, pi a ∈ S) :
    (S : Set (H →L[ℂ] H)) = Set.univ := by
  ext T
  constructor
  · intro _
    trivial
  · intro _
    change T ∈ (S : Set (H →L[ℂ] H))
    rw [← VonNeumannAlgebra.centralizer_centralizer S]
    have hT : T ∈ Set.centralizer (Set.centralizer (Set.range pi)) := by
      rw [irreducible_bicommutant_full pi hpi]
      trivial
    intro R hR
    apply hT R
    intro x hx
    rcases hx with ⟨a, rfl⟩
    exact hR (pi a) (hcontains a)

end MathlibAnnex.CStarAlgebra.TensorAveraging
