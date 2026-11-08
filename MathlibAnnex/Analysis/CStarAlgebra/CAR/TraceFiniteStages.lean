import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceGNSModel
import MathlibAnnex.Analysis.CStarAlgebra.CAR.Simplicity
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite matrix stages in the fixed CAR trace representation

The subalgebras here are the represented copies of the existing stages
`Stage n = M_(2^n)(ℂ)`. They contain the identity of the full operator algebra,
form an increasing sequence, and norm-approximate every represented CAR element.
A containing algebra is infinite-dimensional because it contains a faithful
linear image of `CAR.Limit`, independently of the dimension of its representation
space.
-/

set_option autoImplicit false

namespace MathlibAnnex.CStarAlgebra.CAR

open MathlibAnnex.Analysis.CStarAlgebra

/-- The CAR trace representation is faithful: CAR is simple and the normalized
trace vector makes its Hilbert space nonzero. -/
theorem traceRepresentation_injective : Function.Injective traceRepresentation := by
  letI : Nontrivial TraceHilbertSpace := nontrivial_traceHilbertSpace
  exact traceRepresentation.toRingHom.injective

/-- The actual `n`-th CAR matrix stage acting on the fixed trace Hilbert space. -/
noncomputable def traceStageRepresentation (n : ℕ) :
    Stage n →⋆ₐ[ℂ] (TraceHilbertSpace →L[ℂ] TraceHilbertSpace) :=
  traceRepresentation.comp (ofStage n)

/-- The unital star subalgebra which is the image of the `n`-th matrix stage. -/
noncomputable def traceStageRange (n : ℕ) :
    StarSubalgebra ℂ (TraceHilbertSpace →L[ℂ] TraceHilbertSpace) :=
  (traceStageRepresentation n).range

/-- Membership retains a witness in the original matrix stage. -/
theorem mem_traceStageRange_iff (n : ℕ)
    (T : TraceHilbertSpace →L[ℂ] TraceHilbertSpace) :
    T ∈ traceStageRange n ↔ ∃ a : Stage n, traceRepresentation (ofStage n a) = T :=
  Iff.rfl

/-- Every finite stage lies in the range of the same CAR trace representation. -/
theorem traceStageRange_le_range (n : ℕ) : traceStageRange n ≤ traceRepresentation.range := by
  rintro T ⟨a, rfl⟩
  exact ⟨ofStage n a, rfl⟩

/-- The existing compatible stage maps give inclusion of the represented stages. -/
theorem traceStageRange_mono : Monotone traceStageRange := by
  intro n m hnm T hT
  obtain ⟨a, rfl⟩ := (mem_traceStageRange_iff n T).1 hT
  refine (mem_traceStageRange_iff m _).2 ⟨embed n m hnm a, ?_⟩
  rw [ofStage_embed]

/-- The finite stages form a nonempty inclusion-directed family. -/
theorem traceStageRange_directed : Directed (· ≤ ·) traceStageRange :=
  traceStageRange_mono.directed_le

/-- Each represented stage is the original matrix algebra itself, via a unital
star algebra equivalence onto its image. -/
noncomputable def traceStageEquiv (n : ℕ) : Stage n ≃⋆ₐ[ℂ] traceStageRange n :=
  StarAlgEquiv.ofInjective (traceStageRepresentation n)
    (traceRepresentation_injective.comp (ofStage_injective n))

/-- The represented stages are finite-dimensional algebras, not algebras of
finite-rank operators on the trace Hilbert space. -/
theorem finiteDimensional_traceStageRange (n : ℕ) :
    FiniteDimensional ℂ (traceStageRange n) :=
  (traceStageEquiv n).toAlgEquiv.toLinearEquiv.finiteDimensional

/-- The dimension is exactly the square of the existing matrix size. -/
theorem finrank_traceStageRange (n : ℕ) :
    Module.finrank ℂ (traceStageRange n) = (2 ^ n) * (2 ^ n) := by
  rw [← (traceStageEquiv n).toAlgEquiv.toLinearEquiv.finrank_eq]
  exact finrank_stage n

/-- Each represented CAR element is in the operator-norm closure of the union
of the finite matrix stages. This is the norm-density input for later SOT closure. -/
theorem traceRepresentation_mem_closure_iUnion_traceStageRange (a : Limit) :
    traceRepresentation a ∈ closure
      (⋃ n, (traceStageRange n : Set (TraceHilbertSpace →L[ℂ] TraceHilbertSpace))) := by
  have himage : traceRepresentation '' (⋃ n, Set.range (ofStage n)) ⊆
      ⋃ n, (traceStageRange n : Set (TraceHilbertSpace →L[ℂ] TraceHilbertSpace)) := by
    rintro T ⟨b, hb, rfl⟩
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hb
    obtain ⟨c, rfl⟩ := hn
    exact Set.mem_iUnion.2 ⟨n, (mem_traceStageRange_iff n _).2 ⟨c, rfl⟩⟩
  have hcont : Continuous traceRepresentation :=
    (Representation.continuousLinearMap traceRepresentation).continuous
  exact (closure_mono himage)
    (hcont.range_subset_closure_image_dense dense_stageRange ⟨a, rfl⟩)

/-- Norm closure of the finite stage union equals norm closure of the represented
CAR algebra. This statement does not identify norm and strong operator topology. -/
theorem closure_iUnion_traceStageRange_eq_closure_range :
    closure (⋃ n, (traceStageRange n :
      Set (TraceHilbertSpace →L[ℂ] TraceHilbertSpace))) =
      closure (traceRepresentation.range :
        Set (TraceHilbertSpace →L[ℂ] TraceHilbertSpace)) := by
  apply Set.Subset.antisymm
  · apply closure_mono
    exact Set.iUnion_subset fun n ↦ traceStageRange_le_range n
  · apply closure_minimal
    · rintro T ⟨a, rfl⟩
      exact traceRepresentation_mem_closure_iUnion_traceStageRange a
    · exact isClosed_closure

/-- An algebra containing the faithful CAR image is infinite-dimensional. This
uses the algebraic dimension of CAR, not the dimension of its Hilbert space. -/
theorem not_finiteDimensional_of_range_traceRepresentation_le
    (S : StarSubalgebra ℂ (TraceHilbertSpace →L[ℂ] TraceHilbertSpace))
    (hS : traceRepresentation.range ≤ S) : ¬ FiniteDimensional ℂ S := by
  intro hfinite
  letI : FiniteDimensional ℂ S := hfinite
  let f : Limit →⋆ₐ[ℂ] S := traceRepresentation.codRestrict S (fun a ↦ hS ⟨a, rfl⟩)
  apply not_finiteDimensional
  exact FiniteDimensional.of_injective f.toLinearMap (fun x y hxy ↦
    traceRepresentation_injective (congrArg Subtype.val hxy))

end MathlibAnnex.CStarAlgebra.CAR
