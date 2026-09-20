import MathlibAnnex.Analysis.CStarAlgebra.Representation.Adapters
import MathlibAnnex.Analysis.CStarAlgebra.Representation.AtomicCommutant
import MathlibAnnex.Analysis.CStarAlgebra.AtomicConstruction.Concrete

/-!
# A source-parametric atomic model from projection shells

This theorem consumes only representation-local source data: pairwise
inequivalent irreducible fibers, selected unit vectors, decreasing normalized
flags, and shell partial isometries with their exact initial/final supports.
It constructs the off-diagonal rank-one completions, proves their termwise
shell relations, and proves irreducibility of the displayed concrete target.
No target capture, target simplicity, or final Naimark conclusion is a field
or hypothesis.
-/

set_option autoImplicit false

open Filter Topology
open scoped ENNReal lp InnerProduct

namespace MathlibAnnex.CStarAlgebra.AtomicConstruction

universe u v w

variable {A : Type u} [CStarAlgebra A]
variable {I : Type v} {H : I → Type w}
variable [DecidableEq I]
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)] [∀ i, Nontrivial (H i)]

open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.Analysis.InnerProductSpace

/-- Natural shell data on an arbitrary family of pairwise inequivalent
irreducible fibers produces actual inter-block unitary generators and an
irreducible concrete generated representation. -/
theorem exists_irreducible_atomicShellModel
    (pi : ∀ i, Representation A (H i))
    (hirr : ∀ i, StarAlgHom.IsIrreducible (pi i))
    (hno : ∀ ⦃i j : I⦄, i ≠ j → ∀ e : H i ≃ₗᵢ[ℂ] H j,
      ¬ StarAlgHom.Intertwines (pi i) (pi j) (e : H i →L[ℂ] H j))
    (o : I) (xi : ∀ i, H i) (hxi : ∀ i, ‖xi i‖ = 1)
    (W : I → ℕ → HilbertSum H →L[ℂ] HilbertSum H)
    (U V : I → ℕ → Submodule ℂ (HilbertSum H))
    [∀ i n, (U i n).HasOrthogonalProjection]
    [∀ i n, (V i n).HasOrthogonalProjection]
    [∀ i, (⨅ n, U i n).HasOrthogonalProjection]
    [∀ i, (⨅ n, V i n).HasOrthogonalProjection]
    (hU : ∀ i, Antitone (U i)) (hV : ∀ i, Antitone (V i))
    (hU0 : ∀ i, U i 0 = ⊤) (hV0 : ∀ i, V i 0 = ⊤)
    (hInitial : ∀ i n, ((W i n)†).comp (W i n) =
      Submodule.projectionShell (U i) n)
    (hFinal : ∀ i n, (W i n).comp ((W i n)†) =
      Submodule.projectionShell (V i) n)
    (hUinf : ∀ i, (⨅ n, U i n).starProjection =
      InnerProductSpace.rankOne ℂ (coordinateEmbedding i (xi i))
        (coordinateEmbedding i (xi i)))
    (hVinf : ∀ i, (⨅ n, V i n).starProjection =
      InnerProductSpace.rankOne ℂ (coordinateEmbedding o (xi o))
        (coordinateEmbedding o (xi o))) :
    ∃ L : I → HilbertSum H →L[ℂ] HilbertSum H,
      (∀ i, L i ∈ unitary (HilbertSum H →L[ℂ] HilbertSum H)) ∧
      (∀ i, L i (coordinateEmbedding i (xi i)) =
        coordinateEmbedding o (xi o)) ∧
      (∀ i n, (L i).comp (Submodule.projectionShell (U i) n) = W i n) ∧
      Representation.IsIrreducible
        (ambientInclusion (atomicRepresentation pi) L) := by
  have hexists (i : I) : ∃ S : HilbertSum H →L[ℂ] HilbertSum H,
      ContinuousLinearMap.StronglyConverges
          (ContinuousLinearMap.partialSum (W i)) atTop S ∧
      (S + InnerProductSpace.rankOne ℂ
          (coordinateEmbedding o (xi o)) (coordinateEmbedding i (xi i))) ∈
        unitary (HilbertSum H →L[ℂ] HilbertSum H) ∧
      (S + InnerProductSpace.rankOne ℂ
          (coordinateEmbedding o (xi o)) (coordinateEmbedding i (xi i)))
          (coordinateEmbedding i (xi i)) = coordinateEmbedding o (xi o) ∧
      ∀ n, (S + InnerProductSpace.rankOne ℂ
          (coordinateEmbedding o (xi o)) (coordinateEmbedding i (xi i))).comp
          (Submodule.projectionShell (U i) n) = W i n := by
    apply ContinuousLinearMap.exists_rankOneCompletion_of_projectionShells
      (W i) (U i) (V i) (hU i) (hV i) (hU0 i) (hV0 i)
      (hInitial i) (hFinal i)
      (coordinateEmbedding o (xi o)) (coordinateEmbedding i (xi i))
    · simpa [norm_coordinateEmbedding] using hxi o
    · simpa [norm_coordinateEmbedding] using hxi i
    · exact hUinf i
    · exact hVinf i
  choose S hS hunit hmap hterm using hexists
  let L : I → HilbertSum H →L[ℂ] HilbertSum H := fun i ↦
    S i + InnerProductSpace.rankOne ℂ
      (coordinateEmbedding o (xi o)) (coordinateEmbedding i (xi i))
  have hLunit : ∀ i, L i ∈ unitary (HilbertSum H →L[ℂ] HilbertSum H) := by
    intro i
    exact hunit i
  have hLmap : ∀ i, L i (coordinateEmbedding i (xi i)) =
      coordinateEmbedding o (xi o) := by
    intro i
    exact hmap i
  have hLterm : ∀ i n, (L i).comp
      (Submodule.projectionShell (U i) n) = W i n := by
    intro i n
    exact hterm i n
  have hrootne : coordinateEmbedding o (xi o) ≠ 0 := by
    intro hzero
    have := congrArg norm hzero
    simpa [norm_coordinateEmbedding, hxi o] using this
  letI : Nontrivial (HilbertSum H) := nontrivial_of_ne
    (coordinateEmbedding o (xi o)) 0 hrootne
  have hmodelStar : StarAlgHom.IsIrreducible
      (ambientInclusion (atomicRepresentation pi) L) := by
    apply StarAlgHom.isIrreducible_of_commutant_eq_algebraMap
    intro T hT
    apply eq_algebraMap_of_atomic_of_links pi hirr hno o xi hxi L hLmap T
    · intro a
      have h := hT (sourceHom (atomicRepresentation pi) L a)
      change Commute T
        (((sourceHom (atomicRepresentation pi) L a :
          concreteTarget (atomicRepresentation pi) L) :
            HilbertSum H →L[ℂ] HilbertSum H)) at h
      rw [sourceHom_coe] at h
      exact h
    · intro i
      have h := hT (generator (atomicRepresentation pi) L i)
      change Commute T
        (((generator (atomicRepresentation pi) L i :
          concreteTarget (atomicRepresentation pi) L) :
            HilbertSum H →L[ℂ] HilbertSum H)) at h
      rw [generator_coe] at h
      exact h
  exact ⟨L, hLunit, hLmap, hLterm,
    (Representation.isIrreducible_iff_starAlgHom
      (ambientInclusion (atomicRepresentation pi) L)).2 hmodelStar⟩

end MathlibAnnex.CStarAlgebra.AtomicConstruction
