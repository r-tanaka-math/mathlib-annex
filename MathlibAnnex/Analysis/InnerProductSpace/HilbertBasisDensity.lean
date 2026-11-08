import MathlibAnnex.Analysis.InnerProductSpace.HilbertBasisCardinalNets
import MathlibAnnex.Analysis.InnerProductSpace.HilbertBasisRangeCardinality
import MathlibAnnex.Topology.DensityCharacter

/-!
# Exact density and the cardinality of an infinite Hilbert basis

The upper estimate uses the existing comparison with a dense spanning family.
The reverse estimate uses the existing rational finite sums of basis vectors.
The basis index and the Hilbert space may live in independent universes.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped Cardinal

universe uF uI uH

namespace HilbertBasis

variable {𝕜 : Type uF} [RCLike 𝕜]
variable {ι : Type uI} {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- For an infinite Hilbert basis, the index cardinal is the attained density
character. The two cardinal lifts compare independent index and space universes. -/
theorem lift_mk_eq_of_hasDensityCharacter (b : HilbertBasis ι 𝕜 H) [Infinite ι]
    {κ : Cardinal.{uH}} (hκ : MathlibAnnex.Topology.HasDensityCharacter H κ) :
    Cardinal.lift.{uH} (#ι) = Cardinal.lift.{uI} κ := by
  apply le_antisymm
  · obtain ⟨s, hs, hcard⟩ := hκ.exists_dense
    have hspan :
        (Submodule.span 𝕜 (Set.range ((↑) : s → H))).topologicalClosure = ⊤ := by
      apply top_unique
      intro x _
      change x ∈ closure (Submodule.span 𝕜 (Set.range ((↑) : s → H)) : Set H)
      apply closure_mono (s := s) ?_ (hs x)
      intro y hy
      exact Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩
    simpa only [hcard] using b.lift_mk_le_of_dense_span ((↑) : s → H) hspan
  · have hsmall : κ ≤ #(Set.range b.rationalSpanSum) :=
      hκ.le_cardinalMk _ b.denseRange_rationalSpanSum
    exact (Cardinal.lift_le.mpr hsmall).trans b.lift_mk_range_rationalSpanSum_le

end HilbertBasis
