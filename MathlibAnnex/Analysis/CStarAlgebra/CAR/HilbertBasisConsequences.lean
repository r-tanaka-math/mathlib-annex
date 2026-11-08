import MathlibAnnex.Analysis.CStarAlgebra.CAR.Cardinality
import MathlibAnnex.Analysis.InnerProductSpace.HilbertBasisDensity

/-!
# Hilbert-basis cardinalities of the fixed CAR models

These results retain the ordinary CAR trace GNS space and the selected atomic
irreducible Hilbert model. They count orthonormal Hilbert-basis vectors, without
identifying an infinite Hilbert basis with an algebraic Hamel basis.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped Cardinal ComplexOrder

namespace MathlibAnnex.CStarAlgebra.CAR

universe uI

/-- Every Hilbert basis of the ordinary CAR trace space has countably infinitely
many vectors, including bases whose index type lies in an independent universe. -/
theorem lift_mk_hilbertBasis_traceHilbertSpace {ι : Type uI}
    (b : HilbertBasis ι ℂ TraceHilbertSpace) :
    Cardinal.lift.{0} (#ι) = Cardinal.lift.{uI} (Cardinal.aleph0 : Cardinal.{0}) := by
  classical
  letI : SeminormedAddCommGroup tracePositive.PreGNS :=
    PositiveLinearMap.instSeminormedAddCommGroupPreGNS tracePositive
  rcases finite_or_infinite ι with hfinite | hinfinite
  · letI : Finite ι := hfinite
    letI : Fintype ι := Fintype.ofFinite ι
    exact False.elim (not_finiteDimensional_separableCounterexampleHilbertSpace
      (Module.Finite.of_basis b.toOrthonormalBasis.toBasis))
  · letI : Infinite ι := hinfinite
    letI : TopologicalSpace.SeparableSpace TraceHilbertSpace :=
      separableSpace_traceHilbertSpace
    obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq TraceHilbertSpace
    have hspan : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤ := by
      apply top_unique
      intro x _
      change x ∈ closure (Submodule.span ℂ (Set.range v) : Set TraceHilbertSpace)
      exact closure_mono Submodule.subset_span (hv x)
    have hupper : Cardinal.lift.{0} (#ι) ≤
        Cardinal.lift.{uI} (Cardinal.aleph0 : Cardinal.{0}) := by
      simpa only [Cardinal.mk_nat] using b.lift_mk_le_of_dense_span v hspan
    apply le_antisymm hupper
    simpa only [Cardinal.lift_uzero, Cardinal.lift_aleph0] using
      (Cardinal.aleph0_le_mk ι)

/-- The fixed trace model admits a Hilbert basis indexed by the natural numbers.
An existing Hilbert basis is reindexed by the cardinal equality above. -/
theorem nonempty_hilbertBasis_nat_traceHilbertSpace :
    Nonempty (HilbertBasis ℕ ℂ TraceHilbertSpace) := by
  classical
  letI : SeminormedAddCommGroup tracePositive.PreGNS :=
    PositiveLinearMap.instSeminormedAddCommGroupPreGNS tracePositive
  obtain ⟨s, b, _⟩ := exists_hilbertBasis ℂ TraceHilbertSpace
  have hcard : Cardinal.lift.{0} (#s) = Cardinal.lift.{0} (#ℕ) := by
    simpa only [Cardinal.mk_nat] using lift_mk_hilbertBasis_traceHilbertSpace b
  obtain ⟨e⟩ : Nonempty (s ≃ ℕ) := Cardinal.lift_mk_eq'.mp hcard
  refine ⟨HilbertBasis.mk (b.orthonormal.comp e.symm e.symm.injective) ?_⟩
  have hrange : Set.range (fun n : ℕ => b (e.symm n)) = Set.range b := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨e.symm n, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e i, by simp only [Equiv.symm_apply_apply]⟩
  change ⊤ ≤ (Submodule.span ℂ (Set.range (fun n : ℕ ↦ b (e.symm n)))).topologicalClosure
  rw [hrange, b.dense_span]

/-- Every Hilbert basis of the original irreducible model has continuum many
vectors. A finite index is excluded by the existing continuum density lower
bound and the countable rational sums; the infinite case uses the general
bridge between attained density and Hilbert-basis cardinality. -/
theorem lift_mk_hilbertBasis_atomicCounterexampleHilbert {ι : Type uI}
    (b : HilbertBasis ι ℂ
      (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState)) :
    Cardinal.lift.{0} (#ι) =
      Cardinal.lift.{uI} (Cardinal.continuum : Cardinal.{0}) := by
  classical
  rcases finite_or_infinite ι with hfinite | hinfinite
  · letI : Finite ι := hfinite
    letI : Fintype ι := Fintype.ofFinite ι
    have hcount : (Set.range b.rationalSpanSum).Countable := Set.countable_range _
    have hbound : (Cardinal.continuum : Cardinal.{0}) ≤ Cardinal.aleph0 :=
      (continuum_le_cardinalMk_dense_atomicCounterexampleHilbert
        _ b.denseRange_rationalSpanSum).trans hcount.le_aleph0
    exact False.elim ((not_le_of_gt Cardinal.aleph0_lt_continuum) hbound)
  · letI : Infinite ι := hinfinite
    exact b.lift_mk_eq_of_hasDensityCharacter
      hasDensityCharacter_atomicCounterexampleHilbert

end MathlibAnnex.CStarAlgebra.CAR
