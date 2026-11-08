import MathlibAnnex.Analysis.CStarAlgebra.CAR.HilbertBasisConsequences

set_option autoImplicit false
open scoped Cardinal ComplexOrder

universe uI uJ uH

open MathlibAnnex.CStarAlgebra.CAR

-- The canonical model is used directly; no separability or dimension premises are supplied.
example : Nonempty (HilbertBasis ℕ ℂ TraceHilbertSpace) :=
  nonempty_hilbertBasis_nat_traceHilbertSpace

-- Both basis indices may occupy independent universes.
example {ι : Type uI} {κ : Type uJ}
    (b : HilbertBasis ι ℂ TraceHilbertSpace)
    (c : HilbertBasis κ ℂ
      (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState)) :
    Cardinal.lift.{0} (#ι) = Cardinal.lift.{uI} (Cardinal.aleph0 : Cardinal.{0}) ∧
    Cardinal.lift.{0} (#κ) = Cardinal.lift.{uJ} (Cardinal.continuum : Cardinal.{0}) :=
  ⟨lift_mk_hilbertBasis_traceHilbertSpace b,
    lift_mk_hilbertBasis_atomicCounterexampleHilbert c⟩

-- The trace-space index is actually countable and infinite.
example {ι : Type uI} (b : HilbertBasis ι ℂ TraceHilbertSpace) :
    Countable ι ∧ Infinite ι := by
  have h : #ι = Cardinal.aleph0 := by
    simpa only [Cardinal.lift_uzero, Cardinal.lift_aleph0] using
      lift_mk_hilbertBasis_traceHilbertSpace b
  exact ⟨Cardinal.mk_le_aleph0_iff.mp h.le, Cardinal.aleph0_le_mk_iff.mp h.ge⟩

-- The general bridge keeps an arbitrary Hilbert-space universe.
example {ι : Type uI} {H : Type uH} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [Infinite ι] (b : HilbertBasis ι ℂ H)
    {κ : Cardinal.{uH}} (hκ : MathlibAnnex.Topology.HasDensityCharacter H κ) :
    Cardinal.lift.{uH} (#ι) = Cardinal.lift.{uI} κ :=
  b.lift_mk_eq_of_hasDensityCharacter hκ
