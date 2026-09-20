import MathlibAnnex.Analysis.CStarAlgebra.CAR.TargetReconstruction
import MathlibAnnex.Analysis.CStarAlgebra.PureStateGNS.IrreduciblePure
import MathlibAnnex.Analysis.CStarAlgebra.AtomicConstruction.GeneratedReduction
import MathlibAnnex.Analysis.InnerProductSpace.Reduction

/-!
# The zero-defect branch for the completed-CAR target

If every represented initial limiting fixed space vanished, reduction for the
restricted completed-CAR representation would pass through the target-side
strong shell sums to every added generator.  It would therefore pass to the
whole norm-closed generated target.  Target irreducibility would make the
source restriction irreducible, while chosen pure-GNS coverage supplies a
nonzero common fixed vector.  This contradiction closes the zero-defect
branch without moving any strong limit through the representation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Filter Topology
open scoped ComplexOrder ENNReal lp InnerProduct

namespace MathlibAnnex.CStarAlgebra.CAR

open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.Analysis.InnerProductSpace

universe v

/-- Under the all-zero limiting-defect hypothesis, the completed-CAR
restriction of an irreducible target representation is itself irreducible. -/
theorem isIrreducible_restrictedRepresentation_of_all_fixed_bot
    (family : RepresentativeShellFamily)
    (L : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit →
      MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState)
    (hLunit : ∀ i, L i ∈ unitary
      (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState))
    (hLsource : ∀ i n, (L i).comp (selectedAtomicRepresentation
      (transportedFlag family i n - transportedFlag family i (n + 1))) =
        representedShellLink family i n)
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (rho : Representation (AtomicTarget L) K)
    (hrho : rho.IsIrreducible)
    (hzero : ∀ i, (⨅ n,
      ((restrictedRepresentation L rho) (transportedFlag family i n)).range) = ⊥) :
    (restrictedRepresentation L rho).IsIrreducible := by
  letI : Nontrivial K := Representation.nontrivial_of_isNonzero rho hrho.1
  refine ⟨Representation.isNonzero_of_nontrivial _, ?_⟩
  intro M hM
  have hgenerator (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
      M.Reduces (rho (MathlibAnnex.CStarAlgebra.AtomicConstruction.generator selectedAtomicRepresentation L i)) := by
    obtain ⟨S, T, P, Q, R, hS, hT, -, -, hAdj, -, hPrange, -, -, -, -,
        heq, hR, -, -, -, -⟩ :=
      exists_targetShellReconstruction family L hLunit hLsource rho i
    have hPzero : P = 0 := by
      apply ContinuousLinearMap.ext
      intro x
      have hx : P x ∈ P.range := ⟨x, rfl⟩
      rw [hPrange, hzero i, Submodule.mem_bot] at hx
      exact hx
    have hRzero : R = 0 := by
      rw [hR, hPzero]
      simp
    have hsum :
        ((Unitary.linearIsometryEquiv
          (representedGeneratorUnitary L hLunit rho i) : K ≃ₗᵢ[ℂ] K) :
            K →L[ℂ] K) = S := by
      simpa [hRzero] using heq
    have hW (n : ℕ) : M.Reduces
        ((restrictedRepresentation L rho)
          ((representativeShellData family i).link n)) := by
      constructor
      · intro x hx
        exact (hM.2 ((representativeShellData family i).link n) x hx).1
      · intro x hx
        exact (hM.2 ((representativeShellData family i).link n) x hx).2
    have hSreduces : M.Reduces S :=
      Submodule.Reduces.of_stronglyConverges_partialSum hM.1 hW hS hT hAdj
    change M.Reduces
      (((representedGeneratorUnitary L hLunit rho i : unitary (K →L[ℂ] K)) :
        K →L[ℂ] K))
    rw [show ((representedGeneratorUnitary L hLunit rho i :
      unitary (K →L[ℂ] K)) : K →L[ℂ] K) = S by simpa using hsum]
    exact hSreduces
  have hsource (a : Limit) :
      M.Reduces (rho (MathlibAnnex.CStarAlgebra.AtomicConstruction.sourceHom selectedAtomicRepresentation L a)) := by
    constructor
    · intro x hx
      exact (hM.2 a x hx).1
    · intro x hx
      exact (hM.2 a x hx).2
  have hall := MathlibAnnex.CStarAlgebra.AtomicConstruction.reduces_concreteTarget_of_generators
    selectedAtomicRepresentation L rho M hM.1 hsource hgenerator
  apply hrho.2 M
  refine ⟨hM.1, ?_⟩
  intro a x hx
  exact ⟨(hall a).1 hx, (hall a).2 hx⟩

/-- Every irreducible representation of the actual completed-CAR atomic
target has a surviving represented initial limiting defect.  This is the
formal conclusion of the all-zero/surviving-defect split's first branch. -/
theorem exists_nonzero_targetFixedSpace
    (family : RepresentativeShellFamily)
    (L : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit →
      MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState)
    (hLunit : ∀ i, L i ∈ unitary
      (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState))
    (hLsource : ∀ i n, (L i).comp (selectedAtomicRepresentation
      (transportedFlag family i n - transportedFlag family i (n + 1))) =
        representedShellLink family i n)
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (rho : Representation (AtomicTarget L) K)
    (hrho : rho.IsIrreducible) :
    ∃ i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit,
      (⨅ n, ((restrictedRepresentation L rho)
        (transportedFlag family i n)).range) ≠ ⊥ := by
  by_contra hnone
  have hzero : ∀ i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit,
      (⨅ n, ((restrictedRepresentation L rho)
        (transportedFlag family i n)).range) = ⊥ := by
    intro i
    by_contra hi
    exact hnone ⟨i, hi⟩
  have hsigma := isIrreducible_restrictedRepresentation_of_all_fixed_bot
    family L hLunit hLsource rho hrho hzero
  obtain ⟨j, e, he⟩ := MathlibAnnex.CStarAlgebra.irreducible_covered_by_pureState_representative
    completedRootPureState (restrictedRepresentation L rho) hsigma
  let xi := MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState j
  let eta : K := e.symm xi
  have heta_norm : ‖eta‖ = 1 := by
    simp [eta, xi, MathlibAnnex.CStarAlgebra.PureState.norm_selectedVector]
  have hfix (n : ℕ) :
      (restrictedRepresentation L rho) (transportedFlag family j n) eta = eta := by
    apply e.injective
    calc
      e ((restrictedRepresentation L rho) (transportedFlag family j n) eta) =
          (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState j)
            (transportedFlag family j n) (e eta) := by
        simpa [MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation] using
          he (transportedFlag family j n) eta
      _ = (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState j)
            (transportedFlag family j n) xi := by simp [eta]
      _ = xi := selectedVector_fixed_transportedFlag family j n
      _ = e eta := by simp [eta]
  have heta_mem : eta ∈ (⨅ n,
      ((restrictedRepresentation L rho) (transportedFlag family j n)).range) := by
    rw [Submodule.mem_iInf]
    intro n
    exact ⟨eta, hfix n⟩
  rw [hzero j, Submodule.mem_bot] at heta_mem
  have := congrArg norm heta_mem
  simpa [heta_norm] using this

end MathlibAnnex.CStarAlgebra.CAR
