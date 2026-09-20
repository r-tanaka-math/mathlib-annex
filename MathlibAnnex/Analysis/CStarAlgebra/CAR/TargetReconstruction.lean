import MathlibAnnex.Analysis.CStarAlgebra.CAR.AtomicModel
import MathlibAnnex.Analysis.CStarAlgebra.Representation.ShellReconstruction

/-!
# Reconstructing completed-CAR shells in an arbitrary target representation

The strong sums in this file are formed on the target Hilbert space.  The
source representation contributes only finite algebraic projection and
support identities.  Thus no continuity of an arbitrary representation for
the strong-operator topology is used.
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

/-- The actual concrete target associated with a completed-CAR atomic family. -/
abbrev AtomicTarget
    (L : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit →
      MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState) :=
  MathlibAnnex.CStarAlgebra.AtomicConstruction.concreteTarget selectedAtomicRepresentation L

/-- Restriction of an arbitrary target representation to the actual completed
CAR source. -/
noncomputable def restrictedRepresentation
    (L : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit →
      MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState)
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (rho : Representation (AtomicTarget L) K) :
    Representation Limit K :=
  rho.comp (MathlibAnnex.CStarAlgebra.AtomicConstruction.sourceHom selectedAtomicRepresentation L)

/-- A target generator is unitary in every represented Hilbert space. -/
noncomputable def representedGeneratorUnitary
    (L : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit →
      MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState)
    (hLunit : ∀ i, L i ∈ unitary
      (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState))
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (rho : Representation (AtomicTarget L) K)
    (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) : unitary (K →L[ℂ] K) := by
  have htarget : MathlibAnnex.CStarAlgebra.AtomicConstruction.generator selectedAtomicRepresentation L i ∈
      unitary (AtomicTarget L) := by
    rw [Unitary.mem_iff]
    constructor
    · apply Subtype.ext
      exact (hLunit i).1
    · apply Subtype.ext
      exact (hLunit i).2
  exact ⟨rho (MathlibAnnex.CStarAlgebra.AtomicConstruction.generator selectedAtomicRepresentation L i),
    Unitary.map_mem rho htarget⟩

@[simp]
theorem representedGeneratorUnitary_coe
    (L : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit →
      MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState)
    (hLunit : ∀ i, L i ∈ unitary
      (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState))
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (rho : Representation (AtomicTarget L) K)
    (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
    ((representedGeneratorUnitary L hLunit rho i : unitary (K →L[ℂ] K)) :
      K →L[ℂ] K) =
      rho (MathlibAnnex.CStarAlgebra.AtomicConstruction.generator selectedAtomicRepresentation L i) := rfl

/-- The source shell relation becomes a finite relation in every target
representation. -/
theorem representedGenerator_comp_sourceShell
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
    (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (n : ℕ) :
    ((Unitary.linearIsometryEquiv
      (representedGeneratorUnitary L hLunit rho i) : K ≃ₗᵢ[ℂ] K) :
        K →L[ℂ] K).comp
      (restrictedRepresentation L rho
        (transportedFlag family i n - transportedFlag family i (n + 1))) =
      restrictedRepresentation L rho
        ((representativeShellData family i).link n) := by
  have htarget :
      MathlibAnnex.CStarAlgebra.AtomicConstruction.generator selectedAtomicRepresentation L i *
          MathlibAnnex.CStarAlgebra.AtomicConstruction.sourceHom selectedAtomicRepresentation L
            (transportedFlag family i n - transportedFlag family i (n + 1)) =
        MathlibAnnex.CStarAlgebra.AtomicConstruction.sourceHom selectedAtomicRepresentation L
          ((representativeShellData family i).link n) := by
    apply Subtype.ext
    exact hLsource i n
  change rho (MathlibAnnex.CStarAlgebra.AtomicConstruction.generator selectedAtomicRepresentation L i) *
      rho (MathlibAnnex.CStarAlgebra.AtomicConstruction.sourceHom selectedAtomicRepresentation L
        (transportedFlag family i n - transportedFlag family i (n + 1))) =
      rho (MathlibAnnex.CStarAlgebra.AtomicConstruction.sourceHom selectedAtomicRepresentation L
        ((representativeShellData family i).link n))
  rw [← map_mul, htarget]

/-- In every target Hilbert universe, the represented generator is rebuilt as
the strong sum of the represented completed-CAR shell links plus a precisely
supported limiting defect. -/
theorem exists_targetShellReconstruction
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
    (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
    let sigma := restrictedRepresentation L rho
    let p := transportedFlag family i
    let q := rootFlag
    let w := (representativeShellData family i).link
    let U : ℕ → Submodule ℂ K := fun n ↦ (sigma (p n)).range
    let V : ℕ → Submodule ℂ K := fun n ↦ (sigma (q n)).range
    ∃ S T P Q R : K →L[ℂ] K,
      ContinuousLinearMap.StronglyConverges
        (ContinuousLinearMap.partialSum (fun n ↦ sigma (w n))) atTop S ∧
      ContinuousLinearMap.StronglyConverges
        (ContinuousLinearMap.partialSum (fun n ↦ (sigma (w n))†)) atTop T ∧
      ‖S‖ ≤ 1 ∧ ‖T‖ ≤ 1 ∧ T = S† ∧
      IsStarProjection P ∧ P.range = ⨅ n, U n ∧
      IsStarProjection Q ∧ Q.range = ⨅ n, V n ∧
      (S†).comp S = 1 - P ∧ S.comp (S†) = 1 - Q ∧
      (Unitary.linearIsometryEquiv
        (representedGeneratorUnitary L hLunit rho i) : K ≃ₗᵢ[ℂ] K) =
          S + R ∧
      R = ((Unitary.linearIsometryEquiv
        (representedGeneratorUnitary L hLunit rho i) : K ≃ₗᵢ[ℂ] K) :
          K →L[ℂ] K).comp P ∧
      (R†).comp R = P ∧ R.comp (R†) = Q ∧
      R = (Q.comp R).comp P ∧
      (∀ x, x ∈ ⨅ n, U n ↔
        (Unitary.linearIsometryEquiv
          (representedGeneratorUnitary L hLunit rho i) : K ≃ₗᵢ[ℂ] K) x ∈
            ⨅ n, V n) := by
  dsimp only
  apply exists_represented_unitaryCompletion_of_sourceShells
    (restrictedRepresentation L rho)
    (Unitary.linearIsometryEquiv
      (representedGeneratorUnitary L hLunit rho i))
    (transportedFlag family i) rootFlag
    (representativeShellData family i).link
    (isStarProjection_transportedFlag family i) isStarProjection_rootFlag
    (transportedFlag_zero family i) rootFlag_zero
    (fun _ _ hmn ↦ transportedFlag_mul_of_le family i hmn)
    (fun _ _ hmn ↦ rootFlag_mul_of_le hmn)
    (representativeLink_initial family i)
    (representativeLink_final family i)
    (representedGenerator_comp_sourceShell family L hLunit hLsource rho i)

end MathlibAnnex.CStarAlgebra.CAR
