import MathlibAnnex.Analysis.CStarAlgebra.CAR.CyclicCapture
import MathlibAnnex.Analysis.CStarAlgebra.AtomicConstruction.GeneratedReduction
import MathlibAnnex.Analysis.InnerProductSpace.Reduction

/-!
# Surjectivity of the selected cyclic sum in an irreducible target

The selected pure-state cyclic pieces form a closed source-reducing subspace.
The represented completed-CAR shell reconstruction shows that this subspace
also reduces every additional target generator: the strong shell part reduces
it termwise, while the limiting corner is controlled by its initial and root
one-dimensional fixed lines.  Irreducibility of the arbitrary target
representation then forces the cyclic sum to be the whole target Hilbert
space.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Filter Topology
open scoped ComplexOrder ENNReal lp InnerProduct

namespace MathlibAnnex.CStarAlgebra.CAR

open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.Analysis.InnerProductSpace

universe v

/-- The arbitrary-index sum of the selected pure GNS cyclic copies is
surjective in every nonzero irreducible representation of the actual target.
The returned map still records its source intertwining law and its action on
all selected cyclic vectors. -/
theorem exists_surjective_selectedAtomicCyclicIsometry
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
    (hLroot : L completedRootPureState.classOf = 1)
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (rho : Representation (AtomicTarget L) K)
    (hrho : rho.IsIrreducible) :
    ∃ (eta_o : K) (eta : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit → K)
      (W : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →ₗᵢ[ℂ] K),
      Function.Surjective W ∧
      ‖eta_o‖ = 1 ∧
      (∀ i, ‖eta i‖ = 1) ∧
      (∀ i, W (MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState i
        (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i)) = eta i) ∧
      (∀ i, (Unitary.linearIsometryEquiv
        (representedGeneratorUnitary L hLunit rho i) : K ≃ₗᵢ[ℂ] K)
          (eta i) = eta_o) ∧
      ∀ a,
        W.toContinuousLinearMap.comp (selectedAtomicRepresentation a) =
          ((restrictedRepresentation L rho) a).comp
            W.toContinuousLinearMap := by
  classical
  let sigma := restrictedRepresentation L rho
  obtain ⟨eta_o, eta, heta_o_norm, heta_o_fixed, heta_o_state, heta⟩ :=
    exists_targetDefectVectorFamily family L hLunit hLsource rho hrho
  have heta_norm : ∀ i, ‖eta i‖ = 1 := fun i ↦ (heta i).1
  have heta_state : ∀ i, Representation.vectorFunctional sigma (eta i) =
      (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1 :=
    fun i ↦ (heta i).2.2.2
  have heta_gen : ∀ i, (Unitary.linearIsometryEquiv
      (representedGeneratorUnitary L hLunit rho i) : K ≃ₗᵢ[ℂ] K)
        (eta i) = eta_o := fun i ↦ (heta i).2.2.1
  obtain ⟨W, hWcyclic, hWpoint, hWfixedSpan, hWsource⟩ :=
    exists_selectedAtomicCyclicIsometry family sigma eta heta_norm heta_state
  let M : Submodule ℂ K := LinearMap.range W.toLinearMap
  have hMclosed : IsClosed (M : Set K) := by
    change IsClosed (Set.range W)
    exact W.isometry.isClosedEmbedding.isClosed_range
  have hsourceReduces (a : Limit) : M.Reduces (sigma a) := by
    constructor
    · rintro _ ⟨x, rfl⟩
      refine ⟨selectedAtomicRepresentation a x, ?_⟩
      have h := congrArg
        (fun T : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K ↦
          T x) (hWsource a)
      simpa [ContinuousLinearMap.comp_apply] using h
    · rintro _ ⟨x, rfl⟩
      refine ⟨selectedAtomicRepresentation (star a) x, ?_⟩
      have h := congrArg
        (fun T : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K ↦
          T x) (hWsource (star a))
      simpa [ContinuousLinearMap.comp_apply, map_star,
        ContinuousLinearMap.star_eq_adjoint] using h
  have htargetRoot : MathlibAnnex.CStarAlgebra.AtomicConstruction.generator selectedAtomicRepresentation L
        completedRootPureState.classOf =
      MathlibAnnex.CStarAlgebra.AtomicConstruction.sourceHom selectedAtomicRepresentation L 1 := by
    apply Subtype.ext
    simpa using hLroot
  have hrootGenerator :
      ((Unitary.linearIsometryEquiv
        (representedGeneratorUnitary L hLunit rho
          completedRootPureState.classOf) : K ≃ₗᵢ[ℂ] K) : K →L[ℂ] K) = 1 := by
    change rho (MathlibAnnex.CStarAlgebra.AtomicConstruction.generator selectedAtomicRepresentation L
      completedRootPureState.classOf) = 1
    rw [htargetRoot, map_one]
    exact map_one rho
  have heta_root : eta completedRootPureState.classOf = eta_o := by
    have h := heta_gen completedRootPureState.classOf
    change (((Unitary.linearIsometryEquiv
      (representedGeneratorUnitary L hLunit rho
        completedRootPureState.classOf) : K ≃ₗᵢ[ℂ] K) : K →L[ℂ] K)
          (eta completedRootPureState.classOf)) = eta_o at h
    rw [hrootGenerator] at h
    simpa using h
  have hline_mem (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) {y : K}
      (hy : y ∈ (ℂ ∙ eta i : Submodule ℂ K)) : y ∈ M := by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
    refine ⟨c • MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState i
      (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i), ?_⟩
    change W (c • MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState i
      (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i)) = y
    rw [map_smul, hWpoint]
    exact hc
  have hgeneratorReduces (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
      M.Reduces (rho (MathlibAnnex.CStarAlgebra.AtomicConstruction.generator selectedAtomicRepresentation L i)) := by
    obtain ⟨S, T, P, Q, R, hS, hT, -, -, hAdj, hPproj, hPrange,
        hQproj, hQrange, -, -, hgeneratorEq, hR, hRinitial, hRfinal,
        hRsupport, -⟩ :=
      exists_targetShellReconstruction family L hLunit hLsource rho i
    have hSreduces : M.Reduces S := by
      apply Submodule.Reduces.of_stronglyConverges_partialSum hMclosed
        (W := fun n ↦ sigma ((representativeShellData family i).link n))
        (T := T)
      · intro n
        exact hsourceReduces ((representativeShellData family i).link n)
      · exact hS
      · exact hT
      · exact hAdj
    have hPeq : P = commonFixedProjection
        (fun n ↦ sigma (transportedFlag family i n)) := by
      exact starProjection_eq_commonFixedProjection_of_range_iInf sigma
        (transportedFlag family i) (isStarProjection_transportedFlag family i)
        P hPproj hPrange
    have hQeq : Q = commonFixedProjection
        (fun n ↦ sigma (rootFlag n)) := by
      exact starProjection_eq_commonFixedProjection_of_range_iInf sigma
        rootFlag isStarProjection_rootFlag Q hQproj hQrange
    have hPinv : M.IsInvariantUnder P := by
      rintro _ ⟨x, rfl⟩
      rw [hPeq]
      exact hline_mem i (hWfixedSpan i x)
    have hQinv : M.IsInvariantUnder Q := by
      rintro _ ⟨x, rfl⟩
      rw [hQeq]
      have hspan : commonFixedProjection (fun n ↦ sigma (rootFlag n)) (W x) ∈
          (ℂ ∙ eta completedRootPureState.classOf : Submodule ℂ K) := by
        simpa using hWfixedSpan completedRootPureState.classOf x
      rw [heta_root] at hspan
      exact hline_mem completedRootPureState.classOf (by simpa [heta_root] using hspan)
    have hPfix (n : ℕ) : sigma (transportedFlag family i n) (eta i) = eta i :=
      (heta i).2.1 n
    have hPeta : P (eta i) = eta i := by
      rw [hPeq]
      exact (commonFixedProjection_eq_self_iff _ _).2
        ((mem_commonFixedSubspace_iff _ _).2 hPfix)
    have hQeta : Q eta_o = eta_o := by
      rw [hQeq]
      exact (commonFixedProjection_eq_self_iff _ _).2
        ((mem_commonFixedSubspace_iff _ _).2 heta_o_fixed)
    have hReta : R (eta i) = eta_o := by
      rw [hR]
      change (Unitary.linearIsometryEquiv
        (representedGeneratorUnitary L hLunit rho i) : K ≃ₗᵢ[ℂ] K)
          (P (eta i)) = eta_o
      rw [hPeta]
      exact heta_gen i
    have hRadjeta : (R†) eta_o = eta i := by
      have h := congrArg (fun A : K →L[ℂ] K ↦ A (eta i)) hRinitial
      change (R†) (R (eta i)) = P (eta i) at h
      simpa [hReta, hPeta] using h
    have hRinv : M.IsInvariantUnder R := by
      rintro _ ⟨x, rfl⟩
      change R (W x) ∈ M
      rw [hR, ContinuousLinearMap.comp_apply, hPeq]
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hWfixedSpan i x)
      have hgen_i :
          (((Unitary.linearIsometryEquiv
            (representedGeneratorUnitary L hLunit rho i) : K ≃ₗᵢ[ℂ] K) :
              K →L[ℂ] K) (eta i)) = eta_o := heta_gen i
      rw [← hc, map_smul, hgen_i]
      have hrootMem : eta_o ∈ M := by
        rw [← heta_root]
        exact hline_mem completedRootPureState.classOf
          (Submodule.mem_span_singleton_self _)
      exact M.smul_mem c hrootMem
    have hRadjSupport : R† = (P.comp (R†)).comp Q := by
      have h := congrArg (fun A : K →L[ℂ] K ↦ A†) hRsupport
      have hPadj : P† = P := by
        simpa [ContinuousLinearMap.star_eq_adjoint] using
          hPproj.isSelfAdjoint.star_eq
      have hQadj : Q† = Q := by
        simpa [ContinuousLinearMap.star_eq_adjoint] using
          hQproj.isSelfAdjoint.star_eq
      have h' : R† = P.comp ((R†).comp Q) := by
        simpa [ContinuousLinearMap.adjoint_comp, hPadj, hQadj] using h
      exact h'.trans (ContinuousLinearMap.comp_assoc P (R†) Q).symm
    have hRadjinv : M.IsInvariantUnder (R†) := by
      rintro _ ⟨x, rfl⟩
      change (R†) (W x) ∈ M
      rw [hRadjSupport, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.comp_apply, hQeq]
      have hspan : commonFixedProjection (fun n ↦ sigma (rootFlag n)) (W x) ∈
          (ℂ ∙ eta completedRootPureState.classOf : Submodule ℂ K) := by
        simpa using hWfixedSpan completedRootPureState.classOf x
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
      rw [heta_root] at hc
      rw [← hc, map_smul, hRadjeta, map_smul, hPeta]
      exact hline_mem i (Submodule.smul_mem _ c
        (Submodule.mem_span_singleton_self (eta i)))
    have hRreduces : M.Reduces R := ⟨hRinv, hRadjinv⟩
    have hsumReduces : M.Reduces (S + R) := by
      constructor
      · intro x hx
        exact M.add_mem (hSreduces.1 hx) (hRreduces.1 hx)
      · intro x hx
        have hadd := M.add_mem (hSreduces.2 hx) (hRreduces.2 hx)
        simpa only [map_add ContinuousLinearMap.adjoint, add_apply] using hadd
    change M.Reduces
      (((representedGeneratorUnitary L hLunit rho i : unitary (K →L[ℂ] K)) :
        K →L[ℂ] K))
    rw [show (((representedGeneratorUnitary L hLunit rho i :
      unitary (K →L[ℂ] K)) : K →L[ℂ] K)) = S + R by
        simpa using hgeneratorEq]
    exact hsumReduces
  have hall : ∀ x : AtomicTarget L, M.Reduces (rho x) :=
    MathlibAnnex.CStarAlgebra.AtomicConstruction.reduces_concreteTarget_of_generators
      selectedAtomicRepresentation L rho M hMclosed
      (fun a ↦ hsourceReduces a) hgeneratorReduces
  have hMrepresentation : rho.Reduces M := by
    refine ⟨hMclosed, ?_⟩
    intro a x hx
    exact ⟨(hall a).1 hx, (hall a).2 hx⟩
  have hMne : M ≠ ⊥ := by
    intro hbot
    have hmem : eta_o ∈ M := by
      rw [← heta_root]
      exact hline_mem completedRootPureState.classOf
        (Submodule.mem_span_singleton_self _)
    rw [hbot, Submodule.mem_bot] at hmem
    have hnorm := congrArg norm hmem
    simpa [heta_o_norm] using hnorm
  have hMtop : M = ⊤ := (hrho.2 M hMrepresentation).resolve_left hMne
  have hWsurj : Function.Surjective W := by
    intro y
    have hy : y ∈ M := by rw [hMtop]; exact Submodule.mem_top
    exact hy
  exact ⟨eta_o, eta, W, hWsurj, heta_o_norm, heta_norm, hWpoint,
    heta_gen, hWsource⟩

/-- Consequently, the actual completed-CAR source restriction of every
irreducible target representation is unitarily equivalent to the displayed
arbitrary-index selected pure-GNS sum. -/
theorem selectedAtomicRepresentation_unitaryEquivalent_restricted
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
    (hLroot : L completedRootPureState.classOf = 1)
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (rho : Representation (AtomicTarget L) K)
    (hrho : rho.IsIrreducible) :
    selectedAtomicRepresentation.UnitaryEquivalent
      (restrictedRepresentation L rho) := by
  obtain ⟨eta_o, eta, W, hWsurj, -, -, -, -, hW⟩ :=
    exists_surjective_selectedAtomicCyclicIsometry
      family L hLunit hLsource hLroot rho hrho
  let E : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState ≃ₗᵢ[ℂ] K :=
    LinearIsometryEquiv.ofSurjective W hWsurj
  refine ⟨E, ?_⟩
  intro a x
  have h := congrArg
    (fun T : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K ↦
      T x) (hW a)
  simpa [E, ContinuousLinearMap.comp_apply] using h

end MathlibAnnex.CStarAlgebra.CAR
