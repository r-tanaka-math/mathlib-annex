import MathlibAnnex.Analysis.CStarAlgebra.CAR.AtomicSource
import MathlibAnnex.Analysis.CStarAlgebra.Representation.ShellReconstruction

/-!
# The completed CAR atomic shell model

This file discharges the representation-local shell hypotheses of the generic
atomic construction using the actual completed CAR algebra.  The only
remaining input is `KishimotoOzawaSakaiProperty`; in particular, rank-one limiting defects and
capture conclusions are not fields of a source-data structure.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Filter Topology
open scoped ComplexOrder ENNReal lp InnerProduct

namespace MathlibAnnex.CStarAlgebra.CAR

open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.Analysis.InnerProductSpace

/-- The displayed arbitrary-index direct sum of all selected pure GNS
representations of the completed CAR algebra. -/
noncomputable def selectedAtomicRepresentation :
    Representation Limit
      (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState) :=
  atomicRepresentation
    (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState)

/-- The literal root summand is faithful; this is inherited from the actual
completed CAR root GNS representation, not from simplicity of a future
target. -/
theorem selectedRootRepresentation_injective :
    Function.Injective
      (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState
        completedRootPureState.classOf) := by
  exact (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState
    completedRootPureState.classOf).toRingHom.injective

/-- The displayed atomic source representation is faithful because it
contains the faithful literal root summand. -/
theorem selectedAtomicRepresentation_injective :
    Function.Injective selectedAtomicRepresentation := by
  exact atomicRepresentation_injective_of_component
    (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState)
    completedRootPureState.classOf selectedRootRepresentation_injective

/-- The represented initial flag for one selected state. -/
noncomputable def representedInitialFlag (family : RepresentativeShellFamily)
    (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (n : ℕ) :
    Submodule ℂ (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState) :=
  (selectedAtomicRepresentation (transportedFlag family i n)).range

/-- The common represented final (root) flag. -/
noncomputable def representedRootFlag (n : ℕ) :
    Submodule ℂ (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState) :=
  (selectedAtomicRepresentation (rootFlag n)).range

noncomputable instance instHasOrthogonalProjectionRepresentedInitialFlag
    (family : RepresentativeShellFamily) (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (n : ℕ) :
    (representedInitialFlag family i n).HasOrthogonalProjection :=
  (isStarProjection_iff_eq_starProjection_range.mp
    (IsStarProjection.map_representation selectedAtomicRepresentation
      (isStarProjection_transportedFlag family i n))).choose

theorem selectedAtomicRepresentation_transportedFlag_eq_starProjection
    (family : RepresentativeShellFamily) (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (n : ℕ) :
    selectedAtomicRepresentation (transportedFlag family i n) =
      (representedInitialFlag family i n).starProjection :=
  (isStarProjection_iff_eq_starProjection_range.mp
    (IsStarProjection.map_representation selectedAtomicRepresentation
      (isStarProjection_transportedFlag family i n))).choose_spec

noncomputable instance instHasOrthogonalProjectionRepresentedRootFlag (n : ℕ) :
    (representedRootFlag n).HasOrthogonalProjection :=
  (isStarProjection_iff_eq_starProjection_range.mp
    (IsStarProjection.map_representation selectedAtomicRepresentation
      (isStarProjection_rootFlag n))).choose

theorem selectedAtomicRepresentation_rootFlag_eq_starProjection (n : ℕ) :
    selectedAtomicRepresentation (rootFlag n) =
      (representedRootFlag n).starProjection :=
  (isStarProjection_iff_eq_starProjection_range.mp
    (IsStarProjection.map_representation selectedAtomicRepresentation
      (isStarProjection_rootFlag n))).choose_spec

/-- A named final flag family.  Its state index is deliberately retained so
the generic arbitrary-index construction can use it without changing the
common completed-CAR root flag. -/
noncomputable def representedFinalFlag (_family : RepresentativeShellFamily)
    (_i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (n : ℕ) :
    Submodule ℂ (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState) :=
  representedRootFlag n

noncomputable instance instHasOrthogonalProjectionRepresentedFinalFlag
    (family : RepresentativeShellFamily) (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (n : ℕ) :
    (representedFinalFlag family i n).HasOrthogonalProjection := by
  change (representedRootFlag n).HasOrthogonalProjection
  infer_instance

noncomputable instance instHasOrthogonalProjectionIInfRepresentedInitialFlag
    (family : RepresentativeShellFamily) (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
    (⨅ n, representedInitialFlag family i n).HasOrthogonalProjection := by
  have hspan :
      (⨅ n, representedInitialFlag family i n) =
        ℂ ∙ MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState i
          (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i) := by
    simpa [representedInitialFlag, selectedAtomicRepresentation] using
      (iInf_range_atomic_transportedFlag_eq_span family i)
  rw [hspan]
  infer_instance

noncomputable instance instHasOrthogonalProjectionIInfRepresentedFinalFlag
    (family : RepresentativeShellFamily) (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
    (⨅ n, representedFinalFlag family i n).HasOrthogonalProjection := by
  have hspan :
      (⨅ n, representedFinalFlag family i n) =
        ℂ ∙ MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState
          completedRootPureState.classOf
          (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState
            completedRootPureState.classOf) := by
    simpa [representedFinalFlag, representedRootFlag,
      selectedAtomicRepresentation] using
      (iInf_range_atomic_transportedFlag_eq_span family
        completedRootPureState.classOf)
  rw [hspan]
  infer_instance

/-- The represented algebraic link between one transported difference shell
and the corresponding root difference shell. -/
noncomputable def representedShellLink (family : RepresentativeShellFamily)
    (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (n : ℕ) :
    MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
      MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState :=
  selectedAtomicRepresentation ((representativeShellData family i).link n)

/-- Actual completed-CAR source data produces a faithful irreducible concrete
atomic model.  All projection flags, support identities, and rank-one limiting
defects are supplied by proved CAR/GNS facts.  At the distinguished root the
constructed generator is proved to be the identity from its action on every
difference shell and on the rank-one limiting defect. -/
theorem exists_completedAtomicShellModel (family : RepresentativeShellFamily) :
    ∃ L : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit →
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
          MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState,
      (∀ i, L i ∈ unitary
        (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
          MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState)) ∧
      (∀ i, L i (MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState i
          (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i)) =
        MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState
          completedRootPureState.classOf
          (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState
            completedRootPureState.classOf)) ∧
      (∀ i n, (L i).comp (selectedAtomicRepresentation
          (transportedFlag family i n - transportedFlag family i (n + 1))) =
        representedShellLink family i n) ∧
      L completedRootPureState.classOf = 1 ∧
      Function.Injective
        (MathlibAnnex.CStarAlgebra.AtomicConstruction.sourceHom selectedAtomicRepresentation L) ∧
      Representation.IsIrreducible
        (MathlibAnnex.CStarAlgebra.AtomicConstruction.ambientInclusion selectedAtomicRepresentation L) := by
  classical
  let U := representedInitialFlag family
  let V := representedFinalFlag family
  let W := representedShellLink family
  have hUproj (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (n : ℕ) :
      selectedAtomicRepresentation (transportedFlag family i n) =
        (U i n).starProjection := by
    exact selectedAtomicRepresentation_transportedFlag_eq_starProjection family i n
  have hVproj (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (n : ℕ) :
      selectedAtomicRepresentation (rootFlag n) = (V i n).starProjection :=
    by simpa [V, representedFinalFlag] using
      selectedAtomicRepresentation_rootFlag_eq_starProjection n
  have hUspan (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
      (⨅ n, U i n) =
        ℂ ∙ MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState i
          (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i) := by
    simpa [U, representedInitialFlag, selectedAtomicRepresentation] using
      (iInf_range_atomic_transportedFlag_eq_span family i)
  have hVspan (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
      (⨅ n, V i n) =
        ℂ ∙ MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState
          completedRootPureState.classOf
          (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState
            completedRootPureState.classOf) := by
    simpa [V, representedFinalFlag, representedRootFlag,
      selectedAtomicRepresentation] using
      (iInf_range_atomic_transportedFlag_eq_span family
        completedRootPureState.classOf)
  have hU : ∀ i, Antitone (U i) := by
    intro i m n hmn
    rintro x ⟨y, rfl⟩
    refine ⟨selectedAtomicRepresentation (transportedFlag family i n) y, ?_⟩
    have heq :
        selectedAtomicRepresentation (transportedFlag family i m) *
            selectedAtomicRepresentation (transportedFlag family i n) =
          selectedAtomicRepresentation (transportedFlag family i n) := by
      rw [← map_mul, transportedFlag_mul_of_le family i hmn]
    exact congrArg
      (fun T : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState ↦ T y) heq
  have hV : ∀ i, Antitone (V i) := by
    intro i m n hmn
    rintro x ⟨y, rfl⟩
    refine ⟨selectedAtomicRepresentation (rootFlag n) y, ?_⟩
    have heq : selectedAtomicRepresentation (rootFlag m) *
        selectedAtomicRepresentation (rootFlag n) =
          selectedAtomicRepresentation (rootFlag n) := by
      rw [← map_mul, rootFlag_mul_of_le hmn]
    exact congrArg
      (fun T : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState ↦ T y) heq
  have hU0 : ∀ i, U i 0 = ⊤ := by
    intro i
    rw [← Submodule.range_starProjection (U i 0), ← hUproj i 0,
      transportedFlag_zero, map_one]
    exact LinearMap.range_eq_top.mpr fun x ↦ ⟨x, rfl⟩
  have hV0 : ∀ i, V i 0 = ⊤ := by
    intro i
    rw [← Submodule.range_starProjection (V i 0), ← hVproj i 0,
      rootFlag_zero, map_one]
    exact LinearMap.range_eq_top.mpr fun x ↦ ⟨x, rfl⟩
  have hInitial : ∀ i n, ((W i n)†).comp (W i n) =
      Submodule.projectionShell (U i) n := by
    intro i n
    change star (selectedAtomicRepresentation
        ((representativeShellData family i).link n)) *
        selectedAtomicRepresentation ((representativeShellData family i).link n) = _
    rw [← map_star, ← map_mul, representativeLink_initial, map_sub,
      hUproj i n, hUproj i (n + 1)]
    rfl
  have hFinal : ∀ i n, (W i n).comp ((W i n)†) =
      Submodule.projectionShell (V i) n := by
    intro i n
    change selectedAtomicRepresentation
        ((representativeShellData family i).link n) *
        star (selectedAtomicRepresentation
          ((representativeShellData family i).link n)) = _
    rw [← map_star, ← map_mul, representativeLink_final, map_sub,
      hVproj i n, hVproj i (n + 1)]
    rfl
  have hUShell : ∀ i n,
      selectedAtomicRepresentation
          (transportedFlag family i n - transportedFlag family i (n + 1)) =
        Submodule.projectionShell (U i) n := by
    intro i n
    rw [map_sub, hUproj i n, hUproj i (n + 1)]
    rfl
  have hUinf : ∀ i, (⨅ n, U i n).starProjection =
      InnerProductSpace.rankOne ℂ
        (MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState i
          (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i))
        (MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState i
          (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i)) := by
    intro i
    apply starProjection_eq_rankOne_of_eq_span
      (⨅ n, U i n)
      (MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState i
        (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i))
    simpa [MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding, norm_coordinateEmbedding] using
      MathlibAnnex.CStarAlgebra.PureState.norm_selectedVector completedRootPureState i
    exact hUspan i
  have hVinf : ∀ i, (⨅ n, V i n).starProjection =
      InnerProductSpace.rankOne ℂ
        (MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState
          completedRootPureState.classOf
          (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState
            completedRootPureState.classOf))
        (MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState
          completedRootPureState.classOf
          (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState
            completedRootPureState.classOf)) := by
    intro i
    apply starProjection_eq_rankOne_of_eq_span
      (⨅ n, V i n)
      (MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState
        completedRootPureState.classOf
        (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState
          completedRootPureState.classOf))
    simpa [MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding, norm_coordinateEmbedding] using
      MathlibAnnex.CStarAlgebra.PureState.norm_selectedVector completedRootPureState
        completedRootPureState.classOf
    exact hVspan i
  obtain ⟨L, hLunit, hLmap, hLterm, hLirr⟩ :=
    MathlibAnnex.CStarAlgebra.AtomicConstruction.exists_irreducible_pureAtomicShellModel
      completedRootPureState W U V hU hV hU0 hV0 hInitial hFinal hUinf hVinf
  have hLsource (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (n : ℕ) :
      (L i).comp (selectedAtomicRepresentation
          (transportedFlag family i n - transportedFlag family i (n + 1))) =
        representedShellLink family i n := by
    rw [hUShell i n]
    exact hLterm i n
  have hRootShell (n : ℕ) :
      representedShellLink family completedRootPureState.classOf n =
        Submodule.projectionShell (U completedRootPureState.classOf) n := by
    rw [Submodule.projectionShell, ← hUproj, ← hUproj]
    simp [W, U, representedShellLink, rootShell, map_sub]
  have hLroot : L completedRootPureState.classOf = 1 := by
    apply ContinuousLinearMap.eq_one_of_comp_projectionShell_eq_self_of_rankOne_iInf
      (L completedRootPureState.classOf) (U completedRootPureState.classOf)
      (hU completedRootPureState.classOf) (hU0 completedRootPureState.classOf)
      (MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState
        completedRootPureState.classOf
        (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState
          completedRootPureState.classOf))
    · simpa [MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding, norm_coordinateEmbedding] using
        MathlibAnnex.CStarAlgebra.PureState.norm_selectedVector completedRootPureState
          completedRootPureState.classOf
    · exact hUinf completedRootPureState.classOf
    · intro n
      rw [hLterm]
      change representedShellLink family completedRootPureState.classOf n =
        Submodule.projectionShell (U completedRootPureState.classOf) n
      exact hRootShell n
    · exact hLmap completedRootPureState.classOf
  exact ⟨L, hLunit, hLmap, hLsource, hLroot,
    MathlibAnnex.CStarAlgebra.AtomicConstruction.sourceHom_injective selectedAtomicRepresentation L
      selectedAtomicRepresentation_injective,
    hLirr⟩

end MathlibAnnex.CStarAlgebra.CAR
