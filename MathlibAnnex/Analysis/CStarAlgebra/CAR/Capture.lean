import MathlibAnnex.Analysis.CStarAlgebra.CAR.CaptureRange

/-!
# Full target capture

The surjective cyclic-sum isometry also intertwines the additional target
generators.  The proof compares the two independently constructed strong
shell sums and then identifies the remaining rank-one corner from the
selected-vector transport.  No arbitrary representation is asked to preserve
the source strong-operator limits.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

open Filter Topology
open scoped ComplexOrder ENNReal lp InnerProduct

namespace MathlibAnnex.CStarAlgebra.CAR

open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.Analysis.InnerProductSpace

universe v

/-- The displayed actual completed-CAR atomic target captures every
irreducible representation on an arbitrary target Hilbert universe. -/
theorem ambientInclusion_unitaryEquivalent
    (family : RepresentativeShellFamily)
    (L : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit →
      MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState)
    (hLunit : ∀ i, L i ∈ unitary
      (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState))
    (hLmap : ∀ i, L i
      (MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState i
        (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i)) =
      MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState
        completedRootPureState.classOf
        (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState
          completedRootPureState.classOf))
    (hLsource : ∀ i n, (L i).comp (selectedAtomicRepresentation
      (transportedFlag family i n - transportedFlag family i (n + 1))) =
        representedShellLink family i n)
    (hLroot : L completedRootPureState.classOf = 1)
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (rho : Representation (AtomicTarget L) K)
    (hrho : rho.IsIrreducible) :
    (MathlibAnnex.CStarAlgebra.AtomicConstruction.ambientInclusion selectedAtomicRepresentation L).UnitaryEquivalent
      rho := by
  classical
  let sigma := restrictedRepresentation L rho
  obtain ⟨eta_o, eta, W, hWsurj, heta_o_norm, heta_norm, hWpoint,
      heta_gen, hWsource⟩ :=
    exists_surjective_selectedAtomicCyclicIsometry
      family L hLunit hLsource hLroot rho hrho
  let E : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState ≃ₗᵢ[ℂ] K :=
    LinearIsometryEquiv.ofSurjective W hWsurj
  have hEsource (a : Limit) :
      (E : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K).comp
          (selectedAtomicRepresentation a) =
        (sigma a).comp
          (E : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K) := by
    change W.toContinuousLinearMap.comp (selectedAtomicRepresentation a) =
      (restrictedRepresentation L rho a).comp W.toContinuousLinearMap
    exact hWsource a
  have hEpoint (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
      E (MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState i
        (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i)) = eta i := by
    simpa [E] using hWpoint i
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
  refine ⟨E, ?_⟩
  intro a
  have hsourceGenerator (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (x :
      MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState) :
      E (L i x) =
        rho (MathlibAnnex.CStarAlgebra.AtomicConstruction.generator selectedAtomicRepresentation L i) (E x) := by
    let rho₀ := MathlibAnnex.CStarAlgebra.AtomicConstruction.ambientInclusion selectedAtomicRepresentation L
    let w := (representativeShellData family i).link
    obtain ⟨S₀, T₀, P₀, Q₀, R₀, hS₀, hT₀, -, -, hAdj₀,
        hP₀proj, hP₀range, hQ₀proj, hQ₀range, -, -, hgenerator₀,
        hR₀, -, -, -, -⟩ :=
      exists_targetShellReconstruction family L hLunit hLsource rho₀ i
    obtain ⟨S, T, P, Q, R, hS, hT, -, -, hAdj,
        hPproj, hPrange, hQproj, hQrange, -, -, hgenerator,
        hR, -, -, -, -⟩ :=
      exists_targetShellReconstruction family L hLunit hLsource rho i
    have hrepresented₀ :
        (((Unitary.linearIsometryEquiv
          (representedGeneratorUnitary L hLunit rho₀ i) :
            MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState ≃ₗᵢ[ℂ]
              MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState) :
          MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
            MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState)) = L i := by
      rfl
    rw [hrepresented₀] at hgenerator₀ hR₀
    have hS₀' : ContinuousLinearMap.StronglyConverges
        (ContinuousLinearMap.partialSum
          (fun n ↦ selectedAtomicRepresentation (w n))) atTop S₀ := by
      change ContinuousLinearMap.StronglyConverges
        (ContinuousLinearMap.partialSum
          (fun n ↦ selectedAtomicRepresentation
            ((representativeShellData family i).link n))) atTop S₀ at hS₀
      simpa [w] using hS₀
    have hS' : ContinuousLinearMap.StronglyConverges
        (ContinuousLinearMap.partialSum (fun n ↦ sigma (w n))) atTop S := by
      simpa [w] using hS
    have hpartial (N : ℕ) :
        (E : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K).comp
            (ContinuousLinearMap.partialSum
              (fun n ↦ selectedAtomicRepresentation (w n)) N) =
          (ContinuousLinearMap.partialSum (fun n ↦ sigma (w n)) N).comp
            (E : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K) := by
      apply ContinuousLinearMap.ext
      intro y
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.partialSum_apply,
        ContinuousLinearMap.partialSum_apply, map_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have h := congrArg
        (fun A : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K ↦
          A y) (hEsource (w n))
      simpa [ContinuousLinearMap.comp_apply] using h
    have hSintertwines :
        (E : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K).comp S₀ =
        S.comp (E : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K) :=
      ContinuousLinearMap.intertwines_strongLimits
        (E : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K)
        (E : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K)
        hS₀' hS' hpartial
    have hP₀range' : P₀.range =
        ⨅ n, (selectedAtomicRepresentation (transportedFlag family i n)).range := by
      change P₀.range =
        ⨅ n, (selectedAtomicRepresentation (transportedFlag family i n)).range at hP₀range
      exact hP₀range
    have hP₀eq : P₀ = commonFixedProjection
        (fun n ↦ selectedAtomicRepresentation (transportedFlag family i n)) := by
      exact starProjection_eq_commonFixedProjection_of_range_iInf
        selectedAtomicRepresentation (transportedFlag family i)
        (isStarProjection_transportedFlag family i) P₀ hP₀proj hP₀range'
    have hPeq : P = commonFixedProjection
        (fun n ↦ sigma (transportedFlag family i n)) := by
      exact starProjection_eq_commonFixedProjection_of_range_iInf sigma
        (transportedFlag family i) (isStarProjection_transportedFlag family i)
        P hPproj hPrange
    let F₀ : Submodule ℂ
        (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState) :=
      commonFixedSubspace
        (fun n ↦ selectedAtomicRepresentation (transportedFlag family i n))
    let F : Submodule ℂ K :=
      commonFixedSubspace (fun n ↦ sigma (transportedFlag family i n))
    have hFmap : F₀.map (E.toLinearEquiv :
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →ₗ[ℂ] K) = F := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        change z ∈ commonFixedSubspace
          (fun n ↦ selectedAtomicRepresentation (transportedFlag family i n)) at hz
        rw [mem_commonFixedSubspace_iff] at hz
        change E z ∈ commonFixedSubspace
          (fun n ↦ sigma (transportedFlag family i n))
        rw [mem_commonFixedSubspace_iff]
        intro n
        have h := congrArg
          (fun A : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K ↦
            A z) (hEsource (transportedFlag family i n))
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
          hz n] at h
        exact h.symm
      · intro hy
        change y ∈ commonFixedSubspace
          (fun n ↦ sigma (transportedFlag family i n)) at hy
        rw [mem_commonFixedSubspace_iff] at hy
        refine ⟨E.symm y, ?_, E.apply_symm_apply y⟩
        change E.symm y ∈ commonFixedSubspace
          (fun n ↦ selectedAtomicRepresentation (transportedFlag family i n))
        rw [mem_commonFixedSubspace_iff]
        intro n
        apply E.injective
        have h := congrArg
          (fun A : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K ↦
            A (E.symm y)) (hEsource (transportedFlag family i n))
        change E (selectedAtomicRepresentation (transportedFlag family i n)
          (E.symm y)) = sigma (transportedFlag family i n) (E (E.symm y)) at h
        calc
          E (selectedAtomicRepresentation (transportedFlag family i n) (E.symm y)) =
              sigma (transportedFlag family i n) (E (E.symm y)) := h
          _ = sigma (transportedFlag family i n) y := by rw [E.apply_symm_apply]
          _ = y := hy n
          _ = E (E.symm y) := (E.apply_symm_apply y).symm
    have hPintertwines :
        (E : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K).comp P₀ =
        P.comp (E : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K) := by
      apply ContinuousLinearMap.ext
      intro y
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        hP₀eq, hPeq]
      change E (F₀.starProjection y) = F.starProjection (E y)
      symm
      apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      · rw [← hFmap]
        exact ⟨F₀.starProjection y,
          Submodule.starProjection_apply_mem F₀ y, rfl⟩
      · intro z hz
        rw [← hFmap] at hz
        obtain ⟨z₀, hz₀, rfl⟩ := hz
        rw [← E.map_sub]
        change inner ℂ (E (y - F₀.starProjection y)) (E z₀) = 0
        rw [E.inner_map_map]
        exact F₀.starProjection_inner_eq_zero y z₀ hz₀
    have hF₀span : F₀ =
        ℂ ∙ MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState i
          (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i) := by
      rw [show F₀ = ⨅ n,
        (selectedAtomicRepresentation (transportedFlag family i n)).range by
          exact commonFixedSubspace_eq_iInf_range selectedAtomicRepresentation
            (transportedFlag family i) (isStarProjection_transportedFlag family i)]
      simpa [selectedAtomicRepresentation] using
        iInf_range_atomic_transportedFlag_eq_span family i
    have hRintertwines :
        (E : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K).comp R₀ =
        R.comp (E : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K) := by
      apply ContinuousLinearMap.ext
      intro y
      have hPmem : P₀ y ∈ F₀ := by
        rw [hP₀eq]
        exact commonFixedProjection_mem _ _
      rw [hF₀span] at hPmem
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hPmem
      have hleft : E (R₀ y) = c • eta_o := by
        rw [hR₀, ContinuousLinearMap.comp_apply, ← hc, map_smul,
          hLmap, map_smul, hEpoint, heta_root]
      have hPpoint : P (E y) = c • eta i := by
        have h := congrArg
          (fun A : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K ↦
            A y) hPintertwines
        change E (P₀ y) = P (E y) at h
        rw [← hc, map_smul, hEpoint] at h
        exact h.symm
      have hright : R (E y) = c • eta_o := by
        rw [hR, ContinuousLinearMap.comp_apply, hPpoint, map_smul]
        have hgen_i :
            (((Unitary.linearIsometryEquiv
              (representedGeneratorUnitary L hLunit rho i) : K ≃ₗᵢ[ℂ] K) :
                K →L[ℂ] K) (eta i)) = eta_o := heta_gen i
        rw [hgen_i]
      exact hleft.trans hright.symm
    have hsourceDecomp : L i = S₀ + R₀ := by
      simpa [rho₀] using hgenerator₀
    have htargetDecomp :
        rho (MathlibAnnex.CStarAlgebra.AtomicConstruction.generator selectedAtomicRepresentation L i) = S + R := by
      simpa using hgenerator
    have hSpoint : E (S₀ x) = S (E x) := by
      have h := congrArg
        (fun A : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K ↦
          A x) hSintertwines
      simpa [ContinuousLinearMap.comp_apply] using h
    have hRpoint : E (R₀ x) = R (E x) := by
      have h := congrArg
        (fun A : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K ↦
          A x) hRintertwines
      simpa [ContinuousLinearMap.comp_apply] using h
    calc
      E (L i x) = E ((S₀ + R₀) x) := by rw [hsourceDecomp]
      _ = E (S₀ x) + E (R₀ x) := by simp
      _ = S (E x) + R (E x) := by rw [hSpoint, hRpoint]
      _ = (S + R) (E x) := rfl
      _ = rho (MathlibAnnex.CStarAlgebra.AtomicConstruction.generator selectedAtomicRepresentation L i) (E x) := by
        rw [htargetDecomp]
  have hgeneratorAll (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
      (E : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K).comp
          (L i) =
        (rho (MathlibAnnex.CStarAlgebra.AtomicConstruction.generator selectedAtomicRepresentation L i)).comp
          (E : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K) := by
    apply ContinuousLinearMap.ext
    intro x
    exact hsourceGenerator i x
  have hall := MathlibAnnex.CStarAlgebra.AtomicConstruction.intertwines_concreteTarget_of_generators
    selectedAtomicRepresentation L E rho hEsource hgeneratorAll a
  intro x
  have h := congrArg
    (fun A : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ] K ↦
      A x) hall
  change E ((MathlibAnnex.CStarAlgebra.AtomicConstruction.ambientInclusion selectedAtomicRepresentation L a) x) =
    rho a (E x) at h
  exact h

/-- Ordinary conditional endpoint: the actual completed-CAR construction
removes every representation-local shell, defect, and capture hypothesis.
Only the explicitly parameterized KOS statement remains. -/
theorem exists_completedAtomicTarget_uniqueIrreducibleModel
    (family : RepresentativeShellFamily) :
    ∃ L : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit →
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
          MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState,
      Representation.IsUniqueIrreducibleModel
        (MathlibAnnex.CStarAlgebra.AtomicConstruction.ambientInclusion selectedAtomicRepresentation L) := by
  obtain ⟨L, hLunit, hLmap, hLsource, hLroot, hsourceFaithful, hambientIrr⟩ :=
    exists_completedAtomicShellModel family
  refine ⟨L, ?_, hambientIrr, ?_⟩
  · exact MathlibAnnex.CStarAlgebra.AtomicConstruction.ambientInclusion_injective selectedAtomicRepresentation L
  · intro K _ _ _ rho hrho
    exact ambientInclusion_unitaryEquivalent
      family L hLunit hLmap hLsource hLroot rho hrho

end MathlibAnnex.CStarAlgebra.CAR
