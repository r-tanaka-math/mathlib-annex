import MathlibAnnex.Analysis.CStarAlgebra.Cyclic
import MathlibAnnex.Analysis.CStarAlgebra.Representation.AtomicCommutant

/-!
# Finite interpolation for irreducible representations

This file starts the constructive Kadison-transitivity route at its genuine
one-vector base case.  It derives density of the orbit map from topological
irreducibility; no interpolation or transitivity hypothesis is added.
-/

set_option autoImplicit false

open scoped ENNReal lp
open scoped ComplexStarModule

open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.Analysis.InnerProductSpace
open Filter

/-- A finite family regarded as a vector in its Hilbert direct sum. -/
def finiteHilbertSum {H I : Type*} [NormedAddCommGroup H] [Finite I]
    (ξ : I → H) : lp (fun _ : I => H) 2 :=
  ⟨ξ, Memℓp.all ξ⟩

@[simp]
theorem finiteHilbertSum_apply {H I : Type*} [NormedAddCommGroup H] [Finite I]
    (ξ : I → H) (i : I) : finiteHilbertSum ξ i = ξ i :=
  rfl

/-- The real-linear orbit map obtained by restricting the algebra variable
to its self-adjoint part. -/
noncomputable def selfAdjointOrbitMap
    {A H I : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Finite I]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : I → H) :
    selfAdjoint A →ₗ[ℝ] HilbertSum (fun _ : I => H) where
  toFun a := atomicRepresentation (fun _ : I => π) (a : A) (finiteHilbertSum ξ)
  map_add' a b := by
    apply lp.ext
    funext i
    simp
  map_smul' r a := by
    apply lp.ext
    funext i
    change π ((r : ℂ) • (a : A)) (ξ i) = (r : ℂ) • π (a : A) (ξ i)
    have hmap : π ((r : ℂ) • (a : A)) = (r : ℂ) • π (a : A) :=
      map_smul π (r : ℂ) (a : A)
    simpa using congrArg (fun T : H →L[ℂ] H => T (ξ i)) hmap

namespace StarAlgHom

variable {A H : Type*}
variable [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Taking the real part of an algebra element symmetrizes the two real
matrix coefficients that occur in the self-adjoint density argument. -/
theorem re_inner_selfAdjointOrbitMap_realPart
    {I : Type*} [Fintype I] [DecidableEq I]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : I → H)
    (b : A) (y : HilbertSum (fun _ : I => H)) :
    let ρ := atomicRepresentation (fun _ : I => π)
    let x : HilbertSum (fun _ : I => H) := finiteHilbertSum ξ
    (inner ℂ (ρ (realPart b : A) x) y).re =
      (2 : ℝ)⁻¹ *
        ((inner ℂ (ρ b x) y).re + (inner ℂ x (ρ b y)).re) := by
  dsimp only
  rw [realPart_apply_coe]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, map_add, map_star]
  simp only [smul_apply, add_apply]
  rw [inner_smul_left, inner_add_left,
    ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left
      ((atomicRepresentation (fun _ : I => π)) b) y (finiteHilbertSum ξ)]
  simp [mul_add]

/-- The orbit of every nonzero vector under an irreducible unital star
representation is norm dense. -/
theorem denseRange_orbitMap_of_irreducible
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    {ξ : H} (hξ : ξ ≠ 0) : DenseRange (fun a : A => π a ξ) := by
  change Dense (Set.range fun a : A => π a ξ)
  rw [show Set.range (fun a : A => π a ξ) =
      (LinearMap.range (orbitMap π ξ) : Set H) by
    ext y
    simp [orbitMap]]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (cyclicSubspace_eq_top π hπ hξ)

/-- One-vector norm interpolation, the base case of simultaneous finite
interpolation.  The approximating algebra element has no norm bound yet. -/
theorem exists_apply_sub_norm_lt_of_irreducible
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    {ξ : H} (hξ : ξ ≠ 0) (η : H) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, ‖π a ξ - η‖ < ε := by
  obtain ⟨a, ha⟩ := Metric.denseRange_iff.mp
    (denseRange_orbitMap_of_irreducible π hπ hξ) η ε hε
  refine ⟨a, ?_⟩
  rw [dist_eq_norm] at ha
  simpa only [norm_sub_rev] using ha

/-- The diagonal orbit of a finite linearly independent family is dense in
the Hilbert direct sum.  This is the simultaneous-density step in the
Kadison transitivity argument. -/
theorem denseRange_atomicOrbit_of_irreducible
    [Nontrivial H] (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    {I : Type*} [Fintype I] [DecidableEq I]
    (ξ : I → H) (hξ : LinearIndependent ℂ ξ) :
    DenseRange (fun a : A =>
      atomicRepresentation (fun _ : I => π) a (finiteHilbertSum ξ)) := by
  classical
  let ρ := atomicRepresentation (fun _ : I => π)
  let x : HilbertSum (fun _ : I => H) := finiteHilbertSum ξ
  let M : Submodule ℂ (HilbertSum (fun _ : I => H)) := cyclicSubspace ρ x
  letI : IsClosed (M : Set (HilbertSum (fun _ : I => H))) :=
    isClosed_cyclicSubspace ρ x
  letI : M.HasOrthogonalProjection := inferInstance
  let P : HilbertSum (fun _ : I => H) →L[ℂ]
      HilbertSum (fun _ : I => H) := M.starProjection
  have hPcomm : InCommutant ρ P := by
    intro a
    change P.comp (ρ a) = (ρ a).comp P
    exact Submodule.Reduces.starProjection_commute
      (cyclicSubspace_isReducing ρ x a)
  have hblocks (i j : I) : ∃ c : ℂ,
      atomicBlock P i j = algebraMap ℂ (H →L[ℂ] H) c := by
    apply eq_algebraMap_of_irreducible π hπ
    intro a
    exact atomicBlock_intertwines_of_inCommutant
      (fun _ : I => π) P hPcomm i j a
  choose c hc using hblocks
  have hxsum : x = ∑ i : I, coordinateEmbedding i (ξ i) := by
    have hxhas : HasSum (fun i : I => coordinateEmbedding i (ξ i)) x := by
      simpa [x, coordinateEmbedding_apply] using
        (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) x)
    exact hxhas.unique (hasSum_fintype _)
  have hPx : P x = x := by
    apply M.starProjection_eq_self_iff.mpr
    simpa [ρ, x, M] using orbit_mem_cyclicSubspace ρ x (1 : A)
  have hrelation (j : I) : ∑ i : I, c i j • ξ i = ξ j := by
    calc
      ∑ i : I, c i j • ξ i =
          ∑ i : I, atomicBlock P i j (ξ i) := by
            apply Finset.sum_congr rfl
            intro i _
            have hi := congrArg
              (fun T : H →L[ℂ] H => T (ξ i)) (hc i j)
            simpa [ContinuousLinearMap.algebraMap_apply] using hi.symm
      _ = (P (∑ i : I, coordinateEmbedding i (ξ i))) j := by
            rw [map_sum]
            change (∑ i : I, coordinateProjection j
              (P (coordinateEmbedding i (ξ i)))) = coordinateProjection j
                (∑ i : I, P (coordinateEmbedding i (ξ i)))
            exact (map_sum (coordinateProjection j)
              (fun i : I => P (coordinateEmbedding i (ξ i))) Finset.univ).symm
      _ = ξ j := by rw [← hxsum, hPx]; simp [x]
  have hcoeff (i j : I) : c i j = if i = j then 1 else 0 := by
    let g : I → ℂ := fun k => c k j - if k = j then 1 else 0
    have hg : ∑ k : I, g k • ξ k = 0 := by
      simp only [g, sub_smul, Finset.sum_sub_distrib]
      rw [hrelation]
      simp
    have hi := (Fintype.linearIndependent_iff.mp hξ g hg) i
    exact sub_eq_zero.mp hi
  have hPone : P = 1 := by
    apply ContinuousLinearMap.ext
    intro y
    apply lp.ext
    funext j
    have hysum : y = ∑ i : I, coordinateEmbedding i (y i) := by
      have hyhas : HasSum (fun i : I => coordinateEmbedding i (y i)) y := by
        simpa [coordinateEmbedding_apply] using
          (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) y)
      exact hyhas.unique (hasSum_fintype _)
    calc
      P y j = P (∑ i : I, coordinateEmbedding i (y i)) j := by rw [← hysum]
      _ = ∑ i : I, atomicBlock P i j (y i) := by
        rw [map_sum]
        change coordinateProjection j
          (∑ i : I, P (coordinateEmbedding i (y i))) =
            ∑ i : I, coordinateProjection j (P (coordinateEmbedding i (y i)))
        exact map_sum (coordinateProjection j)
          (fun i : I => P (coordinateEmbedding i (y i))) Finset.univ
      _ = ∑ i : I, c i j • y i := by
        apply Finset.sum_congr rfl
        intro i _
        have hi := congrArg (fun T : H →L[ℂ] H => T (y i)) (hc i j)
        simpa [ContinuousLinearMap.algebraMap_apply] using hi
      _ = y j := by simp [hcoeff]
      _ = (1 : HilbertSum (fun _ : I => H) →L[ℂ]
          HilbertSum (fun _ : I => H)) y j := by simp
  have hMtop : M = ⊤ := by
    have hProjection : M.starProjection = 1 := by simpa [P] using hPone
    rw [← M.range_starProjection, hProjection]
    apply LinearMap.range_eq_top.mpr
    intro y
    exact ⟨y, by simp⟩
  change Dense (Set.range fun a : A => ρ a x)
  rw [show Set.range (fun a : A => ρ a x) =
      (LinearMap.range (orbitMap ρ x) : Set _) by
    ext y
    simp [orbitMap]]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hMtop

/-- The cyclic subspace of a finite diagonal orbit contains the result of
applying any bounded operator to every coordinate.  No independence of the
displayed vectors is required. -/
theorem diagonal_apply_mem_cyclicSubspace_of_irreducible
    [Nontrivial H] (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    {I : Type*} [Fintype I] [DecidableEq I]
    (ξ : I → H) (T : H →L[ℂ] H) :
    let ρ := atomicRepresentation (fun _ : I => π)
    let x : HilbertSum (fun _ : I => H) := finiteHilbertSum ξ
    let D := diagonal (fun _ : I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
    D x ∈ cyclicSubspace ρ x := by
  classical
  dsimp only
  let ρ := atomicRepresentation (fun _ : I => π)
  let x : HilbertSum (fun _ : I => H) := finiteHilbertSum ξ
  let D : HilbertSum (fun _ : I => H) →L[ℂ]
      HilbertSum (fun _ : I => H) :=
    diagonal (fun _ : I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
  let M : Submodule ℂ (HilbertSum (fun _ : I => H)) := cyclicSubspace ρ x
  letI : IsClosed (M : Set (HilbertSum (fun _ : I => H))) :=
    isClosed_cyclicSubspace ρ x
  letI : M.HasOrthogonalProjection := inferInstance
  let P : HilbertSum (fun _ : I => H) →L[ℂ]
      HilbertSum (fun _ : I => H) := M.starProjection
  have hPcomm : InCommutant ρ P := by
    intro a
    change P.comp (ρ a) = (ρ a).comp P
    exact Submodule.Reduces.starProjection_commute
      (cyclicSubspace_isReducing ρ x a)
  have hblocks (i j : I) : ∃ c : ℂ,
      atomicBlock P i j = algebraMap ℂ (H →L[ℂ] H) c := by
    apply eq_algebraMap_of_irreducible π hπ
    intro a
    exact atomicBlock_intertwines_of_inCommutant
      (fun _ : I => π) P hPcomm i j a
  choose c hc using hblocks
  have hsum (y : HilbertSum (fun _ : I => H)) :
      y = ∑ i : I, coordinateEmbedding i (y i) := by
    have hyhas : HasSum (fun i : I => coordinateEmbedding i (y i)) y := by
      simpa [coordinateEmbedding_apply] using
        (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) y)
    exact hyhas.unique (hasSum_fintype _)
  have hblocksum (y : HilbertSum (fun _ : I => H)) (j : I) :
      P y j = ∑ i : I, atomicBlock P i j (y i) := by
    calc
      P y j = P (∑ i : I, coordinateEmbedding i (y i)) j :=
        congrArg (fun z => P z j) (hsum y)
      _ = ∑ i : I, atomicBlock P i j (y i) := by
        rw [map_sum]
        change coordinateProjection j
          (∑ i : I, P (coordinateEmbedding i (y i))) =
            ∑ i : I, coordinateProjection j (P (coordinateEmbedding i (y i)))
        exact map_sum (coordinateProjection j)
          (fun i : I => P (coordinateEmbedding i (y i))) Finset.univ
  have hblockscalar (i j : I) (y : H) :
      atomicBlock P i j y = c i j • y := by
    have hij := congrArg (fun S : H →L[ℂ] H => S y) (hc i j)
    simpa [ContinuousLinearMap.algebraMap_apply] using hij
  have hPD (y : HilbertSum (fun _ : I => H)) : P (D y) = D (P y) := by
    apply lp.ext
    funext j
    calc
      P (D y) j = ∑ i : I, atomicBlock P i j (D y i) := hblocksum (D y) j
      _ = ∑ i : I, c i j • T (y i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hblockscalar]
        rfl
      _ = T (∑ i : I, c i j • y i) := by
        simpa using (map_sum T (fun i : I => c i j • y i) Finset.univ).symm
      _ = T (P y j) := by
        rw [hblocksum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [hblockscalar]
      _ = D (P y) j := rfl
  have hxmem : x ∈ M := by
    simpa [M] using orbit_mem_cyclicSubspace ρ x (1 : A)
  have hPx : P x = x := M.starProjection_eq_self_iff.mpr hxmem
  have hDx : P (D x) = D x := by rw [hPD, hPx]
  exact M.starProjection_eq_self_iff.mp hDx

/-- Simultaneous finite-vector approximation of an arbitrary bounded
operator by one algebra element.  This is the unbounded K1 approximation
used by the self-adjoint density argument. -/
theorem exists_atomic_apply_sub_norm_lt_of_irreducible
    [Nontrivial H] (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    {I : Type*} [Fintype I] [DecidableEq I]
    (ξ : I → H) (T : H →L[ℂ] H)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A,
      ‖atomicRepresentation (fun _ : I => π) a (finiteHilbertSum ξ) -
        diagonal (fun _ : I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
          (finiteHilbertSum ξ)‖ < ε := by
  let ρ := atomicRepresentation (fun _ : I => π)
  let x : HilbertSum (fun _ : I => H) := finiteHilbertSum ξ
  let D : HilbertSum (fun _ : I => H) →L[ℂ]
      HilbertSum (fun _ : I => H) :=
    diagonal (fun _ : I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
  have hmem : D x ∈ cyclicSubspace ρ x := by
    exact diagonal_apply_mem_cyclicSubspace_of_irreducible π hπ ξ T
  change D x ∈ closure (LinearMap.range (orbitMap ρ x)) at hmem
  obtain ⟨y, ⟨a, rfl⟩, ha⟩ := Metric.mem_closure_iff.mp hmem ε hε
  refine ⟨a, ?_⟩
  rw [dist_eq_norm] at ha
  simpa [ρ, x, D, orbitMap, norm_sub_rev] using ha

/-- Simultaneous finite-vector approximation of a self-adjoint bounded
operator by a self-adjoint algebra element.  This proves the K2 density step:
the extra copy of the test family controls the adjoint term rather than
assuming that strong convergence passes to adjoints. -/
theorem exists_selfAdjoint_atomic_apply_sub_norm_lt_of_irreducible
    [Nontrivial H] (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    {I : Type*} [Fintype I] [DecidableEq I]
    (ξ : I → H) (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, IsSelfAdjoint a ∧
      ‖atomicRepresentation (fun _ : I => π) a (finiteHilbertSum ξ) -
        diagonal (fun _ : I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
          (finiteHilbertSum ξ)‖ < ε := by
  classical
  let K := HilbertSum (fun _ : I => H)
  let ρ := atomicRepresentation (fun _ : I => π)
  let x : K := finiteHilbertSum ξ
  let D : K →L[ℂ] K :=
    diagonal (fun _ : I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
  let t : K := D x
  letI : InnerProductSpace ℝ K := InnerProductSpace.rclikeToReal ℂ K
  let L : selfAdjoint A →ₗ[ℝ] K := selfAdjointOrbitMap π ξ
  let M : Submodule ℝ K := LinearMap.range L
  have htclosure : t ∈ M.topologicalClosure := by
    apply (le_of_eq M.orthogonal_orthogonal_eq_closure : Mᗮᗮ ≤ M.topologicalClosure)
    rw [Submodule.mem_orthogonal]
    intro y hy
    have horbit (a : selfAdjoint A) : inner ℝ (L a) y = 0 := by
      exact (M.mem_orthogonal y).mp hy (L a) ⟨a, rfl⟩
    let z : Sum I I → H := Sum.elim ξ (fun i => y i)
    have happrox (m : ℕ) : ∃ b : A,
        ‖atomicRepresentation (fun _ : Sum I I => π) b (finiteHilbertSum z) -
          diagonal (fun _ : Sum I I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
            (finiteHilbertSum z)‖ < (((m + 1 : ℕ) : ℝ))⁻¹ := by
      apply exists_atomic_apply_sub_norm_lt_of_irreducible π hπ z T
      positivity
    choose b hb using happrox
    have heps : Tendsto (fun m : ℕ => (((m + 1 : ℕ) : ℝ))⁻¹)
        atTop (nhds 0) := by
      simpa [one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hcoord (k : Sum I I) :
        Tendsto (fun m => π (b m) (z k)) atTop (nhds (T (z k))) := by
      have hbound (m : ℕ) :
          ‖π (b m) (z k) - T (z k)‖ ≤ (((m + 1 : ℕ) : ℝ))⁻¹ := by
        have hle := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (atomicRepresentation (fun _ : Sum I I => π) (b m) (finiteHilbertSum z) -
            diagonal (fun _ : Sum I I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
              (finiteHilbertSum z)) k
        exact hle.trans (hb m).le
      have hnorm : Tendsto (fun m => ‖π (b m) (z k) - T (z k)‖)
          atTop (nhds 0) :=
        squeeze_zero (fun _ => norm_nonneg _) hbound heps
      have hzero : Tendsto (fun m => π (b m) (z k) - T (z k))
          atTop (nhds 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
      convert hzero.add_const (T (z k)) using 1 <;> simp
    have hleft (i : I) :
        Tendsto (fun m => π (b m) (ξ i)) atTop (nhds (T (ξ i))) := by
      simpa [z] using hcoord (Sum.inl i)
    have hright (i : I) :
        Tendsto (fun m => π (b m) (y i)) atTop (nhds (T (y i))) := by
      simpa [z] using hcoord (Sum.inr i)
    have hf : Tendsto (fun m => (inner ℂ (ρ (b m) x) y).re)
        atTop (nhds (inner ℂ t y).re) := by
      have hi (i : I) : Tendsto
          (fun m => (inner ℂ (π (b m) (ξ i)) (y i)).re) atTop
          (nhds (inner ℂ (T (ξ i)) (y i)).re) :=
        Complex.continuous_re.continuousAt.tendsto.comp
          ((hleft i).inner tendsto_const_nhds)
      simpa [K, ρ, x, t, D, lp.inner_eq_tsum, tsum_fintype] using
        (tendsto_finsetSum Finset.univ (fun i _ => hi i))
    have hg : Tendsto (fun m => (inner ℂ x (ρ (b m) y)).re)
        atTop (nhds (inner ℂ x (D y)).re) := by
      have hi (i : I) : Tendsto
          (fun m => (inner ℂ (ξ i) (π (b m) (y i))).re) atTop
          (nhds (inner ℂ (ξ i) (T (y i))).re) :=
        Complex.continuous_re.continuousAt.tendsto.comp
          (tendsto_const_nhds.inner (hright i))
      simpa [K, ρ, x, D, lp.inner_eq_tsum, tsum_fintype] using
        (tendsto_finsetSum Finset.univ (fun i _ => hi i))
    have hTadj : ContinuousLinearMap.adjoint T = T := by
      rw [← ContinuousLinearMap.star_eq_adjoint, hT.star_eq]
    have htarget : (inner ℂ x (D y)).re = (inner ℂ t y).re := by
      simp only [K, x, D, t, lp.inner_eq_tsum, tsum_fintype,
        finiteHilbertSum_apply, diagonal_apply]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      calc
        inner ℂ (ξ i) (T (y i)) =
            inner ℂ (ContinuousLinearMap.adjoint T (ξ i)) (y i) :=
          (ContinuousLinearMap.adjoint_inner_left T (y i) (ξ i)).symm
        _ = inner ℂ (T (ξ i)) (y i) := by rw [hTadj]
    have hzero (m : ℕ) :
        (inner ℂ (ρ (realPart (b m) : A) x) y).re = 0 := by
      simpa [L, selfAdjointOrbitMap, ρ, x,
        real_inner_eq_re_inner] using horbit (realPart (b m))
    have hsumzero (m : ℕ) :
        (inner ℂ (ρ (b m) x) y).re +
          (inner ℂ x (ρ (b m) y)).re = 0 := by
      have hs := re_inner_selfAdjointOrbitMap_realPart π ξ (b m) y
      dsimp only at hs
      rw [hzero m] at hs
      norm_num at hs ⊢
      exact hs
    have hsumlim := hf.add hg
    rw [htarget] at hsumlim
    have hzerolim : Tendsto
        (fun m => (inner ℂ (ρ (b m) x) y).re +
          (inner ℂ x (ρ (b m) y)).re) atTop (nhds 0) := by
      simpa only [hsumzero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    have hdouble : (inner ℂ t y).re + (inner ℂ t y).re = 0 :=
      tendsto_nhds_unique hsumlim hzerolim
    have hq : (inner ℂ t y).re = 0 := by linarith
    rw [real_inner_eq_re_inner, inner_re_symm]
    exact hq
  change t ∈ closure (M : Set K) at htclosure
  obtain ⟨u, huM, hdist⟩ := Metric.mem_closure_iff.mp htclosure ε hε
  obtain ⟨a, rfl⟩ := huM
  refine ⟨(a : A), a.property, ?_⟩
  rw [dist_eq_norm] at hdist
  simpa [L, selfAdjointOrbitMap, ρ, x, t, D, norm_sub_rev] using hdist

end StarAlgHom
