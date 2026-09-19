import MathlibAnnex.Analysis.InnerProductSpace.OrthogonalSum

/-!
# Finite algebra of decreasing projection shells

This file derives the orthogonality, telescoping, and two finite prefix-product
identities needed by the strong shell-sum theorem directly from decreasing
orthogonal projections and the two support identities of each shell map.
-/

set_option autoImplicit false

open Filter Topology
open scoped Function InnerProduct

namespace Submodule

variable {𝕜 E : Type*}
variable [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The projection shell between two successive members of a submodule sequence. -/
noncomputable def projectionShell (U : ℕ → Submodule 𝕜 E) [∀ n, (U n).HasOrthogonalProjection]
    (n : ℕ) : E →L[𝕜] E :=
  (U n).starProjection - (U (n + 1)).starProjection

/-- If `U ≤ V`, projecting first onto `U` and then onto `V` still projects onto `U`.
This is the reverse composition order from
`Submodule.starProjection_comp_starProjection_of_le`. -/
theorem starProjection_comp_starProjection_of_le_right {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ≤ V) :
    V.starProjection.comp U.starProjection = U.starProjection := by
  ext x
  exact starProjection_eq_self_iff.mpr (h (starProjection_apply_mem U x))

/-- Projection shells of an antitone family are self-adjoint. -/
theorem projectionShell_adjoint (U : ℕ → Submodule 𝕜 E)
    [∀ n, (U n).HasOrthogonalProjection] (n : ℕ) :
    (projectionShell U n)† = projectionShell U n := by
  rw [projectionShell, map_sub,
    (U n).starProjection_isSymmetric.clm_adjoint_eq,
    (U (n + 1)).starProjection_isSymmetric.clm_adjoint_eq]

/-- Projection shells of an antitone family are idempotent. -/
theorem projectionShell_idempotent (U : ℕ → Submodule 𝕜 E)
    [∀ n, (U n).HasOrthogonalProjection] (hU : Antitone U) (n : ℕ) :
    (projectionShell U n).comp (projectionShell U n) = projectionShell U n := by
  have hle : U (n + 1) ≤ U n := hU (Nat.le_succ n)
  have hnn : (U n).starProjection.comp (U n).starProjection = (U n).starProjection :=
    (U n).isIdempotentElem_starProjection
  have hss : (U (n + 1)).starProjection.comp (U (n + 1)).starProjection =
      (U (n + 1)).starProjection :=
    (U (n + 1)).isIdempotentElem_starProjection
  have hsn : (U (n + 1)).starProjection.comp (U n).starProjection =
      (U (n + 1)).starProjection :=
    starProjection_comp_starProjection_of_le hle
  have hns : (U n).starProjection.comp (U (n + 1)).starProjection =
      (U (n + 1)).starProjection :=
    starProjection_comp_starProjection_of_le_right hle
  simp only [projectionShell, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  rw [hnn, hns, hsn, hss]
  abel

/-- Earlier projection shells annihilate later projection shells. -/
theorem projectionShell_comp_projectionShell_eq_zero_of_lt
    (U : ℕ → Submodule 𝕜 E) [∀ n, (U n).HasOrthogonalProjection]
    (hU : Antitone U) {m n : ℕ} (hmn : m < n) :
    (projectionShell U m).comp (projectionShell U n) = 0 := by
  have hnm : U n ≤ U m := hU (Nat.le_of_lt hmn)
  have hnsm : U (n + 1) ≤ U m := hU (Nat.le_trans (Nat.le_of_lt hmn) (Nat.le_succ n))
  have hnms : U n ≤ U (m + 1) := hU (Nat.succ_le_iff.mpr hmn)
  have hnsms : U (n + 1) ≤ U (m + 1) :=
    hU (Nat.succ_le_succ (Nat.le_of_lt hmn))
  simp only [projectionShell, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  rw [starProjection_comp_starProjection_of_le_right hnm,
    starProjection_comp_starProjection_of_le_right hnsm,
    starProjection_comp_starProjection_of_le_right hnms,
    starProjection_comp_starProjection_of_le_right hnsms]
  abel

/-- Distinct projection shells of an antitone family have zero cross-product. -/
theorem projectionShell_comp_projectionShell_eq_zero
    (U : ℕ → Submodule 𝕜 E) [∀ n, (U n).HasOrthogonalProjection]
    (hU : Antitone U) {m n : ℕ} (hmn : m ≠ n) :
    (projectionShell U m).comp (projectionShell U n) = 0 := by
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact projectionShell_comp_projectionShell_eq_zero_of_lt U hU hlt
  · have hzero := projectionShell_comp_projectionShell_eq_zero_of_lt U hU hgt
    have hadj := congrArg (fun A : E →L[𝕜] E ↦ A†) hzero
    simpa [ContinuousLinearMap.adjoint_comp, projectionShell_adjoint] using hadj

/-- Finite projection shells telescope to the complement of the final projection. -/
theorem partialSum_projectionShell (U : ℕ → Submodule 𝕜 E)
    [∀ n, (U n).HasOrthogonalProjection] (hU0 : U 0 = ⊤) (N : ℕ) :
    ContinuousLinearMap.partialSum (projectionShell U) N = 1 - (U N).starProjection := by
  have hproj0 : (U 0).starProjection = (1 : E →L[𝕜] E) := by
    ext x
    change (U 0).starProjection x = x
    exact starProjection_eq_self_iff.mpr (by rw [hU0]; exact mem_top)
  simp only [ContinuousLinearMap.partialSum, projectionShell]
  rw [Finset.sum_range_sub', hproj0]

end Submodule

namespace ContinuousLinearMap

variable {𝕜 E F : Type*}
variable [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- A map whose adjoint-product is a self-adjoint idempotent is supported on that
projection on the right. -/
theorem comp_projection_eq_self_of_adjoint_comp_self_eq
    (W : E →L[𝕜] F) (P : E →L[𝕜] E)
    (hPadj : P† = P) (hPidem : P.comp P = P)
    (hW : (W†).comp W = P) :
    W.comp P = W := by
  have hzero : W.comp (1 - P) = 0 := by
    apply adjoint_comp_self_eq_zero_iff.mp
    calc
      ((W.comp (1 - P))†).comp (W.comp (1 - P)) =
          (1 - P).comp (((W†).comp W).comp (1 - P)) := by
            rw [adjoint_comp, map_sub, adjoint_one, hPadj]
            rfl
      _ = (1 - P).comp (P.comp (1 - P)) := by rw [hW]
      _ = 0 := by
        have hPzero : P.comp (1 - P) = 0 := by
          rw [comp_sub, hPidem]
          have hPone : P.comp (1 : E →L[𝕜] E) = P := by ext; rfl
          rw [hPone, sub_self]
        rw [hPzero, comp_zero]
  have hsub : W - W.comp P = 0 := by
    rw [comp_sub] at hzero
    have hWone : W.comp (1 : E →L[𝕜] E) = W := by ext; rfl
    rwa [hWone] at hzero
  exact (sub_eq_zero.mp hsub).symm

/-- A map whose product with its adjoint is a self-adjoint idempotent is supported
on that projection on the left. -/
theorem projection_comp_eq_self_of_comp_adjoint_eq
    (W : E →L[𝕜] F) (P : F →L[𝕜] F)
    (hPadj : P† = P) (hPidem : P.comp P = P)
    (hW : W.comp (W†) = P) :
    P.comp W = W := by
  have hright := comp_projection_eq_self_of_adjoint_comp_self_eq
    (W†) P hPadj hPidem (by simpa using hW)
  have hadj := congrArg (fun A : F →L[𝕜] E ↦ A†) hright
  simpa [adjoint_comp, hPadj] using hadj

/-- Initial projection-shell identities force correctly oriented initial-space
cross-product orthogonality. -/
theorem pairwiseInitialOrthogonal_of_projectionShells
    (W : ℕ → E →L[𝕜] F) (U : ℕ → Submodule 𝕜 E)
    [∀ n, (U n).HasOrthogonalProjection] (hU : Antitone U)
    (hW : ∀ n, ((W n)†).comp (W n) = Submodule.projectionShell U n) :
    PairwiseInitialOrthogonal W := by
  intro m n hmn
  have hm : (W m).comp (Submodule.projectionShell U m) = W m :=
    comp_projection_eq_self_of_adjoint_comp_self_eq (W m) (Submodule.projectionShell U m)
      (Submodule.projectionShell_adjoint U m)
      (Submodule.projectionShell_idempotent U hU m) (hW m)
  have hn : (Submodule.projectionShell U n).comp ((W n)†) = (W n)† := by
    have h := congrArg (fun A : E →L[𝕜] F ↦ A†)
      (comp_projection_eq_self_of_adjoint_comp_self_eq (W n) (Submodule.projectionShell U n)
        (Submodule.projectionShell_adjoint U n)
        (Submodule.projectionShell_idempotent U hU n) (hW n))
    simpa [adjoint_comp, Submodule.projectionShell_adjoint U n] using h
  calc
    (W m).comp ((W n)†) = ((W m).comp (Submodule.projectionShell U m)).comp
        ((Submodule.projectionShell U n).comp ((W n)†)) := by rw [hm, hn]
    _ = ((W m).comp ((Submodule.projectionShell U m).comp
        (Submodule.projectionShell U n))).comp ((W n)†) := rfl
    _ = 0 := by
      rw [Submodule.projectionShell_comp_projectionShell_eq_zero U hU hmn]
      simp

/-- Final projection-shell identities force correctly oriented final-space
cross-product orthogonality. -/
theorem pairwiseFinalOrthogonal_of_projectionShells
    (W : ℕ → E →L[𝕜] F) (V : ℕ → Submodule 𝕜 F)
    [∀ n, (V n).HasOrthogonalProjection] (hV : Antitone V)
    (hW : ∀ n, (W n).comp ((W n)†) = Submodule.projectionShell V n) :
    PairwiseFinalOrthogonal W := by
  intro m n hmn
  have hm : ((W m)†).comp (Submodule.projectionShell V m) = (W m)† := by
    have h := congrArg (fun A : E →L[𝕜] F ↦ A†)
      (projection_comp_eq_self_of_comp_adjoint_eq (W m) (Submodule.projectionShell V m)
        (Submodule.projectionShell_adjoint V m)
        (Submodule.projectionShell_idempotent V hV m) (hW m))
    simpa [adjoint_comp, Submodule.projectionShell_adjoint V m] using h
  have hn : (Submodule.projectionShell V n).comp (W n) = W n :=
    projection_comp_eq_self_of_comp_adjoint_eq (W n) (Submodule.projectionShell V n)
      (Submodule.projectionShell_adjoint V n)
      (Submodule.projectionShell_idempotent V hV n) (hW n)
  calc
    ((W m)†).comp (W n) = (((W m)†).comp (Submodule.projectionShell V m)).comp
        ((Submodule.projectionShell V n).comp (W n)) := by rw [hm, hn]
    _ = (((W m)†).comp ((Submodule.projectionShell V m).comp
        (Submodule.projectionShell V n))).comp
        (W n) := rfl
    _ = 0 := by
      rw [Submodule.projectionShell_comp_projectionShell_eq_zero V hV hmn]
      simp

/-- A prefix of adjoints annihilates any later term of a final-orthogonal family. -/
theorem partialSum_adjoint_comp_eq_zero (W : ℕ → E →L[𝕜] F)
    (hW : PairwiseFinalOrthogonal W) {N k : ℕ} (hNk : N ≤ k) :
    (partialSum (fun n ↦ (W n)†) N).comp (W k) = 0 := by
  rw [partialSum, finsetSum_comp]
  apply Finset.sum_eq_zero
  intro n hn
  exact hW (ne_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hn) hNk))

/-- A later adjoint annihilates an earlier prefix of a final-orthogonal family. -/
theorem adjoint_comp_partialSum_eq_zero (W : ℕ → E →L[𝕜] F)
    (hW : PairwiseFinalOrthogonal W) {N k : ℕ} (hNk : N ≤ k) :
    ((W k)†).comp (partialSum W N) = 0 := by
  rw [partialSum, comp_finsetSum]
  apply Finset.sum_eq_zero
  intro n hn
  exact hW (ne_of_gt (lt_of_lt_of_le (Finset.mem_range.mp hn) hNk))

/-- The next prefix is the previous prefix plus its new final term. -/
theorem partialSum_succ (W : ℕ → E →L[𝕜] F) (N : ℕ) :
    partialSum W (N + 1) = partialSum W N + W N := by
  simp [partialSum, Finset.sum_range_succ]

/-- Final cross-product orthogonality and the diagonal adjoint-products determine
the first finite prefix product. -/
theorem adjoint_partialSum_comp_partialSum_eq
    (W : ℕ → E →L[𝕜] F) (D : ℕ → E →L[𝕜] E)
    (horth : PairwiseFinalOrthogonal W)
    (hdiag : ∀ n, ((W n)†).comp (W n) = D n) (N : ℕ) :
    (partialSum (fun n ↦ (W n)†) N).comp (partialSum W N) = partialSum D N := by
  induction N with
  | zero => simp [partialSum]
  | succ N ih =>
      rw [partialSum_succ, partialSum_succ]
      simp only [add_comp, comp_add]
      rw [ih, partialSum_adjoint_comp_eq_zero W horth (le_refl N),
        adjoint_comp_partialSum_eq_zero W horth (le_refl N), hdiag, partialSum_succ]
      simp

/-- Initial cross-product orthogonality and the diagonal products determine the
second finite prefix product. -/
theorem partialSum_comp_adjoint_partialSum_eq
    (W : ℕ → E →L[𝕜] F) (G : ℕ → F →L[𝕜] F)
    (horth : PairwiseInitialOrthogonal W)
    (hdiag : ∀ n, (W n).comp ((W n)†) = G n) (N : ℕ) :
    (partialSum W N).comp (partialSum (fun n ↦ (W n)†) N) = partialSum G N := by
  have h := adjoint_partialSum_comp_partialSum_eq (fun n ↦ (W n)†) G
    (pairwiseFinalOrthogonal_adjoint_iff W |>.2 horth) (by simpa using hdiag) N
  simpa only [adjoint_adjoint] using h

/-- Raw decreasing projection shells yield both strong sums, the adjoint relation,
and both limiting support products.  No finite product or convergence hypothesis is
part of this entry theorem. -/
theorem exists_strongSums_of_projectionShells
    (W : ℕ → E →L[𝕜] F)
    (U : ℕ → Submodule 𝕜 E) (V : ℕ → Submodule 𝕜 F)
    [∀ n, (U n).HasOrthogonalProjection]
    [∀ n, (V n).HasOrthogonalProjection]
    [(⨅ n, U n).HasOrthogonalProjection]
    [(⨅ n, V n).HasOrthogonalProjection]
    (hU : Antitone U) (hV : Antitone V)
    (hU0 : U 0 = ⊤) (hV0 : V 0 = ⊤)
    (hInitial : ∀ n, ((W n)†).comp (W n) = Submodule.projectionShell U n)
    (hFinal : ∀ n, (W n).comp ((W n)†) = Submodule.projectionShell V n) :
    ∃ S : E →L[𝕜] F, ∃ T : F →L[𝕜] E,
      StronglyConverges (partialSum W) atTop S ∧
      StronglyConverges (partialSum fun n ↦ (W n)†) atTop T ∧
      ‖S‖ ≤ 1 ∧ ‖T‖ ≤ 1 ∧ T = S† ∧
      (S†).comp S = 1 - (⨅ n, U n).starProjection ∧
      S.comp (S†) = 1 - (⨅ n, V n).starProjection := by
  have hi := pairwiseInitialOrthogonal_of_projectionShells W U hU hInitial
  have hf := pairwiseFinalOrthogonal_of_projectionShells W V hV hFinal
  apply exists_strongSums_adjoint_products W U V hU hV hi hf
  · intro N
    rw [adjoint_partialSum_comp_partialSum_eq W (Submodule.projectionShell U) hf hInitial,
      Submodule.partialSum_projectionShell U hU0]
  · intro N
    rw [partialSum_comp_adjoint_partialSum_eq W (Submodule.projectionShell V) hi hFinal,
      Submodule.partialSum_projectionShell V hV0]

end ContinuousLinearMap
