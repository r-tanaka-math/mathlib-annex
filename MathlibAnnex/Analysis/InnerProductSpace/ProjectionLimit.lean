import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
Strong convergence of projections onto an antitone family of closed Hilbert
subspaces.  The conclusion is vectorwise norm convergence, not operator-norm
convergence.
-/

set_option autoImplicit false

open Filter

namespace MathlibAnnex.Analysis.InnerProductSpace

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The closed span of the orthogonal complements of closed subspaces is the
orthogonal complement of their intersection. -/
theorem topologicalClosure_iSup_orthogonal_eq_orthogonal_iInf
    (U : ℕ → ClosedSubmodule 𝕜 H) :
    (⨆ n, (U n).toSubmoduleᗮ).topologicalClosure =
      ((⨅ n, U n).toSubmodule)ᗮ := by
  let L : Submodule 𝕜 H := (⨆ n, (U n).toSubmoduleᗮ).topologicalClosure
  let K : Submodule 𝕜 H := (⨅ n, U n).toSubmodule
  have hclosed (n : ℕ) : (U n).toSubmodule.topologicalClosure = (U n).toSubmodule := by
    ext y
    change y ∈ closure (U n : Set H) ↔ y ∈ (U n : Set H)
    rw [closure_eq_iff_isClosed.mpr (U n).isClosed]
  have hKclosed : K.topologicalClosure = K := by
    apply SetLike.coe_injective
    rw [Submodule.topologicalClosure_coe]
    exact closure_eq_iff_isClosed.mpr (⨅ n, U n).isClosed
  apply (Submodule.orthogonalComplement_eq_orthogonalComplement).mp
  calc
    Lᗮ = (⨆ n, (U n).toSubmoduleᗮ)ᗮ := by
      exact Submodule.orthogonal_closure _
    _ = ⨅ n, ((U n).toSubmoduleᗮ)ᗮ :=
      (Submodule.iInf_orthogonal (fun n ↦ (U n).toSubmoduleᗮ)).symm
    _ = ⨅ n, (U n).toSubmodule := by
      congr 1
      funext n
      rw [Submodule.orthogonal_orthogonal_eq_closure, hclosed n]
    _ = K := by
      exact (ClosedSubmodule.toSubmodule_iInf U).symm
    _ = (Kᗮ)ᗮ := by
      rw [Submodule.orthogonal_orthogonal_eq_closure, hKclosed]

/-- Orthogonal projections onto an antitone sequence of closed subspaces
converge strongly to the projection onto their intersection. -/
theorem tendsto_starProjection_iInf (U : ℕ → ClosedSubmodule 𝕜 H)
    (hU : Antitone U) (x : H) :
    Tendsto (fun n ↦ (U n).toSubmodule.starProjection x) atTop
      (nhds ((⨅ n, U n).toSubmodule.starProjection x)) := by
  let V : ℕ → Submodule 𝕜 H := fun n ↦ (U n).toSubmoduleᗮ
  let L : Submodule 𝕜 H := (⨆ i, V i).topologicalClosure
  let K : Submodule 𝕜 H := (⨅ n, U n).toSubmodule
  have hV : Monotone V := fun _ _ hnm ↦ Submodule.orthogonal_le (hU hnm)
  have hlim := Submodule.starProjection_tendsto_closure_iSup V hV x
  have hsub :
      Tendsto (fun n ↦ x - (V n).starProjection x) atTop
        (nhds (x - L.starProjection x)) :=
    tendsto_const_nhds.sub hlim
  have hLK : L = Kᗮ := by
    simpa only [L, K, V] using
      topologicalClosure_iSup_orthogonal_eq_orthogonal_iInf U
  have hproj : L.starProjection x = Kᗮ.starProjection x := by
    symm
    apply (Kᗮ).eq_starProjection_of_mem_orthogonal
    · rw [← hLK]
      exact L.starProjection_apply_mem x
    · have hz := L.sub_starProjection_mem_orthogonal x
      have horth : Lᗮ = Kᗮᗮ := congrArg Submodule.orthogonal hLK
      exact horth ▸ hz
  convert hsub using 1
  · funext n
    have hcomp := congrArg (fun T : H →L[𝕜] H ↦ T x)
      (Submodule.starProjection_orthogonal' (U n).toSubmodule)
    change (U n).toSubmoduleᗮ.starProjection x = x - (U n).toSubmodule.starProjection x at hcomp
    simp only [V, hcomp, sub_sub_cancel]
  · apply congrArg nhds
    change K.starProjection x = x - L.starProjection x
    have hcomp := congrArg (fun T : H →L[𝕜] H ↦ T x)
      (Submodule.starProjection_orthogonal' K)
    change Kᗮ.starProjection x = x - K.starProjection x at hcomp
    calc
      K.starProjection x = x - Kᗮ.starProjection x := by rw [hcomp, sub_sub_cancel]
      _ = x - L.starProjection x := by rw [hproj]

/-- The closed range associated to an orthogonal projection. -/
def closedRange (Q : H →L[𝕜] H) (hQ : IsStarProjection Q) :
    ClosedSubmodule 𝕜 H where
  toSubmodule := Q.range
  isClosed' := ContinuousLinearMap.IsIdempotentElem.isClosed_range hQ.isIdempotentElem

@[simp]
theorem mem_closedRange_iff (Q : H →L[𝕜] H) (hQ : IsStarProjection Q) (x : H) :
    x ∈ closedRange Q hQ ↔ Q x = x := by
  exact LinearMap.IsIdempotentElem.mem_range_iff
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap hQ.isIdempotentElem)

/-- Operator form: an antitone sequence of orthogonal projections converges
pointwise in norm to the projection onto the intersection of its fixed
spaces. -/
theorem tendsto_projection_of_antitone_ranges
    (Q : ℕ → H →L[𝕜] H) (hQ : ∀ n, IsStarProjection (Q n))
    (hanti : Antitone fun n ↦ (closedRange (Q n) (hQ n))) (x : H) :
    Tendsto (fun n ↦ Q n x) atTop
      (nhds ((⨅ n, closedRange (Q n) (hQ n)).toSubmodule.starProjection x)) := by
  have hlim := tendsto_starProjection_iInf
    (fun n ↦ closedRange (Q n) (hQ n)) hanti x
  convert hlim using 1
  funext n
  obtain ⟨_, heq⟩ :=
    isStarProjection_iff_eq_starProjection_range.mp (hQ n)
  exact congrArg (fun T : H →L[𝕜] H ↦ T x) heq

@[simp]
theorem mem_iInf_closedRange_iff
    (Q : ℕ → H →L[𝕜] H) (hQ : ∀ n, IsStarProjection (Q n)) (x : H) :
    x ∈ ⨅ n, closedRange (Q n) (hQ n) ↔ ∀ n, Q n x = x := by
  simp only [ClosedSubmodule.mem_iInf, mem_closedRange_iff]

end MathlibAnnex.Analysis.InnerProductSpace
