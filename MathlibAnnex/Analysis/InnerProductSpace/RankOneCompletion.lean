import MathlibAnnex.Analysis.InnerProductSpace.RankOne
import MathlibAnnex.Analysis.InnerProductSpace.ProjectionShell
import MathlibAnnex.Analysis.InnerProductSpace.UnitaryCompletion

/-!
# Rank-one completion of a one-dimensional defect

The input operator has initial and final defects equal to the projections onto
two displayed unit vectors.  The missing rank-one link completes it to a
unitary.  In particular, no cross-term vanishing is assumed: it is derived
from the two defect-product identities.
-/

set_option autoImplicit false

open Filter Topology
open scoped InnerProduct

namespace ContinuousLinearMap

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The initial defect identity forces the partial isometry to vanish on its
displayed initial defect vector. -/
theorem apply_eq_zero_of_adjoint_comp_eq_one_sub_rankOne
    (S : H →L[ℂ] H) (b : H) (hb : ‖b‖ = 1)
    (hS : (S†).comp S = 1 - InnerProductSpace.rankOne ℂ b b) :
    S b = 0 := by
  have hnorm : ‖S b‖ ^ 2 = 0 := by
    rw [apply_norm_sq_eq_inner_adjoint_left, hS]
    simp [InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, hb]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)

/-- The final defect identity forces the adjoint partial isometry to vanish on
its displayed final defect vector. -/
theorem adjoint_apply_eq_zero_of_comp_adjoint_eq_one_sub_rankOne
    (S : H →L[ℂ] H) (a : H) (ha : ‖a‖ = 1)
    (hS : S.comp (S†) = 1 - InnerProductSpace.rankOne ℂ a a) :
    (S†) a = 0 := by
  have hnorm : ‖(S†) a‖ ^ 2 = 0 := by
    rw [apply_norm_sq_eq_inner_adjoint_left, adjoint_adjoint, hS]
    simp [InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, ha]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)

/-- A partial isometry with displayed one-dimensional initial and final
defects becomes a unitary after adding the rank-one link from `b` to `a`.
The conclusion also records its action on the source defect vector. -/
theorem add_rankOne_mem_unitary
    (S : H →L[ℂ] H) (a b : H) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hInitial : (S†).comp S = 1 - InnerProductSpace.rankOne ℂ b b)
    (hFinal : S.comp (S†) = 1 - InnerProductSpace.rankOne ℂ a a) :
    S + InnerProductSpace.rankOne ℂ a b ∈ unitary (H →L[ℂ] H) ∧
      (S + InnerProductSpace.rankOne ℂ a b) b = a := by
  let V : H →L[ℂ] H := InnerProductSpace.rankOne ℂ a b
  let P : H →L[ℂ] H := InnerProductSpace.rankOne ℂ b b
  let Q : H →L[ℂ] H := InnerProductSpace.rankOne ℂ a a
  have hSb : S b = 0 :=
    apply_eq_zero_of_adjoint_comp_eq_one_sub_rankOne S b hb hInitial
  have hSa : (S†) a = 0 :=
    adjoint_apply_eq_zero_of_comp_adjoint_eq_one_sub_rankOne S a ha hFinal
  have hVstar : V† = InnerProductSpace.rankOne ℂ b a := by
    simpa [V] using InnerProductSpace.adjoint_rankOne a b
  have hSVstar : S.comp (V†) = 0 := by
    rw [hVstar, InnerProductSpace.comp_rankOne, hSb]
    simp
  have hVstarS : (V†).comp S = 0 := by
    rw [hVstar, InnerProductSpace.rankOne_comp, hSa]
    simp
  have hSstarV : (S†).comp V = 0 := by
    dsimp [V]
    rw [InnerProductSpace.comp_rankOne, hSa]
    simp
  have hVSstar : V.comp (S†) = 0 := by
    dsimp [V]
    rw [InnerProductSpace.rankOne_comp, adjoint_adjoint, hSb]
    simp
  have hVstarV : (V†).comp V = P := by
    ext x
    simp [V, P, InnerProductSpace.rankOne_apply,
      InnerProductSpace.adjoint_rankOne, ha]
  have hVVstar : V.comp (V†) = Q := by
    ext x
    simp [V, Q, InnerProductSpace.rankOne_apply,
      InnerProductSpace.adjoint_rankOne, hb]
  constructor
  · rw [Unitary.mem_iff]
    constructor
    · change (S + V)† * (S + V) = 1
      rw [map_add]
      calc
        (S† + V†) * (S + V) =
            ((S†).comp S + (S†).comp V) +
              ((V†).comp S + (V†).comp V) := by
          ext x
          simp [ContinuousLinearMap.mul_apply]
        _ = 1 := by
          rw [hInitial, hSstarV, hVstarS, hVstarV]
          simp [P]
    · change (S + V) * (S + V)† = 1
      rw [map_add]
      calc
        (S + V) * (S† + V†) =
            (S.comp (S†) + S.comp (V†)) +
              (V.comp (S†) + V.comp (V†)) := by
          ext x
          simp [ContinuousLinearMap.mul_apply]
        _ = 1 := by
          rw [hFinal, hSVstar, hVSstar, hVVstar]
          simp [Q]
  · change S b + V b = a
    rw [hSb]
    simp [V, InnerProductSpace.rankOne_apply,
      inner_self_eq_norm_sq_to_K, hb]

/-- A strong sum of supported projection shells restricts to the original
shell map on every shell. -/
theorem StronglyConverges.comp_projectionShell_eq
    (W : ℕ → H →L[ℂ] H) (U : ℕ → Submodule ℂ H)
    [∀ n, (U n).HasOrthogonalProjection]
    (hU : Antitone U)
    (hInitial : ∀ n, ((W n)†).comp (W n) = Submodule.projectionShell U n)
    (S : H →L[ℂ] H) (hS : StronglyConverges (partialSum W) atTop S)
    (n : ℕ) :
    S.comp (Submodule.projectionShell U n) = W n := by
  have horth := pairwiseInitialOrthogonal_of_projectionShells W U hU hInitial
  have hsupport : (W n).comp (Submodule.projectionShell U n) = W n :=
    comp_projection_eq_self_of_adjoint_comp_self_eq
      (W n) (Submodule.projectionShell U n)
      (Submodule.projectionShell_adjoint U n)
      (Submodule.projectionShell_idempotent U hU n) (hInitial n)
  have hpartial {N : ℕ} (hN : n < N) :
      (partialSum W N).comp (Submodule.projectionShell U n) = W n := by
    rw [partialSum, finsetSum_comp, Finset.sum_eq_single n]
    · exact hsupport
    · intro m hm hmn
      calc
        (W m).comp (Submodule.projectionShell U n) =
            ((W m).comp ((W n)†)).comp (W n) := by
          rw [← hInitial n]
          rfl
        _ = 0 := by rw [horth hmn]; simp
    · intro hnmem
      exact (hnmem (Finset.mem_range.mpr hN)).elim
  apply ContinuousLinearMap.ext
  intro x
  apply tendsto_nhds_unique ((hS.comp_right (Submodule.projectionShell U n)) x)
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  exact Filter.eventually_atTop.2 ⟨n + 1, fun N hN ↦
    congrArg (fun T : H →L[ℂ] H ↦ T x)
      (hpartial (Nat.lt_of_succ_le hN)).symm⟩

/-- A bounded operator which fixes every shell of a normalized decreasing
projection flag and fixes the unit vector spanning the limiting defect is the
identity.  This is the root-normalization argument: fixing the defect vector
alone is not used as a substitute for fixing the complementary shell sum. -/
theorem eq_one_of_comp_projectionShell_eq_self_of_rankOne_iInf
    (L : H →L[ℂ] H) (U : ℕ → Submodule ℂ H)
    [∀ n, (U n).HasOrthogonalProjection]
    [(⨅ n, U n).HasOrthogonalProjection]
    (hU : Antitone U) (hU0 : U 0 = ⊤)
    (b : H) (hb : ‖b‖ = 1)
    (hUinf : (⨅ n, U n).starProjection =
      InnerProductSpace.rankOne ℂ b b)
    (hShell : ∀ n, L.comp (Submodule.projectionShell U n) =
      Submodule.projectionShell U n)
    (hLb : L b = b) :
    L = 1 := by
  let P : H →L[ℂ] H := (⨅ n, U n).starProjection
  have hComplement : StronglyConverges
      (fun n ↦ 1 - (U n).starProjection) atTop (1 - P) :=
    (StronglyConverges.const (ι := ℕ) (l := atTop) (1 : H →L[ℂ] H)).sub
      (Submodule.stronglyConverges_starProjection_iInf U hU)
  have hFinite (N : ℕ) :
      L.comp (1 - (U N).starProjection) = 1 - (U N).starProjection := by
    rw [← Submodule.partialSum_projectionShell U hU0]
    exact comp_partialSum_eq_of_comp_eq L
      (Submodule.projectionShell U) (Submodule.projectionShell U) hShell N
  apply ContinuousLinearMap.ext
  intro x
  have hComplementFixed : L ((1 - P) x) = (1 - P) x := by
    apply tendsto_nhds_unique ((hComplement.comp_left L) x)
    refine (hComplement x).congr' ?_
    filter_upwards [] with N
    exact congrArg (fun T : H →L[ℂ] H ↦ T x) (hFinite N).symm
  have hDefectFixed : L (P x) = P x := by
    change L ((⨅ n, U n).starProjection x) =
      (⨅ n, U n).starProjection x
    rw [hUinf]
    simp [InnerProductSpace.rankOne_apply, hLb]
  calc
    L x = L ((1 - P) x + P x) := by simp
    _ = L ((1 - P) x) + L (P x) := map_add L _ _
    _ = (1 - P) x + P x := by rw [hComplementFixed, hDefectFixed]
    _ = x := by simp

/-- Raw decreasing projection-shell data whose limiting defects are two
displayed unit-vector lines yields an actual unitary rank-one completion.
Both strong sums and the completed unitary are conclusions. -/
theorem exists_rankOneCompletion_of_projectionShells
    (W : ℕ → H →L[ℂ] H)
    (U V : ℕ → Submodule ℂ H)
    [∀ n, (U n).HasOrthogonalProjection]
    [∀ n, (V n).HasOrthogonalProjection]
    [(⨅ n, U n).HasOrthogonalProjection]
    [(⨅ n, V n).HasOrthogonalProjection]
    (hU : Antitone U) (hV : Antitone V)
    (hU0 : U 0 = ⊤) (hV0 : V 0 = ⊤)
    (hInitial : ∀ n, ((W n)†).comp (W n) = Submodule.projectionShell U n)
    (hFinal : ∀ n, (W n).comp ((W n)†) = Submodule.projectionShell V n)
    (a b : H) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hUinf : (⨅ n, U n).starProjection = InnerProductSpace.rankOne ℂ b b)
    (hVinf : (⨅ n, V n).starProjection = InnerProductSpace.rankOne ℂ a a) :
    ∃ S : H →L[ℂ] H,
      StronglyConverges (partialSum W) atTop S ∧
      (S + InnerProductSpace.rankOne ℂ a b) ∈ unitary (H →L[ℂ] H) ∧
      (S + InnerProductSpace.rankOne ℂ a b) b = a ∧
      ∀ n, (S + InnerProductSpace.rankOne ℂ a b).comp
        (Submodule.projectionShell U n) = W n := by
  obtain ⟨S, _, hS, _, _, _, _, hProdU, hProdV⟩ :=
    exists_strongSums_of_projectionShells
      W U V hU hV hU0 hV0 hInitial hFinal
  have hInitialS : (S†).comp S =
      1 - InnerProductSpace.rankOne ℂ b b := by
    simpa [hUinf] using hProdU
  have hFinalS : S.comp (S†) =
      1 - InnerProductSpace.rankOne ℂ a a := by
    simpa [hVinf] using hProdV
  obtain ⟨hunitary, hmap⟩ :=
    add_rankOne_mem_unitary S a b ha hb hInitialS hFinalS
  refine ⟨S, hS, hunitary, hmap, ?_⟩
  intro n
  have hSshell := StronglyConverges.comp_projectionShell_eq
    W U hU hInitial S hS n
  have hbmem : b ∈ ⨅ k, U k := by
    apply (⨅ k, U k).starProjection_eq_self_iff.mp
    rw [hUinf]
    simp [InnerProductSpace.rankOne_apply,
      inner_self_eq_norm_sq_to_K, hb]
  have hbshell : Submodule.projectionShell U n b = 0 := by
    have hball : ∀ k, b ∈ U k := (Submodule.mem_iInf U).mp hbmem
    have hbn : b ∈ U n := hball n
    have hbnext : b ∈ U (n + 1) := hball (n + 1)
    simp [Submodule.projectionShell,
      Submodule.starProjection_eq_self_iff.mpr hbn,
      Submodule.starProjection_eq_self_iff.mpr hbnext]
  have hrank : (InnerProductSpace.rankOne ℂ a b).comp
      (Submodule.projectionShell U n) = 0 := by
    rw [InnerProductSpace.rankOne_comp,
      Submodule.projectionShell_adjoint, hbshell]
    simp
  rw [add_comp, hSshell, hrank, add_zero]

end ContinuousLinearMap
