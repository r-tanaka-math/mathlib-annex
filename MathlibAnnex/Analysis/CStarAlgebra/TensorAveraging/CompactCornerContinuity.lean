import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.CentralKernelSection

/-!
# Weak continuity of the constructed corner section on bounded nets

Compactness and uniqueness in the corner give weak convergence of section
values. This is not a claim that arbitrary weakly convergent nets have a
common norm bound, and not an unproved upgrade to global weak-star
continuity. Every boundedness and compactness premise is visible.
C02 proof-source candidate; unbuilt.
-/
set_option autoImplicit false
noncomputable section
open Filter Topology

namespace MathlibAnnex.CentralKernelSection

universe u v w z t
variable {M : Type u} [CStarAlgebra M]
variable {N : Type v} [CStarAlgebra N]
variable {q : M →⋆ₐ[ℂ] N} (s : KernelSupport q)
variable (hball : ∀ y : N, ∃ x : M, q x = y ∧ ‖x‖ ≤ ‖y‖)

/-- On an explicitly bounded net, compactness upgrades quotient convergence
to convergence of the uniquely projected section values. -/
theorem tendsto_value_of_bounded
    {W : Type w} [TopologicalSpace W] [T2Space W]
    {V : Type z} [TopologicalSpace V] [T2Space V]
    (j : M ≃ W) (c : N → V) (hc : Function.Injective c)
    (hcompact : ∀ r : ℝ, IsCompact (j '' Metric.closedBall (0 : M) r))
    (hp : Continuous (fun w : W => j (s.projection * j.symm w)))
    (hq : Continuous (fun w : W => c (q (j.symm w))))
    {ι : Type t} (l : Filter ι) (f : ι → N) (y : N)
    (ht : Tendsto (fun i => c (f i)) l (𝓝 (c y)))
    (r : ℝ) (hr : ∀ᶠ i in l, ‖f i‖ ≤ r) :
    Tendsto (fun i => j (s.value hball (f i))) l (𝓝 (j (s.value hball y))) := by
  let S : Set W := (j '' Metric.closedBall (0 : M) r) ∩
    {w | j (s.projection * j.symm w) = w}
  have hS : IsCompact S := (hcompact r).inter_right (isClosed_eq hp continuous_id)
  let a : ι → W := fun i => j (s.value hball (f i))
  have ha : ∀ᶠ i in l, a i ∈ S := by
    filter_upwards [hr] with i hi
    refine ⟨⟨s.value hball (f i), ?_, rfl⟩, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right] using
        (s.value_norm_le hball (f i)).trans hi
    · change j (s.projection * j.symm (a i)) = a i
      simp only [a, Equiv.symm_apply_apply, projection_value]
  apply hS.tendsto_nhds_of_unique_mapClusterPt ha
  intro w hw hcluster
  let K : Filter W := 𝓝 w ⊓ Filter.map a l
  letI : NeBot K := hcluster
  have hmap : Tendsto (fun z : W => c (q (j.symm z))) (Filter.map a l) (𝓝 (c y)) := by
    change Filter.map (fun z : W => c (q (j.symm z))) (Filter.map a l) ≤ _
    rw [Filter.map_map]
    change Filter.map (fun i => c (f i)) l ≤ _ at ht
    simpa only [Function.comp_def, a, Equiv.symm_apply_apply, q_value] using ht
  have hcand : Tendsto (fun z : W => c (q (j.symm z))) K (𝓝 (c (q (j.symm w)))) :=
    hq.continuousAt.tendsto.mono_left inf_le_left
  have heq : q (j.symm w) = y :=
    hc (tendsto_nhds_unique hcand (hmap.mono_left inf_le_right))
  have hfixed : s.projection * j.symm w = j.symm w := by
    apply j.injective
    simpa only [Set.mem_setOf_eq, Equiv.apply_symm_apply] using hw.2
  have hunique : j.symm w = s.value hball y := by
    apply s.corner_injective hfixed (s.projection_value hball y)
    simpa only [q_value] using heq
  simpa only [Equiv.apply_symm_apply] using congrArg j hunique

end MathlibAnnex.CentralKernelSection
