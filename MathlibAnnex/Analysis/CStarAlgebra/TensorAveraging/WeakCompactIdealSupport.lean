import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith

/-!
# Constructing the central identity of a weakly closed two-sided ideal

A contractive approximate identity of the closed C*-ideal has a cluster
point in the compact weak unit ball. Separate continuity proves that this
point is an identity on the ideal. Its centrality and self-adjointness
then follow algebraically; neither is a premise.

The weak topology is carried by a separate type `W`. This avoids replacing
the norm topology or silently installing a second C*-algebra structure on
C01's raw Banach bidual. The generic construction is complete below; the
specific C01 bidual's C*-realization and weak multiplication laws remain
separate controller obligations. C02 unbuilt proof-source candidate.
-/
set_option autoImplicit false
noncomputable section
open Filter Topology

namespace MathlibAnnex.WeakCompactIdealSupport

universe u v w
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

/-- The identity is constructed, not passed in as a projection argument.
Only the two-sided ideal and the stated weak topological properties are
inputs. The ideal is allowed to be zero or the whole algebra. -/
theorem exists_central_identity
    (J : NonUnitalStarSubalgebra ℂ M)
    (ideal_left : ∀ a x : M, x ∈ J → a * x ∈ J)
    (ideal_right : ∀ x a : M, x ∈ J → x * a ∈ J)
    {W : Type v} [TopologicalSpace W] [T2Space W]
    (j : M ≃ W) (hj : Continuous j)
    (hball : IsCompact (j '' Metric.closedBall (0 : M) 1))
    (hJ : IsClosed (j '' (J : Set M)))
    (hleft : ∀ a : M, Continuous (fun w : W => j (a * j.symm w)))
    (hright : ∀ a : M, Continuous (fun w : W => j (j.symm w * a))) :
    ∃ e : M, e ∈ J ∧ ‖e‖ ≤ 1 ∧ star e = e ∧ e * e = e ∧
      (∀ a : M, e * a = a * e) ∧
      (∀ x ∈ J, e * x = x ∧ x * e = x) := by
  have hclosed : IsClosed (J : Set M) := by
    convert hJ.preimage hj using 1
    ext x
    simp
  letI : IsClosed (J : Set M) := hclosed
  letI : PartialOrder J := CStarAlgebra.spectralOrder J
  letI : StarOrderedRing J := CStarAlgebra.spectralOrderedRing J
  let l : Filter J := CStarAlgebra.approximateUnit J
  have hu := CStarAlgebra.increasingApproximateUnit J
  letI : NeBot l := hu.toIsApproximateUnit.neBot
  let u : J → W := fun x => j (x : M)
  let L : Filter W := Filter.map u l
  let S : Set W := (j '' Metric.closedBall (0 : M) 1) ∩ j '' (J : Set M)
  have hS : IsCompact S := hball.inter_right hJ
  have hLS : L ≤ 𝓟 S := by
    apply Filter.le_principal_iff.mpr
    change ∀ᶠ x : J in l, u x ∈ S
    filter_upwards [hu.eventually_norm] with x hx
    exact ⟨⟨(x : M), by simpa using hx, rfl⟩, ⟨(x : M), x.property, rfl⟩⟩
  obtain ⟨w, hw, hcluster⟩ := hS.exists_clusterPt hLS
  let e : M := j.symm w
  have heJ : e ∈ J := by
    obtain ⟨x, hx, hxw⟩ := hw.2
    have : x = e := by simpa [e] using congrArg j.symm hxw
    simpa [this] using hx
  have henorm : ‖e‖ ≤ 1 := by
    obtain ⟨x, hx, hxw⟩ := hw.1
    have : x = e := by simpa [e] using congrArg j.symm hxw
    simpa [this] using hx
  let K : Filter W := 𝓝 w ⊓ L
  letI : NeBot K := hcluster
  have hId : ∀ x ∈ J, e * x = x ∧ x * e = x := by
    intro x hx
    let xJ : J := ⟨x, hx⟩
    have hucont : Continuous u := hj.comp continuous_subtype_val
    have hRnorm : Tendsto (fun y : J => j ((y : M) * x)) l (𝓝 (j x)) := by
      simpa [l, u, xJ, Function.comp_def] using
        hucont.continuousAt.tendsto.comp (hu.tendsto_mul_right xJ)
    have hLnorm : Tendsto (fun y : J => j (x * (y : M))) l (𝓝 (j x)) := by
      simpa [l, u, xJ, Function.comp_def] using
        hucont.continuousAt.tendsto.comp (hu.tendsto_mul_left xJ)
    have hRmap : Tendsto (fun z : W => j (j.symm z * x)) L (𝓝 (j x)) := by
      change Filter.map (fun z : W => j (j.symm z * x)) (Filter.map u l) ≤ _
      rw [Filter.map_map]
      change Tendsto ((fun z : W => j (j.symm z * x)) ∘ u) l (𝓝 (j x))
      simpa only [Function.comp_def, u, Equiv.symm_apply_apply] using hRnorm
    have hLmap : Tendsto (fun z : W => j (x * j.symm z)) L (𝓝 (j x)) := by
      change Filter.map (fun z : W => j (x * j.symm z)) (Filter.map u l) ≤ _
      rw [Filter.map_map]
      change Tendsto ((fun z : W => j (x * j.symm z)) ∘ u) l (𝓝 (j x))
      simpa only [Function.comp_def, u, Equiv.symm_apply_apply] using hLnorm
    have hRlimit : Tendsto (fun z : W => j (j.symm z * x)) K (𝓝 (j (e * x))) :=
      (hright x).continuousAt.tendsto.mono_left inf_le_left
    have hLlimit : Tendsto (fun z : W => j (x * j.symm z)) K (𝓝 (j (x * e))) :=
      (hleft x).continuousAt.tendsto.mono_left inf_le_left
    exact ⟨j.injective (tendsto_nhds_unique hRlimit (hRmap.mono_left inf_le_right)),
      j.injective (tendsto_nhds_unique hLlimit (hLmap.mono_left inf_le_right))⟩
  have hee : e * e = e := (hId e heJ).1
  have hstar : star e = e := by
    have h := (hId (star e) (J.star_mem' heJ)).1
    have hs := congrArg star h
    have hs' : e * star e = e := by
      simpa only [star_mul, star_star] using hs
    exact h.symm.trans hs'
  have hcentral : ∀ a : M, e * a = a * e := by
    intro a
    calc
      e * a = (e * a) * e := (hId (e * a) (ideal_right e a heJ)).2.symm
      _ = e * (a * e) := mul_assoc _ _ _
      _ = a * e := (hId (a * e) (ideal_left a e heJ)).1
  exact ⟨e, heJ, henorm, hstar, hee, hcentral, hId⟩

/-- The complementary central projection and the precise annihilator
characterization. These conclusions are algebraic, independent of topology. -/
theorem complement_properties
    (J : NonUnitalStarSubalgebra ℂ M)
    (ideal_left : ∀ a x : M, x ∈ J → a * x ∈ J)
    (e : M) (heJ : e ∈ J) (he : star e = e) (hee : e * e = e)
    (hc : ∀ a : M, e * a = a * e)
    (hid : ∀ x ∈ J, e * x = x) :
    star (1 - e) = 1 - e ∧ (1 - e) * (1 - e) = 1 - e ∧
      (∀ a : M, (1 - e) * a = a * (1 - e)) ∧
      ‖1 - e‖ ≤ 1 ∧ (∀ x : M, x ∈ J ↔ (1 - e) * x = 0) := by
  have hpstar : star (1 - e) = 1 - e := by simp [he]
  have hpp : (1 - e) * (1 - e) = 1 - e := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hee]
    abel
  have hpc : ∀ a : M, (1 - e) * a = a * (1 - e) := by
    intro a
    simp only [sub_mul, mul_sub, one_mul, mul_one, hc]
  have hpn : ‖1 - e‖ ≤ 1 := by
    have hn := CStarRing.norm_star_mul_self (x := (1 - e))
    rw [hpstar, hpp] at hn
    nlinarith [norm_nonneg (1 - e)]
  refine ⟨hpstar, hpp, hpc, hpn, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    simp only [sub_mul, one_mul, hid x hx, sub_self]
  · intro hx
    have hex : x = e * x := by
      simpa only [sub_mul, one_mul, sub_eq_zero] using hx
    rw [hex, hc]
    exact ideal_left x e heJ

/-- Banach--Alaoglu supplies the compact-ball input for an actual isometric
predual realization; the separate multiplication hypotheses stay explicit. -/
theorem isCompact_predual_unitBall
    {X : Type w} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (k : M ≃ₗᵢ[ℂ] StrongDual ℂ X) :
    IsCompact ((fun x : M => StrongDual.toWeakDual (k x)) '' Metric.closedBall 0 1) := by
  have heq : ((fun x : M => StrongDual.toWeakDual (k x)) '' Metric.closedBall 0 1) =
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ X) 1 := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
        StrongDual.toStrongDual_toWeakDual, k.norm_map] using hx
    · intro hw
      refine ⟨k.symm (WeakDual.toStrongDual w), ?_, ?_⟩
      · simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
          k.symm.norm_map] using hw
      · simp
  rw [heq]
  exact WeakDual.isCompact_closedBall _ _

end MathlibAnnex.WeakCompactIdealSupport
