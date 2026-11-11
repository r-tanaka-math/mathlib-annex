import Mathlib.Topology.MetricSpace.Equicontinuity
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.CyclicRestriction
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.UnitaryTranslate
import MathlibAnnex.Analysis.CStarAlgebra.State.NonUnitalApproximation
import MathlibAnnex.Analysis.VonNeumannAlgebra.OperatorTopology

/-!
# Approximate units in nondegenerate representations

The original algebra's positive contractive approximate unit converges strongly
to the identity in every nondegenerate representation. The proof uses the
existing common-kernel definition of nondegeneracy, with no cyclicity,
separability, faithful unitization, or nonzero Hilbert-space assumption.

The norm bound is eventual along the approximate-unit filter. A cutoff outside
the unit ball supplies a globally equicontinuous family; it does not change the
net eventually. The convergence locus is a closed linear subspace containing
all represented ranges, and its orthogonal complement is zero by nondegeneracy.
-/

set_option autoImplicit false
noncomputable section

open Filter Set Topology
open scoped CStarAlgebra InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every increasing contractive approximate unit converges strongly to the
identity under a nondegenerate representation. -/
theorem stronglyConverges_of_isIncreasingApproximateUnit
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    {l : Filter A} (hl : l.IsIncreasingApproximateUnit) :
    ContinuousLinearMap.StronglyConverges (fun e : A => pi e) l 1 := by
  classical
  let F : A → H →L[ℂ] H := fun e => if ‖e‖ ≤ 1 then pi e else 0
  have hF : ∀ e : A, ‖F e‖ ≤ 1 := by
    intro e
    by_cases he : ‖e‖ ≤ 1
    · simpa only [F, if_pos he] using (NonUnitalStarAlgHom.norm_apply_le pi e).trans he
    · simp [F, he]
  have hequi : Equicontinuous (fun e : A => (F e : H → H)) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => r) tendsto_id
    intro x y e
    calc
      dist (F e x) (F e y) = ‖F e (x - y)‖ := by rw [dist_eq_norm, map_sub]
      _ ≤ ‖F e‖ * ‖x - y‖ := (F e).le_opNorm (x - y)
      _ ≤ 1 * ‖x - y‖ := mul_le_mul_of_nonneg_right (hF e) (norm_nonneg _)
      _ = dist x y := by rw [one_mul, dist_eq_norm]
  let M : Submodule ℂ H :=
    { carrier := {x | Tendsto (fun e : A => F e x) l (𝓝 x)}
      zero_mem' := by simpa only [Set.mem_setOf_eq, map_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : A => (0 : H)) l (𝓝 0))
      add_mem' := by
        intro x y hx hy
        simpa only [Set.mem_setOf_eq, map_add] using hx.add hy
      smul_mem' := by
        intro c x hx
        simpa only [Set.mem_setOf_eq, map_smul] using (tendsto_const_nhds (x := c)).smul hx }
  have hclosed : IsClosed (M : Set H) :=
    hequi.isClosed_setOfPred_tendsto (continuous_id : Continuous (fun x : H => x))
  letI : IsClosed (M : Set H) := hclosed
  letI : CompleteSpace M := inferInstance
  have hmem (a : A) (x : H) : pi a x ∈ M := by
    change Tendsto (fun e : A => F e (pi a x)) l (𝓝 (pi a x))
    have h := (orbitMap pi x).continuous.continuousAt.tendsto.comp
      (hl.tendsto_mul_right a)
    apply h.congr'
    filter_upwards [hl.eventually_norm] with e he
    simp only [Function.comp_apply, orbitMap_apply, map_mul, ContinuousLinearMap.mul_apply, F, if_pos he]
  have horth (z : H) (hz : z ∈ Mᗮ) : z = 0 := by
    apply hnd z
    intro a
    have h := Submodule.inner_right_of_mem_orthogonal (K := M)
      (hmem (star a) (pi a z)) hz
    rw [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left] at h
    exact (inner_self_eq_zero (𝕜 := ℂ)).mp h
  intro x
  have hx : x ∈ M := by
    have hz := horth (x - M.starProjection x) (M.sub_starProjection_mem_orthogonal x)
    exact M.starProjection_eq_self_iff.mp (sub_eq_zero.mp hz).symm
  change Tendsto (fun e : A => pi e x) l (𝓝 x)
  change Tendsto (fun e : A => F e x) l (𝓝 x) at hx
  apply hx.congr'
  filter_upwards [hl.eventually_norm] with e he
  simp only [F, if_pos he]

/-- The canonical approximate unit of the original algebra converges to the
identity on every vector of a nondegenerate represented Hilbert space. -/
theorem stronglyConverges_approximateUnit
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    ContinuousLinearMap.StronglyConverges (fun e : A => pi e)
      (_root_.CStarAlgebra.approximateUnit A) 1 :=
  stronglyConverges_of_isIncreasingApproximateUnit pi hnd
    (_root_.CStarAlgebra.increasingApproximateUnit A)

private theorem unitization_mul_original
    (pi : NonUnitalCStarRepresentation A H) (z : Unitization ℂ A) (e : A) :
    pi.unitization z * pi e = pi (z.fst • e + z.snd * e) := by
  calc
    pi.unitization z * pi e =
        pi.unitization z * pi.unitization (Unitization.inr e) := by rw [unitization_inr]
    _ = pi.unitization (z * Unitization.inr e) := by rw [map_mul]
    _ = pi.unitization (Unitization.inr (unitizationLeftMul z e)) := by
      rw [inr_unitizationLeftMul]
    _ = pi (z.fst • e + z.snd * e) := by
      rw [unitization_inr, unitizationLeftMul_apply]

/-- Unitization adds no points to the strong closure of the original range
in a nondegenerate representation. The approximants are actual elements of
the original algebra: `z.fst • e + z.snd * e`. -/
theorem unitization_mem_sotClosure_range
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (z : Unitization ℂ A) :
    ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
      (pi.unitization z) ∈
        closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
          Set.range pi) := by
  have hstrong := (stronglyConverges_approximateUnit pi hnd).comp_left (pi.unitization z)
  have hstrong' : ContinuousLinearMap.StronglyConverges
      (fun e : A => pi (z.fst • e + z.snd * e))
      (_root_.CStarAlgebra.approximateUnit A) (pi.unitization z) := by
    change ContinuousLinearMap.StronglyConverges
      (fun e : A => pi.unitization z * pi e)
      (_root_.CStarAlgebra.approximateUnit A) (pi.unitization z * 1) at hstrong
    simpa only [unitization_mul_original, mul_one] using hstrong
  apply mem_closure_of_tendsto
    (ContinuousLinearMap.stronglyConverges_iff_tendsto_pointwiseConvergenceCLM.mp hstrong')
  exact Eventually.of_forall fun e =>
    ⟨pi (z.fst • e + z.snd * e), ⟨z.fst • e + z.snd * e, rfl⟩, rfl⟩

/-- The same original-algebra approximants converge weakly. -/
theorem unitization_mem_wotClosure_range
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (z : Unitization ℂ A) :
    ContinuousLinearMapWOT.ofCLM (pi.unitization z) ∈
      closure (ContinuousLinearMapWOT.ofCLM '' Set.range pi) := by
  have h := mem_closure_image
    (PointwiseConvergenceCLM.toWOT ℂ H H).continuous.continuousAt
    (unitization_mem_sotClosure_range pi hnd z)
  have hcomp : (fun T : H →L[ℂ] H => PointwiseConvergenceCLM.toWOT ℂ H H
      (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H T)) =
      ContinuousLinearMapWOT.ofCLM := rfl
  rw [Set.image_image, hcomp] at h
  exact h

/-- Strong closures of the original and same-space unitized ranges agree. -/
theorem sotClosure_range_unitization
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
      Set.range pi.unitization) =
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
      Set.range pi) := by
  apply le_antisymm
  · apply closure_minimal _ isClosed_closure
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact unitization_mem_sotClosure_range pi hnd z
  · apply closure_mono
    apply Set.image_mono
    rintro _ ⟨a, rfl⟩
    exact ⟨Unitization.inr a, unitization_inr pi a⟩

/-- Weak closures of the original and same-space unitized ranges agree. -/
theorem wotClosure_range_unitization
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    closure (ContinuousLinearMapWOT.ofCLM '' Set.range pi.unitization) =
      closure (ContinuousLinearMapWOT.ofCLM '' Set.range pi) := by
  apply le_antisymm
  · apply closure_minimal _ isClosed_closure
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact unitization_mem_wotClosure_range pi hnd z
  · apply closure_mono
    apply Set.image_mono
    rintro _ ⟨a, rfl⟩
    exact ⟨Unitization.inr a, unitization_inr pi a⟩

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
