import MathlibAnnex.Analysis.CStarAlgebra.CAR.Completion
import MathlibAnnex.Analysis.CStarAlgebra.CAR.FiniteTrace
import MathlibAnnex.Analysis.CStarAlgebra.State.Basic

/-!
# The normalized trace on the completed CAR algebra

The compatible finite traces are first defined on the actual algebraic
inductive limit, transported to the metric union, and continuously extended
to its completion. Positivity, traciality and normalization are all proved.
-/

set_option autoImplicit false

open scoped ComplexOrder

namespace MathlibAnnex.CStarAlgebra.CAR

@[simp]
theorem stageTrace_embed (n : ℕ) : ∀ (m : ℕ) (h : n ≤ m) (a : Stage n),
    stageTrace m (embed n m h a) = stageTrace n a := by
  apply Nat.le_induction
  · intro a
    rw [embed_refl]
    rfl
  · intro m h ih a
    rw [embed_succ, StarAlgHom.comp_apply, stageTrace_step, ih]
    exact h

/-- The trace on the algebraic inductive limit. -/
noncomputable def algTraceLinear : AlgCAR →ₗ[ℂ] ℂ :=
  DirectLimit.Module.lift ℂ ℕ Stage (fun _ _ h ↦ embed _ _ h)
    (fun n ↦ (stageTrace n).toLinearMap)
    (fun i j hij a ↦ stageTrace_embed i j hij a)

@[simp]
theorem algTraceLinear_algStageHom (n : ℕ) (a : Stage n) :
    algTraceLinear (algStageHom n a) = stageTrace n a := rfl

/-- The trace on the normed, not yet completed, union. -/
noncomputable def preTraceLinear : PreCAR →ₗ[ℂ] ℂ :=
  algTraceLinear.comp preStarAlgEquiv.toAlgEquiv.toLinearEquiv.toLinearMap

@[simp]
theorem preTraceLinear_stageHom (n : ℕ) (a : Stage n) :
    preTraceLinear (stageHom n a) = stageTrace n a := rfl

theorem norm_preTraceLinear_le (x : PreCAR) : ‖preTraceLinear x‖ ≤ ‖x‖ := by
  obtain ⟨n, a, _, ha, _⟩ := exists_common_stage x x
  rw [← ha, preTraceLinear_stageHom, norm_stageHom]
  exact norm_stageTrace_le n a

/-- The continuous trace on the metric union. -/
noncomputable def preTrace : PreCAR →L[ℂ] ℂ :=
  preTraceLinear.mkContinuous 1 fun x ↦ by
    simpa only [one_mul] using norm_preTraceLinear_le x

@[simp]
theorem preTrace_stageHom (n : ℕ) (a : Stage n) :
    preTrace (stageHom n a) = stageTrace n a := rfl

/-- The normalized trace of the completed CAR algebra. -/
noncomputable def trace : Limit →L[ℂ] ℂ :=
  preTrace.extend (UniformSpace.Completion.toComplL : PreCAR →L[ℂ] Limit)

@[simp]
theorem trace_coe (x : PreCAR) : trace (x : Limit) = preTrace x :=
  ContinuousLinearMap.extend_eq preTrace UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe PreCAR) x

@[simp]
theorem trace_ofStage (n : ℕ) (a : Stage n) : trace (ofStage n a) = stageTrace n a := by
  rw [ofStage_apply, trace_coe, preTrace_stageHom]

theorem norm_trace_le (x : Limit) : ‖trace x‖ ≤ ‖x‖ := by
  refine UniformSpace.Completion.induction_on (α := PreCAR)
    (p := fun x ↦ ‖trace x‖ ≤ ‖x‖) x ?_ ?_
  · exact isClosed_le trace.continuous.norm continuous_norm
  · intro a
    rw [trace_coe, UniformSpace.Completion.norm_coe]
    change ‖preTraceLinear a‖ ≤ ‖a‖
    exact norm_preTraceLinear_le a

@[simp]
theorem trace_one : trace 1 = 1 := by
  calc
    trace 1 = trace (ofStage 0 (1 : Stage 0)) :=
      congrArg trace ((ofStage 0).map_one).symm
    _ = stageTrace 0 1 := trace_ofStage 0 1
    _ = 1 := stageTrace_one 0

private theorem preTrace_star_mul_self_nonneg (x : PreCAR) :
    0 ≤ preTrace (star x * x) := by
  obtain ⟨n, a, _, ha, _⟩ := exists_common_stage x x
  rw [← ha, ← map_star, ← map_mul, preTrace_stageHom]
  exact stageTrace_star_mul_self_nonneg n a

theorem trace_star_mul_self_nonneg (x : Limit) : 0 ≤ trace (star x * x) := by
  refine UniformSpace.Completion.induction_on (α := PreCAR)
    (p := fun x ↦ 0 ≤ trace (star x * x)) x ?_ ?_
  · exact isClosed_le continuous_const
      (trace.continuous.comp (continuous_limit_star.mul continuous_id))
  · intro a
    simpa only [← UniformSpace.Completion.coe_mul, star_coe, trace_coe] using
      preTrace_star_mul_self_nonneg a

theorem trace_nonneg (x : Limit) (hx : 0 ≤ x) : 0 ≤ trace x := by
  obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx
  exact trace_star_mul_self_nonneg y

theorem trace_mem_stateSpace :
    trace ∈ MathlibAnnex.Analysis.CStarAlgebra.stateSpace Limit :=
  ⟨trace_nonneg, trace_one⟩

private theorem preTrace_mul_comm (x y : PreCAR) : preTrace (x * y) = preTrace (y * x) := by
  obtain ⟨n, a, b, ha, hb⟩ := exists_common_stage x y
  rw [← ha, ← hb, ← map_mul, ← map_mul, preTrace_stageHom, preTrace_stageHom]
  exact stageTrace_mul_comm n a b

theorem trace_mul_comm (x y : Limit) : trace (x * y) = trace (y * x) := by
  refine UniformSpace.Completion.induction_on₂ (α := PreCAR) (β := PreCAR)
    (p := fun x y ↦ trace (x * y) = trace (y * x)) x y ?_ ?_
  · apply isClosed_eq <;> fun_prop
  · intro a b
    simpa only [← UniformSpace.Completion.coe_mul, trace_coe] using preTrace_mul_comm a b

@[simp]
theorem trace_rootFlag (n : ℕ) : trace (rootFlag n) = (2 ^ n : ℂ)⁻¹ := by
  rw [rootFlag, trace_ofStage, stageTrace_rootProjection]

/-- The same trace as a positive linear map, for GNS calculations. -/
noncomputable def tracePositive : Limit →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ trace.toLinearMap trace_nonneg

@[simp]
theorem tracePositive_apply (x : Limit) : tracePositive x = trace x := rfl

@[simp]
theorem tracePositive_one : tracePositive 1 = 1 := trace_one

end MathlibAnnex.CStarAlgebra.CAR
