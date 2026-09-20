import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.CStarBidualTopology
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.WeakStarQuotientCorner
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.CompactCornerContinuity

/-!
# The central corner for an actual irreducible representation

This instantiates the C02 support theorem with the C03 *constructed* C*-bidual,
its *fixed* Banach predual, its proved two weak multiplication laws, and the
actual represented quotient. Neither a central projection nor a section is an
input. The non-unital embedding into the whole bidual sends 1 to the central
support p, not to 1. Bounded-net weak continuity is proved and used as such.
C03 controller proof-source candidate, not compiled.
-/
set_option autoImplicit false
noncomputable section
open Filter Topology

namespace MathlibAnnex.RepresentedCentralCorner
open MathlibAnnex.CStarBidual MathlibAnnex.CentralKernelSection
universe u v t
variable {A : Type u} [CStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]
variable (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)

/-- Every premise to the earlier abstract support theorem is now supplied. -/
def support : KernelSupport (quotient pi) :=
  Classical.choice (MathlibAnnex.WeakStarQuotientCorner.nonempty_kernelSupport
    (quotient pi) (Model.toRaw A)
    (fun F => weak_mul_left F) (fun F => weak_mul_right F)
    ContinuousLinearMapWOT.ofCLM ContinuousLinearMapWOT.ofCLM_injective
    (quotient_weakStar_wot pi))

/-- The actual norm-controlled quotient lifting theorem. -/
theorem ball_lifting (hpi : StarAlgHom.IsIrreducible pi) (T : H →L[ℂ] H) :
    ∃ F : Model A, quotient pi F = T ∧ ‖F‖ ≤ ‖T‖ :=
  quotient_preimage pi hpi T

def projection : Model A := (support pi).projection

include hpi in
def sectionMap : (H →L[ℂ] H) →L[ℂ] Model A :=
  (support pi).sectionCLM (ball_lifting pi hpi)

include hpi in
def sectionHom : (H →L[ℂ] H) →⋆ₙₐ[ℂ] Model A :=
  (support pi).sectionHom (ball_lifting pi hpi)

@[simp] theorem sectionHom_apply (T : H →L[ℂ] H) :
    sectionHom pi hpi T = sectionMap pi hpi T := rfl

@[simp] theorem projection_star : star (projection pi) = projection pi :=
  (support pi).projection_star
@[simp] theorem projection_idem : projection pi * projection pi = projection pi :=
  (support pi).projection_idem

theorem projection_central (F : Model A) : projection pi * F = F * projection pi :=
  (support pi).projection_central F

@[simp] theorem quotient_projection : quotient pi (projection pi) = 1 :=
  (support pi).q_projection

@[simp] theorem section_one : sectionMap pi hpi 1 = projection pi :=
  (support pi).value_one (ball_lifting pi hpi)

@[simp] theorem quotient_section (T : H →L[ℂ] H) :
    quotient pi (sectionMap pi hpi T) = T := (support pi).q_value (ball_lifting pi hpi) T

@[simp] theorem norm_section (T : H →L[ℂ] H) :
    ‖sectionMap pi hpi T‖ = ‖T‖ := (support pi).value_norm (ball_lifting pi hpi) T

theorem isometry_section : Isometry (sectionMap pi hpi) := by
  apply Isometry.of_dist_eq
  intro T U
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_section]

@[simp] theorem section_mul (T U : H →L[ℂ] H) :
    sectionMap pi hpi (T * U) = sectionMap pi hpi T * sectionMap pi hpi U :=
  (support pi).value_mul (ball_lifting pi hpi) T U

@[simp] theorem section_star (T : H →L[ℂ] H) :
    sectionMap pi hpi (star T) = star (sectionMap pi hpi T) :=
  (support pi).value_star (ball_lifting pi hpi) T

@[simp] theorem projection_section (T : H →L[ℂ] H) :
    projection pi * sectionMap pi hpi T = sectionMap pi hpi T :=
  (support pi).projection_value (ball_lifting pi hpi) T

@[simp] theorem section_quotient (F : Model A) :
    sectionMap pi hpi (quotient pi F) = projection pi * F :=
  (support pi).value_quotient (ball_lifting pi hpi) F

/-- Exact central-corner description of the section's range. -/
theorem range_section :
    Set.range (sectionMap pi hpi) = {F : Model A | projection pi * F = F} := by
  ext F
  constructor
  · rintro ⟨T, rfl⟩
    exact projection_section pi hpi T
  · intro hF
    exact ⟨quotient pi F, (section_quotient pi hpi F).trans hF⟩

/-- The quotient kernel is exactly the complementary central summand. -/
theorem kernel_iff (F : Model A) :
    quotient pi F = 0 ↔ projection pi * F = 0 := by
  constructor
  · exact (support pi).projection_mul_kernel F
  · intro hF
    have h := congrArg (quotient pi) hF
    simpa only [map_mul, quotient_projection, one_mul, map_zero] using h

/-- Actual covariance needed for tensor-test pullback. -/
theorem left_covariance (a : A) (T : H →L[ℂ] H) :
    sectionMap pi hpi (pi a * T) = Model.canonical A a * sectionMap pi hpi T := by
  simpa only [sectionMap, KernelSupport.sectionCLM_apply, quotient_canonical] using
    (support pi).value_left_covariance (ball_lifting pi hpi) (Model.canonical A a) T

theorem right_covariance (a : A) (T : H →L[ℂ] H) :
    sectionMap pi hpi (T * pi a) = sectionMap pi hpi T * Model.canonical A a := by
  simpa only [sectionMap, KernelSupport.sectionCLM_apply, quotient_canonical] using
    (support pi).value_right_covariance (ball_lifting pi hpi) (Model.canonical A a) T

/-- A bounded-linear adapter into the exact old raw-bidual carrier. -/
def rawSection : (H →L[ℂ] H) →L[ℂ] StrongDual ℂ (StrongDual ℂ A) :=
  (Model.toRaw A).toContinuousLinearEquiv.toContinuousLinearMap.comp (sectionMap pi hpi)

@[simp] theorem rawSection_apply (T : H →L[ℂ] H) :
    rawSection pi hpi T = Model.toRaw A (sectionMap pi hpi T) := rfl

@[simp] theorem norm_rawSection (T : H →L[ℂ] H) : ‖rawSection pi hpi T‖ = ‖T‖ := by
  rw [rawSection_apply, (Model.toRaw A).norm_map, norm_section]

/-- All weakly convergent nets are NOT asserted to be bounded. The actual
norm bound is an explicit hypothesis, precisely as required downstream. -/
theorem tendsto_section_of_bounded {ι : Type t} (l : Filter ι)
    (T : ι → H →L[ℂ] H) (U : H →L[ℂ] H)
    (hT : Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (T i)) l
      (𝓝 (ContinuousLinearMapWOT.ofCLM U)))
    (r : ℝ) (hr : ∀ᶠ i in l, ‖T i‖ ≤ r) :
    Tendsto (fun i => weak (sectionMap pi hpi (T i))) l
      (𝓝 (weak (sectionMap pi hpi U))) :=
  tendsto_value_of_bounded (support pi) (ball_lifting pi hpi)
    weak ContinuousLinearMapWOT.ofCLM ContinuousLinearMapWOT.ofCLM_injective
    isCompact_weak_closedBall (weak_mul_left (projection pi)) (quotient_weakStar_wot pi)
    l T U hT r hr

/-- Every actual source predual test is continuous along the same bounded
operator net, with the same section and no test-dependent lift. -/
theorem tendsto_evaluation_section {ι : Type t} (l : Filter ι)
    (T : ι → H →L[ℂ] H) (U : H →L[ℂ] H)
    (hT : Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (T i)) l
      (𝓝 (ContinuousLinearMapWOT.ofCLM U)))
    (r : ℝ) (hr : ∀ᶠ i in l, ‖T i‖ ≤ r) (f : StrongDual ℂ A) :
    Tendsto (fun i => rawSection pi hpi (T i) f) l
      (𝓝 (rawSection pi hpi U f)) :=
  (WeakDual.eval_continuous f).continuousAt.tendsto.comp
    (tendsto_section_of_bounded pi hpi l T U hT r hr)

end MathlibAnnex.RepresentedCentralCorner
