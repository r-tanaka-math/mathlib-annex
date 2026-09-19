import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Subspace

/-!
# Isometric transport from equal Gram kernels

Equal inner products on two densely spanning linear images first identify the
kernels, then identify the quotient ranges, and finally extend uniquely to a
surjective linear isometry.  This keeps well-definedness separate from dense
extension.
-/

set_option autoImplicit false

namespace LinearMap

variable {𝕜 A H K : Type*}
variable [RCLike 𝕜]
variable [AddCommGroup A] [Module 𝕜 A]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

theorem ker_eq_of_inner_eq (p : A →ₗ[𝕜] H) (q : A →ₗ[𝕜] K)
    (hinner : ∀ a b, inner 𝕜 (p a) (p b) = inner 𝕜 (q a) (q b)) :
    LinearMap.ker p = LinearMap.ker q := by
  ext a
  simp only [LinearMap.mem_ker]
  constructor
  · intro ha
    apply (inner_self_eq_zero (𝕜 := 𝕜) (E := K)).mp
    rw [← hinner, ha, inner_zero_left]
  · intro ha
    apply (inner_self_eq_zero (𝕜 := 𝕜) (E := H)).mp
    rw [hinner, ha, inner_zero_left]

/-- The algebraic equivalence of ranges induced by equal Gram kernels. -/
noncomputable def rangeEquivOfInnerEq (p : A →ₗ[𝕜] H) (q : A →ₗ[𝕜] K)
    (hinner : ∀ a b, inner 𝕜 (p a) (p b) = inner 𝕜 (q a) (q b)) :
  LinearMap.range p ≃ₗ[𝕜] LinearMap.range q :=
  p.quotKerEquivRange.symm.trans <|
    (Submodule.quotEquivOfEq (LinearMap.ker p) (LinearMap.ker q)
      (ker_eq_of_inner_eq p q hinner)).trans q.quotKerEquivRange

@[simp]
theorem rangeEquivOfInnerEq_apply (p : A →ₗ[𝕜] H) (q : A →ₗ[𝕜] K)
    (hinner : ∀ a b, inner 𝕜 (p a) (p b) = inner 𝕜 (q a) (q b)) (a : A) :
    rangeEquivOfInnerEq p q hinner
      ⟨p a, LinearMap.mem_range_self p a⟩ =
      ⟨q a, LinearMap.mem_range_self q a⟩ := by
  apply Subtype.ext
  simp [rangeEquivOfInnerEq]

private theorem rangeEquiv_norm (p : A →ₗ[𝕜] H) (q : A →ₗ[𝕜] K)
    (hinner : ∀ a b, inner 𝕜 (p a) (p b) = inner 𝕜 (q a) (q b))
    (x : LinearMap.range p) :
    ‖rangeEquivOfInnerEq p q hinner x‖ = ‖x‖ := by
  obtain ⟨a, ha⟩ := x.prop
  have hx : x = ⟨p a, LinearMap.mem_range_self p a⟩ :=
    Subtype.ext ha.symm
  rw [hx, rangeEquivOfInnerEq_apply]
  change ‖q a‖ = ‖p a‖
  rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜) (q a),
    norm_eq_sqrt_re_inner (𝕜 := 𝕜) (p a), ← hinner]

/-- Equal Gram kernels on dense linear images give a unique unitary transport. -/
theorem existsUnique_linearIsometryEquiv_of_inner_eq
    (p : A →ₗ[𝕜] H) (q : A →ₗ[𝕜] K)
    (hp : DenseRange p) (hq : DenseRange q)
    (hinner : ∀ a b, inner 𝕜 (p a) (p b) = inner 𝕜 (q a) (q b)) :
    ∃! W : H ≃ₗᵢ[𝕜] K, ∀ a, W (p a) = q a := by
  let f := rangeEquivOfInnerEq p q hinner
  let W : H ≃ₗᵢ[𝕜] K := f.extendOfIsometry
    (LinearMap.range p).subtype (LinearMap.range q).subtype
    hp.denseRange_val hq.denseRange_val (rangeEquiv_norm p q hinner)
  have hW : ∀ a, W (p a) = q a := by
    intro a
    simpa [W, f] using LinearEquiv.extendOfIsometry_eq f
      (LinearMap.range p).subtype (LinearMap.range q).subtype
      hp.denseRange_val hq.denseRange_val (rangeEquiv_norm p q hinner)
      ⟨p a, LinearMap.mem_range_self p a⟩
  refine ⟨W, hW, ?_⟩
  intro W' hW'
  apply LinearIsometryEquiv.ext
  intro x
  exact hp.induction_on x (isClosed_eq W'.continuous W.continuous) fun a ↦ by
    rw [hW, hW']

end LinearMap
