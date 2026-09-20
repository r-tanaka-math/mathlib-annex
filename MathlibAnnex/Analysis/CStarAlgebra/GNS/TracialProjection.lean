import MathlibAnnex.Analysis.CStarAlgebra.Representation.Cyclic
import MathlibAnnex.Analysis.CStarAlgebra.Representation.VectorFunctional
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Vanishing projection flags in a tracial cyclic subspace

A trace estimate is first established on every source-orbit vector. The
limiting projection is then shown to vanish on the closed source-cyclic
subspace. The ambient representation need not be tracial or cyclic.
-/

set_option autoImplicit false

open Filter Topology
open scoped ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Cyclicity is not needed for the projection estimate; agreement of the
vector functional with the tracial positive functional suffices. -/
theorem norm_sq_projection_orbit_le (τ : A →ₚ[ℂ] ℂ)
    (hτ : ∀ a b, τ (a * b) = τ (b * a))
    (σ : Representation A H) (ξ : H)
    (hξ : ∀ a, Representation.vectorFunctional σ ξ a = τ a)
    (p : A) (hp : IsStarProjection p) (r : ℝ) (hr : τ p = (r : ℂ))
    (b : A) : ‖σ p (σ b ξ)‖ ^ 2 ≤ ‖b‖ ^ 2 * r := by
  have hsquare : star (p * b) * (p * b) = star b * p * b := by
    calc
      star (p * b) * (p * b) = (star b * p) * (p * b) := by
        rw [star_mul, hp.isSelfAdjoint.star_eq]
      _ = star b * ((p * p) * b) := by simp only [mul_assoc]
      _ = star b * (p * b) := by rw [hp.isIdempotentElem.eq]
      _ = star b * p * b := (mul_assoc _ _ _).symm
  have hnorm : τ (star b * p * b) = ((‖σ p (σ b ξ)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hsquare, ← hξ, Representation.vectorFunctional_star_mul,
      inner_self_eq_norm_sq_to_K, map_mul]
    simp only [mul_apply_eq_comp]
    norm_cast
  have hcyclic : τ (star b * p * b) = τ (p * (b * star b) * p) := by
    calc
      τ (star b * p * b) = τ (star b * (p * b)) := by rw [mul_assoc]
      _ = τ (star b * ((p * p) * b)) := by rw [hp.isIdempotentElem.eq]
      _ = τ ((star b * p) * (p * b)) := by simp only [mul_assoc]
      _ = τ ((p * b) * (star b * p)) := hτ _ _
      _ = τ (p * (b * star b) * p) := by simp only [mul_assoc]
  have horder : p * (b * star b) * p ≤ ‖b‖ ^ 2 • p := by
    have h := CStarAlgebra.star_left_conjugate_le_norm_smul
      (a := p) (b := b * star b) (IsSelfAdjoint.mul_star_self b)
    simpa only [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq,
      CStarRing.norm_self_mul_star, sq] using h
  have hbound := OrderHomClass.mono τ horder
  have hscalar : τ (‖b‖ ^ 2 • p) = ((‖b‖ ^ 2 * r : ℝ) : ℂ) := by
    rw [← Complex.coe_smul, map_smul, hr]
    simp only [smul_eq_mul, Complex.ofReal_mul]
  rw [← hcyclic, hnorm, hscalar] at hbound
  have hre := (RCLike.nonneg_iff.mp (sub_nonneg.mpr hbound)).1
  change 0 ≤ Complex.re
    (((‖b‖ ^ 2 * r : ℝ) : ℂ) - ((‖σ p (σ b ξ)‖ ^ 2 : ℝ) : ℂ)) at hre
  simpa only [Complex.sub_re, Complex.ofReal_re, sub_nonneg] using hre

/-- A square-norm bound tending to zero gives vectorwise convergence. -/
theorem tendsto_zero_of_norm_sq_le {E : Type*} [SeminormedAddCommGroup E]
    (x : ℕ → E) (c : ℝ) (r : ℕ → ℝ)
    (hbound : ∀ n, ‖x n‖ ^ 2 ≤ c * r n)
    (hr : Tendsto r atTop (nhds 0)) : Tendsto x atTop (nhds 0) := by
  have hsquare : Tendsto (fun n ↦ ‖x n‖ ^ 2) atTop (nhds 0) :=
    squeeze_zero (fun n ↦ sq_nonneg _) hbound
      (by simpa only [mul_zero] using tendsto_const_nhds.mul hr)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_order.mp hsquare).2 (ε ^ 2) (sq_pos_of_pos hε))
  refine ⟨N, fun n hn ↦ ?_⟩
  have h := hN n hn
  rw [dist_zero_right]
  nlinarith [norm_nonneg (x n)]

theorem tendsto_projection_orbit_zero (τ : A →ₚ[ℂ] ℂ)
    (hτ : ∀ a b, τ (a * b) = τ (b * a))
    (σ : Representation A H) (ξ : H)
    (hξ : ∀ a, Representation.vectorFunctional σ ξ a = τ a)
    (p : ℕ → A) (hp : ∀ n, IsStarProjection (p n))
    (r : ℕ → ℝ) (hvalue : ∀ n, τ (p n) = (r n : ℂ))
    (hr : Tendsto r atTop (nhds 0)) (b : A) :
    Tendsto (fun n ↦ σ (p n) (σ b ξ)) atTop (nhds 0) :=
  tendsto_zero_of_norm_sq_le _ (‖b‖ ^ 2) r
    (fun n ↦ norm_sq_projection_orbit_le τ hτ σ ξ hξ (p n) (hp n) (r n)
      (hvalue n) b) hr

/-- A projection onto the common range is fixed by every projection in the
flag. This is a finite operator identity, not a continuity assertion. -/
theorem projection_mul_eq_self_of_range_eq_iInf
    (Q : ℕ → H →L[ℂ] H) (hQ : ∀ n, IsStarProjection (Q n))
    (P : H →L[ℂ] H) (hP : IsStarProjection P)
    (hrange : P.range = ⨅ n, (Q n).range) (n : ℕ) :
    Q n * P = P ∧ P * Q n = P := by
  have hleft : Q n * P = P := by
    apply ContinuousLinearMap.ext
    intro x
    have hx : P x ∈ (Q n).range := by
      have hmem : P x ∈ P.range := ⟨x, rfl⟩
      rw [hrange] at hmem
      exact (Submodule.mem_iInf (fun n ↦ (Q n).range)).mp hmem n
    obtain ⟨y, hy⟩ := hx
    change Q n (P x) = P x
    rw [← hy]
    exact congrArg (fun T : H →L[ℂ] H ↦ T y) (hQ n).isIdempotentElem.eq
  refine ⟨hleft, ?_⟩
  have h := congrArg star hleft
  simpa only [star_mul, hP.isSelfAdjoint.star_eq, (hQ n).isSelfAdjoint.star_eq] using h

/-- The common-range projection kills the whole closed source-cyclic
subspace once the flag tends to zero on each source-orbit vector. -/
theorem projection_eq_zero_on_cyclicSubspace
    (σ : Representation A H) (ξ : H) (p : ℕ → A)
    (hp : ∀ n, IsStarProjection (p n))
    (hzero : ∀ b, Tendsto (fun n ↦ σ (p n) (σ b ξ)) atTop (nhds 0))
    (P : H →L[ℂ] H) (hP : IsStarProjection P)
    (hrange : P.range = ⨅ n, (σ (p n)).range) :
    ∀ x ∈ Representation.cyclicSubspace σ ξ, P x = 0 := by
  have hPe (n : ℕ) : P * σ (p n) = P :=
    (projection_mul_eq_self_of_range_eq_iInf (fun n ↦ σ (p n))
      (fun n ↦ (hp n).map σ) P hP hrange n).2
  have horbit (b : A) : P (σ b ξ) = 0 := by
    have hlim : Tendsto (fun n ↦ P (σ (p n) (σ b ξ))) atTop (nhds 0) := by
      change Tendsto (P ∘ fun n ↦ σ (p n) (σ b ξ)) atTop (nhds 0)
      simpa only [map_zero] using (P.continuous.tendsto 0).comp (hzero b)
    have heq : (fun n ↦ P (σ (p n) (σ b ξ))) = fun _n : ℕ ↦ P (σ b ξ) := by
      funext n
      change (P * σ (p n)) (σ b ξ) = P (σ b ξ)
      rw [hPe n]
    rw [heq] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  have hclosed : IsClosed {x : H | P x = 0} :=
    isClosed_eq P.continuous continuous_const
  intro x hx
  have hx' : x ∈ closure (Set.range (Representation.orbitLinearMap σ ξ)) := by
    change x ∈ (Representation.cyclicSubspace σ ξ : Set H) at hx
    simpa only [Representation.cyclicSubspace, Submodule.topologicalClosure_coe,
      LinearMap.coe_range] using hx
  apply closure_minimal (t := {x : H | P x = 0}) _ hclosed hx'
  rintro _ ⟨b, rfl⟩
  exact horbit b

end MathlibAnnex.Analysis.CStarAlgebra
