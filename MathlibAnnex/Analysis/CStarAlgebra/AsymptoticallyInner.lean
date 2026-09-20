import MathlibAnnex.Analysis.CStarAlgebra.ApproximateIntertwining
import MathlibAnnex.Topology.MetricSpace.DenseCauchy
import Mathlib.Topology.Algebra.Star.Unitary

/-!
# Asymptotically inner automorphisms with a path from one

This file records the start-at-one (`AInn₀`) notion independently of any
particular C-star algebra construction.  Negative-time constancy is not part
of the predicate; only continuity on `ℝ`, the value at zero, and the
point-norm limit at `+∞` are required.
-/

set_option autoImplicit false

open Filter

namespace MathlibAnnex.CStarAlgebra

variable {A : Type*} [CStarAlgebra A]

/-- Point-norm asymptotic innerness implemented by a continuous unitary path
starting at the identity. -/
def IsAsymptoticallyInnerFromOne (alpha : A ≃⋆ₐ[ℂ] A) : Prop :=
  ∃ U : ℝ → unitary A, Continuous U ∧ U 0 = 1 ∧
    ∀ a : A, Tendsto (fun t ↦ Unitary.conjStarAlgAut ℂ A (U t) a)
      atTop (nhds (alpha a))

/-- Once the specified forward limit is already known to be an equivalence,
the actual inverse maps converge to its inverse.  This statement makes no
completeness assumption and is not a replacement for inverse control when
surjectivity of an unknown limit is still being proved. -/
theorem tendsto_symm_apply_atTop_of_tendsto
    (f : ℝ → A ≃⋆ₐ[ℂ] A) (alpha : A ≃⋆ₐ[ℂ] A)
    (h : ∀ a : A, Tendsto (fun t ↦ f t a) atTop (nhds (alpha a)))
    (a : A) :
    Tendsto (fun t ↦ (f t).symm a) atTop (nhds (alpha.symm a)) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.mp (h (alpha.symm a))) epsilon hepsilon
  refine ⟨T, fun t ht ↦ ?_⟩
  calc
    dist ((f t).symm a) (alpha.symm a) =
        dist (f t ((f t).symm a)) (f t (alpha.symm a)) :=
      ((StarAlgEquiv.isometry (f t)).dist_eq _ _).symm
    _ = dist a (f t (alpha.symm a)) := by rw [(f t).apply_symm_apply]
    _ = dist (f t (alpha.symm a)) a := dist_comm _ _
    _ < epsilon := by simpa using hT t ht

/-- The inverse-action limit carried by every start-at-one asymptotically
inner witness. -/
theorem IsAsymptoticallyInnerFromOne.tendsto_symm_apply
    {alpha : A ≃⋆ₐ[ℂ] A} (h : IsAsymptoticallyInnerFromOne alpha) (a : A) :
    Tendsto
      (fun t ↦ (Unitary.conjStarAlgAut ℂ A (Classical.choose h t)).symm a)
      atTop (nhds (alpha.symm a)) := by
  exact tendsto_symm_apply_atTop_of_tendsto
    (fun t ↦ Unitary.conjStarAlgAut ℂ A (Classical.choose h t)) alpha
    (Classical.choose_spec h).2.2 a

/-- The identity automorphism is implemented by the constant-one path. -/
theorem isAsymptoticallyInnerFromOne_refl :
    IsAsymptoticallyInnerFromOne (StarAlgEquiv.refl ℂ A) := by
  refine ⟨fun _ ↦ 1, continuous_const, rfl, ?_⟩
  intro a
  simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ a) atTop (nhds a))

/-- Start-at-one asymptotic innerness is closed under inverse. -/
theorem IsAsymptoticallyInnerFromOne.symm {alpha : A ≃⋆ₐ[ℂ] A}
    (h : IsAsymptoticallyInnerFromOne alpha) :
    IsAsymptoticallyInnerFromOne alpha.symm := by
  obtain ⟨U, hU, hU0, hlimit⟩ := h
  have hstar : Continuous (fun t ↦ star (U t)) := by
    exact continuous_star.comp hU
  refine ⟨fun t ↦ star (U t), hstar, ?_, ?_⟩
  · change star (U 0) = 1
    rw [hU0]
    simp
  intro a
  have hinv := tendsto_symm_apply_atTop_of_tendsto
    (fun t ↦ Unitary.conjStarAlgAut ℂ A (U t)) alpha hlimit a
  simpa using hinv

/-- Start-at-one asymptotic innerness is closed under composition.  The
product order follows `StarAlgEquiv.trans`: `alpha.trans beta` applies
`alpha` first and then `beta`. -/
theorem IsAsymptoticallyInnerFromOne.trans
    {alpha beta : A ≃⋆ₐ[ℂ] A}
    (halpha : IsAsymptoticallyInnerFromOne alpha)
    (hbeta : IsAsymptoticallyInnerFromOne beta) :
    IsAsymptoticallyInnerFromOne (alpha.trans beta) := by
  obtain ⟨U, hU, hU0, hUlimit⟩ := halpha
  obtain ⟨V, hV, hV0, hVlimit⟩ := hbeta
  refine ⟨fun t ↦ V t * U t, hV.mul hU, ?_, ?_⟩
  · simp [hU0, hV0]
  intro a
  have hcomp := MathlibAnnex.Metric.tendsto_comp_of_isometry
    (fun t ↦ Unitary.conjStarAlgAut ℂ A (V t))
    (fun t ↦ Unitary.conjStarAlgAut ℂ A (U t) a)
    (fun _ ↦ StarAlgEquiv.isometry _)
    (hUlimit a) (hVlimit (alpha a))
  simpa [Unitary.conjStarAlgAut_mul_apply] using hcomp

/-- Start-at-one asymptotic innerness is invariant under conjugation by a
fixed star-algebra automorphism. -/
theorem IsAsymptoticallyInnerFromOne.conj
    {alpha : A ≃⋆ₐ[ℂ] A} (h : IsAsymptoticallyInnerFromOne alpha)
    (gamma : A ≃⋆ₐ[ℂ] A) :
    IsAsymptoticallyInnerFromOne
      (gamma.symm.trans (alpha.trans gamma)) := by
  obtain ⟨U, hU, hU0, hlimit⟩ := h
  let gammaStar : A →⋆* A :=
    { gamma.toMonoidHom with map_star' := fun a ↦ map_star gamma a }
  let W : ℝ → unitary A := fun t ↦ Unitary.map gammaStar (U t)
  have hW : Continuous W := by
    apply Continuous.subtype_mk
    change Continuous (fun t ↦ gamma (U t : A))
    exact (StarAlgEquiv.isometry gamma).continuous.comp
      (continuous_subtype_val.comp hU)
  refine ⟨W, hW, ?_, ?_⟩
  · change Unitary.map gammaStar (U 0) = 1
    rw [hU0]
    exact map_one _
  intro a
  have hmapped := ((StarAlgEquiv.isometry gamma).continuous.tendsto _).comp
    (hlimit (gamma.symm a))
  have heq :
      (fun t ↦ Unitary.conjStarAlgAut ℂ A (W t) a) =
        gamma ∘ (fun t ↦ Unitary.conjStarAlgAut ℂ A (U t) (gamma.symm a)) := by
    funext t
    change gamma (U t : A) * a * star (gamma (U t : A)) =
      gamma ((U t : A) * gamma.symm a * star (U t : A))
    simp [map_mul, map_star, mul_assoc]
  rw [heq]
  simpa only [StarAlgEquiv.trans_apply, gamma.apply_symm_apply] using hmapped

/-- Forgetting the path gives finite-set point-norm approximate innerness,
with a single time and unitary chosen for the whole finite set. -/
theorem IsAsymptoticallyInnerFromOne.isPointNormApproximatelyInner
    {alpha : A ≃⋆ₐ[ℂ] A} (h : IsAsymptoticallyInnerFromOne alpha) :
    IsPointNormApproximatelyInner alpha := by
  obtain ⟨U, _hU, _hU0, hlimit⟩ := h
  intro F epsilon hepsilon
  have hfinite : ∀ᶠ t in atTop, ∀ a ∈ F,
      ‖alpha a - Unitary.conjStarAlgAut ℂ A (U t) a‖ < epsilon := by
    apply (F.eventually_all).2
    intro a _ha
    have ha := (hlimit a) (Metric.ball_mem_nhds _ hepsilon)
    filter_upwards [ha] with t ht
    change dist (Unitary.conjStarAlgAut ℂ A (U t) a) (alpha a) < epsilon at ht
    simpa only [dist_eq_norm, norm_sub_rev] using ht
  obtain ⟨t, ht⟩ := hfinite.exists
  exact ⟨U t, ht⟩

end MathlibAnnex.CStarAlgebra
