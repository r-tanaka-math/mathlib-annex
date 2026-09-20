import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import MathlibAnnex.Analysis.CStarAlgebra.Cyclic

/-!
# Bounded Schur lemma on arbitrary complex Hilbert spaces

The self-adjoint core uses real continuous functional calculus.  Two distinct
spectral points would give nonzero disjoint CFC pieces.  The closed range of
one is a nonzero reducing subspace, hence all of the Hilbert space; the other
piece must then vanish, a contradiction.  No finite-dimensional eigenvalue
argument is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped InnerProduct ComplexStarModule

namespace StarAlgHom

variable {A H : Type*}
variable [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An operator belongs to the bounded commutant of a representation. -/
def InCommutant (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H) : Prop :=
  ∀ a, Commute T (π a)

private def rangeClosure (T : H →L[ℂ] H) : Submodule ℂ H :=
  (LinearMap.range T.toLinearMap).topologicalClosure

private theorem isReducing_rangeClosure (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hcomm : InCommutant π T) :
    IsReducing π (rangeClosure T) := by
  have hinv (a : A) : (rangeClosure T).IsInvariantUnder (π a) := by
    intro x hx
    change x ∈ closure (LinearMap.range T.toLinearMap) at hx
    change π a x ∈ closure (LinearMap.range T.toLinearMap)
    apply (show Set.MapsTo (π a) (LinearMap.range T.toLinearMap)
        (LinearMap.range T.toLinearMap) by
      rintro _ ⟨y, rfl⟩
      refine ⟨π a y, ?_⟩
      have hc := congrArg (fun R : H →L[ℂ] H ↦ R y) (hcomm a).eq
      change T (π a y) = π a (T y)
      simpa only [FunLike.coe_mul_eq_comp, Function.comp_apply] using hc).closure
      (π a).continuous hx
  intro a
  refine ⟨hinv a, ?_⟩
  have hadj : π (star a) = ContinuousLinearMap.adjoint (π a) := by
    rw [map_star, ContinuousLinearMap.star_eq_adjoint]
  rw [← hadj]
  exact hinv (star a)

private theorem rangeClosure_ne_bot {T : H →L[ℂ] H} (hT : T ≠ 0) :
    rangeClosure T ≠ ⊥ := by
  intro hbot
  apply hT
  apply ContinuousLinearMap.ext
  intro x
  have hx : T x ∈ rangeClosure T :=
    (LinearMap.range T.toLinearMap).le_topologicalClosure
      (LinearMap.mem_range_self T.toLinearMap x)
  rw [hbot, Submodule.mem_bot] at hx
  exact hx

private theorem eq_zero_of_comp_eq_zero_of_rangeClosure_eq_top
    {S T : H →L[ℂ] H} (hcomp : S.comp T = 0) (hdense : rangeClosure T = ⊤) : S = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have hrange : LinearMap.range T.toLinearMap ≤ LinearMap.ker S.toLinearMap := by
    rintro _ ⟨y, rfl⟩
    have hy := congrArg (fun R : H →L[ℂ] H ↦ R y) hcomp
    simpa [ContinuousLinearMap.comp_apply] using hy
  have hclosure : rangeClosure T ≤ LinearMap.ker S.toLinearMap :=
    (LinearMap.range T.toLinearMap).topologicalClosure_minimal hrange
      S.isClosed_ker
  have hx : x ∈ LinearMap.ker S.toLinearMap := hclosure (hdense.symm ▸ Submodule.mem_top)
  simpa using hx

private theorem rangeClosure_eq_top_of_irreducible
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (hne : T ≠ 0)
    (hcomm : InCommutant π T) : rangeClosure T = ⊤ := by
  rcases hπ (rangeClosure T)
    (LinearMap.range T.toLinearMap).isClosed_topologicalClosure
    (isReducing_rangeClosure π T hcomm) with hbot | htop
  · exact (rangeClosure_ne_bot hne hbot).elim
  · exact htop

/-- Self-adjoint bounded Schur lemma.  The scalar is real and the Hilbert
space is explicitly required to be nontrivial so that the spectrum is
nonempty. -/
theorem eq_algebraMap_of_isSelfAdjoint_of_irreducible [Nontrivial H]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (hcomm : InCommutant π T) :
    ∃ r : ℝ, T = algebraMap ℝ (H →L[ℂ] H) r := by
  have no_two_points {r s : ℝ} (hr : r ∈ spectrum ℝ T) (hs : s ∈ spectrum ℝ T)
      (hrs : r < s) : False := by
    let c : ℝ := (r + s) / 2
    let f : ℝ → ℝ := fun x ↦ max (x - c) 0
    let g : ℝ → ℝ := fun x ↦ max (c - x) 0
    have hfcont : Continuous f :=
      (continuous_id.sub continuous_const).max continuous_const
    have hgcont : Continuous g :=
      (continuous_const.sub continuous_id).max continuous_const
    have hfg : ∀ x, f x * g x = 0 := by
      intro x
      by_cases hx : x ≤ c
      · simp [f, max_eq_right (sub_nonpos.mpr hx)]
      · have hcx : c ≤ x := (lt_of_not_ge hx).le
        simp [g, max_eq_right (sub_nonpos.mpr hcx)]
    have hgf : ∀ x, g x * f x = 0 := fun x ↦ by rw [mul_comm, hfg]
    let F : H →L[ℂ] H := cfc (p := IsSelfAdjoint) f T
    let G : H →L[ℂ] H := cfc (p := IsSelfAdjoint) g T
    have hf_s : f s ≠ 0 := by
      have : c < s := by dsimp [c]; linarith
      simp [f, max_eq_left (sub_nonneg.mpr this.le), ne_of_gt (sub_pos.mpr this)]
    have hg_r : g r ≠ 0 := by
      have : r < c := by dsimp [c]; linarith
      simp [g, max_eq_left (sub_nonneg.mpr this.le), ne_of_gt (sub_pos.mpr this)]
    have hFne : F ≠ 0 := by
      intro hzero
      have hb := norm_apply_le_norm_cfc (p := IsSelfAdjoint)
        f T hs hfcont.continuousOn hT
      change ‖f s‖ ≤ ‖F‖ at hb
      rw [hzero, norm_zero] at hb
      exact hf_s (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))
    have hGne : G ≠ 0 := by
      intro hzero
      have hb := norm_apply_le_norm_cfc (p := IsSelfAdjoint)
        g T hr hgcont.continuousOn hT
      change ‖g r‖ ≤ ‖G‖ at hb
      rw [hzero, norm_zero] at hb
      exact hg_r (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))
    have hFcomm : InCommutant π F := fun a ↦ hT.commute_cfc (hcomm a) f
    have hGcomm : InCommutant π G := fun a ↦ hT.commute_cfc (hcomm a) g
    have hFdense : rangeClosure F = ⊤ :=
      rangeClosure_eq_top_of_irreducible π hπ IsSelfAdjoint.cfc hFne hFcomm
    have hGF : G.comp F = 0 := by
      change G * F = 0
      calc
        G * F = cfc (fun x ↦ g x * f x) T := (cfc_mul g f T).symm
        _ = cfc (0 : ℝ → ℝ) T := by congr 1; funext x; exact hgf x
        _ = 0 := cfc_zero ℝ T
    exact hGne (eq_zero_of_comp_eq_zero_of_rangeClosure_eq_top hGF hFdense)
  have hsingle : (spectrum ℝ T).Subsingleton := by
    intro r hr s hs
    by_cases hrs : r = s
    · exact hrs
    · rcases lt_or_gt_of_ne hrs with hlt | hgt
      · exact (no_two_points hr hs hlt).elim
      · exact (no_two_points hs hr hgt).elim
  have hspec : (spectrum ℝ T).Nonempty :=
    ContinuousFunctionalCalculus.spectrum_nonempty
      (R := ℝ) (A := H →L[ℂ] H) (p := IsSelfAdjoint) T hT
  obtain ⟨r, hr⟩ := hspec
  refine ⟨r, CFC.eq_algebraMap_of_spectrum_subset_singleton
    (p := IsSelfAdjoint) T r ?_ hT⟩
  intro s hs
  exact Set.mem_singleton_iff.mpr (hsingle hs hr)

/-- Bounded Hilbert-space Schur lemma in arbitrary dimension: every operator
in the commutant of an irreducible complex star representation is scalar. -/
theorem eq_algebraMap_of_irreducible [Nontrivial H]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (T : H →L[ℂ] H) (hcomm : InCommutant π T) :
    ∃ z : ℂ, T = algebraMap ℂ (H →L[ℂ] H) z := by
  have hstar : InCommutant π (T†) := by
    intro a
    have h := (hcomm (star a)).star_star
    have hπ : star (π (star a)) = π a := by rw [map_star, star_star]
    rw [ContinuousLinearMap.star_eq_adjoint T, hπ] at h
    exact h
  have hreal : InCommutant π (ℜ T : H →L[ℂ] H) := by
    intro a
    rw [realPart_apply_coe]
    exact ((hcomm a).add_left (hstar a)).smul_left _
  have himag : InCommutant π (ℑ T : H →L[ℂ] H) := by
    intro a
    rw [imaginaryPart_apply_coe]
    exact (((hcomm a).sub_left (hstar a)).smul_left _).smul_left _
  obtain ⟨r, hr⟩ := eq_algebraMap_of_isSelfAdjoint_of_irreducible
    π hπ (ℜ T : H →L[ℂ] H) (ℜ T).2 hreal
  obtain ⟨s, hs⟩ := eq_algebraMap_of_isSelfAdjoint_of_irreducible
    π hπ (ℑ T : H →L[ℂ] H) (ℑ T).2 himag
  refine ⟨(r : ℂ) + Complex.I * (s : ℂ), ?_⟩
  rw [← realPart_add_I_smul_imaginaryPart T, hr, hs]
  apply ContinuousLinearMap.ext
  intro x
  simp [Algebra.smul_def]

end StarAlgHom
