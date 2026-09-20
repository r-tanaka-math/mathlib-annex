import MathlibAnnex.Analysis.Normed.Affine.IsometryExtension.Local
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Extension from open connected domains

This module glues the local affine-isometry extensions into a unique ambient
affine isometry equivalence.
-/

open Metric Set AffineIsometryEquiv

namespace MathlibAnnex

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace IsometryEquiv

private theorem affineIsometryEquiv_map_lineMap
    (A : E ≃ᵃⁱ[ℝ] F) (c x : E) (a : ℝ) :
    A (AffineMap.lineMap c x a) =
      AffineMap.lineMap (A c) (A x) a := by
  rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module']
  change A.toAffineEquiv.toAffineMap (a • (x - c) + c) = _
  rw [show a • (x - c) + c = a • (x - c) +ᵥ c by rfl]
  rw [AffineMap.map_vadd]
  change A.toAffineEquiv.toAffineMap.linear (a • (x -ᵥ c)) +ᵥ A c =
    a • (A x -ᵥ A c) +ᵥ A c
  rw [LinearMap.map_smul, A.toAffineEquiv.toAffineMap.linearMap_vsub]
  rfl

private theorem affineIsometryEquiv_eq_of_isOpen_of_eqOn
    {u : Set E} (hu : IsOpen u) (hne : u.Nonempty)
    (A B : E ≃ᵃⁱ[ℝ] F) (h : u.EqOn A B) : A = B := by
  rcases hne with ⟨c, hc⟩
  rcases Metric.mem_nhds_iff.1 (hu.mem_nhds hc) with ⟨ε, hε, hball⟩
  apply AffineIsometryEquiv.ext
  intro x
  by_cases hxc : x = c
  · subst x
    exact h hc
  let a : ℝ := ε / (2 * dist x c)
  have hd : 0 < dist x c := dist_pos.mpr hxc
  have ha : 0 < a := div_pos hε (mul_pos (by norm_num) hd)
  let y : E := AffineMap.lineMap c x a
  have hyc : dist y c = ε / 2 := by
    simp only [y]
    rw [AffineMap.lineMap_apply_module', dist_eq_norm,
      add_sub_cancel_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos ha, ← dist_eq_norm]
    simp only [a]
    field_simp
  have hy : y ∈ u := by
    apply hball
    rw [mem_ball, hyc]
    linarith
  have hcAB : A c = B c := h hc
  have hyAB : A y = B y := h hy
  have hline : AffineMap.lineMap (A c) (A x) a =
      AffineMap.lineMap (B c) (B x) a := by
    rw [← affineIsometryEquiv_map_lineMap A c x a,
      ← affineIsometryEquiv_map_lineMap B c x a]
    exact hyAB
  rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module', hcAB] at hline
  have hv : A x - B c = B x - B c := by
    apply smul_right_injective F ha.ne'
    exact add_right_cancel hline
  exact sub_left_injective hv

private theorem existsUnique_affineIsometryEquiv_of_local
    {s : Set E} (hs : IsOpen s) (hsc : IsConnected s) (f : s → F)
    (hlocal : ∀ x : s, ∃ A : E ≃ᵃⁱ[ℝ] F, ∃ r > 0,
      ∀ y : s, dist (y : E) (x : E) < r → A (y : E) = f y) :
    ∃! A : E ≃ᵃⁱ[ℝ] F, ∀ x : s, A (x : E) = f x := by
  let chart : s → E ≃ᵃⁱ[ℝ] F := fun x ↦ Classical.choose (hlocal x)
  have chart_spec (x : s) : ∃ r > 0,
      ∀ y : s, dist (y : E) (x : E) < r → chart x (y : E) = f y :=
    Classical.choose_spec (hlocal x)
  have hchart : IsLocallyConstant chart := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    rcases chart_spec x with ⟨r, hr, hxr⟩
    filter_upwards [ball_mem_nhds x hr] with y hy
    rcases chart_spec y with ⟨q, hq, hyq⟩
    let u : Set E := (s ∩ ball (x : E) r) ∩ ball (y : E) q
    have hu : IsOpen u := (hs.inter isOpen_ball).inter isOpen_ball
    have hyx : dist (y : E) (x : E) < r := by
      simpa only [mem_ball, Subtype.dist_eq] using hy
    have hune : u.Nonempty := by
      refine ⟨(y : E), ⟨y.property, ?_⟩, mem_ball_self hq⟩
      exact hyx
    have heq : u.EqOn (chart y) (chart x) := by
      intro z hz
      let zs : s := ⟨z, hz.1.1⟩
      calc
        chart y z = f zs := hyq zs (by simpa only [zs, mem_ball] using hz.2)
        _ = chart x z :=
          (hxr zs (by simpa only [zs, mem_ball] using hz.1.2)).symm
    exact affineIsometryEquiv_eq_of_isOpen_of_eqOn hu hune (chart y) (chart x) heq
  let x₀ : s := ⟨Classical.choose hsc.nonempty, Classical.choose_spec hsc.nonempty⟩
  have hconst (x y : s) : chart x = chart y := by
    letI : PreconnectedSpace s := Subtype.preconnectedSpace hsc.isPreconnected
    exact hchart.apply_eq_of_preconnectedSpace x y
  have hagree (x : s) : chart x₀ (x : E) = f x := by
    rw [hconst x₀ x]
    rcases chart_spec x with ⟨r, hr, hxr⟩
    exact hxr x (by simpa using hr)
  refine ⟨chart x₀, hagree, ?_⟩
  intro A hA
  apply affineIsometryEquiv_eq_of_isOpen_of_eqOn hs hsc.nonempty A (chart x₀)
  intro z hz
  calc
    A z = f ⟨z, hz⟩ := hA ⟨z, hz⟩
    _ = chart x₀ z := (hagree ⟨z, hz⟩).symm

/-- A surjective isometry between open connected subsets of real normed
spaces extends to a unique ambient real affine isometry equivalence. -/
theorem existsUnique_affineExtension
    {s : Set E} {t : Set F} (f : s ≃ᵢ t)
    (hs : IsOpen s) (hsc : IsConnected s) (ht : IsOpen t) :
    ∃! A : E ≃ᵃⁱ[ℝ] F,
      ∀ x : s, A (x : E) = ((f x : t) : F) := by
  have hlocal : ∀ x : s, ∃ A : E ≃ᵃⁱ[ℝ] F, ∃ r > 0,
      ∀ y : s, dist (y : E) (x : E) < r →
        A (y : E) = ((f y : t) : F) := by
    intro x
    rcases Metric.mem_nhds_iff.1 (hs.mem_nhds x.property) with
      ⟨Rs, hRs, hsball⟩
    rcases Metric.mem_nhds_iff.1 (ht.mem_nhds (f x).property) with
      ⟨Rt, hRt, htball⟩
    let R : ℝ := min Rs Rt
    have hR : 0 < R := lt_min hRs hRt
    have hsball' : ball (x : E) R ⊆ s :=
      (ball_subset_ball (min_le_left Rs Rt)).trans hsball
    have htball' : ball ((f x : t) : F) R ⊆ t :=
      (ball_subset_ball (min_le_right Rs Rt)).trans htball
    rcases MathlibAnnex.IsometryEquiv.exists_affineExtension_eqOn_ball
      f x hR hsball' htball' with ⟨A, hA⟩
    refine ⟨A, R / 8, by positivity, ?_⟩
    intro y hy
    exact hA y (by simpa only [mem_ball] using hy)
  exact existsUnique_affineIsometryEquiv_of_local hs hsc
    (fun x ↦ ((f x : t) : F)) hlocal

end IsometryEquiv

end

end MathlibAnnex
