import MathlibAnnex.Analysis.Normed.Affine.Reflection
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.AffineSpace.MidpointZero
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Local extension machinery for isometries

This module develops the local midpoint and affine-segment identities used to
extend isometries between open subsets of real normed spaces.
-/

open Metric Set AffineIsometryEquiv Bornology

namespace MathlibAnnex

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The intersection of two closed balls with the same radius. -/
def symmetricLens (x y : E) (r : ℝ) : Set E :=
  closedBall x r ∩ closedBall y r

private theorem midpoint_mem_symmetricLens {x y : E} {r : ℝ}
    (h : 2⁻¹ * dist x y ≤ r) : midpoint ℝ x y ∈ symmetricLens x y r := by
  constructor
  · simpa [symmetricLens, dist_midpoint_left, Real.norm_two] using h
  · simpa [symmetricLens, dist_midpoint_right, Real.norm_two] using h

private theorem mapsTo_pointReflection_symmetricLens (x y : E) (r : ℝ) :
    MapsTo (pointReflection ℝ (midpoint ℝ x y))
      (symmetricLens x y r) (symmetricLens x y r) := by
  rintro z ⟨hzx, hzy⟩
  constructor
  · change dist (pointReflection ℝ (midpoint ℝ x y) z) x ≤ r
    calc
      dist (pointReflection ℝ (midpoint ℝ x y) z) x =
          dist (pointReflection ℝ (midpoint ℝ x y) z)
            (pointReflection ℝ (midpoint ℝ x y) y) :=
        congrArg (dist (pointReflection ℝ (midpoint ℝ x y) z))
          (pointReflection_midpoint_right x y).symm
      _ = dist z y := (pointReflection ℝ (midpoint ℝ x y)).dist_map z y
      _ ≤ r := hzy
  · change dist (pointReflection ℝ (midpoint ℝ x y) z) y ≤ r
    calc
      dist (pointReflection ℝ (midpoint ℝ x y) z) y =
          dist (pointReflection ℝ (midpoint ℝ x y) z)
            (pointReflection ℝ (midpoint ℝ x y) x) :=
        congrArg (dist (pointReflection ℝ (midpoint ℝ x y) z))
          (pointReflection_midpoint_left x y).symm
      _ = dist z x := (pointReflection ℝ (midpoint ℝ x y)).dist_map z x
      _ ≤ r := hzx

namespace IsometryEquiv

/-- An isometry between corresponding bounded symmetric lenses maps the
midpoint of their foci to the midpoint of the target foci. -/
theorem map_midpoint_of_symmetricLens
    {x y : E} {x' y' : F} {r : ℝ}
    (hxy : 2⁻¹ * dist x y ≤ r) (hxy' : 2⁻¹ * dist x' y' ≤ r)
    (f : symmetricLens x y r ≃ᵢ symmetricLens x' y' r) :
    ((f ⟨midpoint ℝ x y, midpoint_mem_symmetricLens hxy⟩ :
        symmetricLens x' y' r) : F) = midpoint ℝ x' y' := by
  have hs : IsBounded (symmetricLens x y r) :=
    isBounded_closedBall.subset inter_subset_left
  have h := MathlibAnnex.IsometryEquiv.map_center_of_mapsTo_pointReflection
    f (midpoint_mem_symmetricLens hxy) (midpoint_mem_symmetricLens hxy') hs
    (mapsTo_pointReflection_symmetricLens x y r)
    (mapsTo_pointReflection_symmetricLens x' y' r)
  exact congrArg Subtype.val h

private def restrictToSymmetricLens
    {s : Set E} {t : Set F} (f : s ≃ᵢ t) (x y : s) (r : ℝ)
    (hs : symmetricLens (x : E) (y : E) r ⊆ s)
    (ht : symmetricLens ((f x : t) : F) ((f y : t) : F) r ⊆ t) :
    symmetricLens (x : E) (y : E) r ≃ᵢ
      symmetricLens ((f x : t) : F) ((f y : t) : F) r where
  toFun z := by
    let zs : s := ⟨z, hs z.property⟩
    refine ⟨(f zs : t), ?_⟩
    constructor
    · change dist (f zs) (f x) ≤ r
      rw [f.dist_eq, Subtype.dist_eq]
      exact z.property.1
    · change dist (f zs) (f y) ≤ r
      rw [f.dist_eq, Subtype.dist_eq]
      exact z.property.2
  invFun z := by
    let zt : t := ⟨z, ht z.property⟩
    refine ⟨(f.symm zt : s), ?_⟩
    constructor
    · change dist (f.symm zt) x ≤ r
      rw [← f.dist_eq, f.apply_symm_apply, Subtype.dist_eq]
      exact z.property.1
    · change dist (f.symm zt) y ≤ r
      rw [← f.dist_eq, f.apply_symm_apply, Subtype.dist_eq]
      exact z.property.2
  left_inv z := by
    apply Subtype.ext
    change ((f.symm (f ⟨(z : E), hs z.property⟩) : s) : E) = (z : E)
    exact congrArg Subtype.val (f.symm_apply_apply ⟨(z : E), hs z.property⟩)
  right_inv z := by
    apply Subtype.ext
    change ((f (f.symm ⟨(z : F), ht z.property⟩) : t) : F) = (z : F)
    exact congrArg Subtype.val (f.apply_symm_apply ⟨(z : F), ht z.property⟩)
  isometry_toFun := Isometry.of_dist_eq fun z w => by
    change dist (f ⟨z, hs z.property⟩) (f ⟨w, hs w.property⟩) = dist z w
    rw [f.dist_eq, Subtype.dist_eq, Subtype.dist_eq]

/-- A set isometry preserves the midpoint of two points whenever the
corresponding symmetric lenses stay inside the source and target sets. -/
theorem map_midpoint_of_symmetricLens_subset
    {s : Set E} {t : Set F} (f : s ≃ᵢ t) (x y : s) (r : ℝ)
    (hhalf : 2⁻¹ * dist (x : E) (y : E) ≤ r)
    (hs : symmetricLens (x : E) (y : E) r ⊆ s)
    (ht : symmetricLens ((f x : t) : F) ((f y : t) : F) r ⊆ t) :
    ((f ⟨midpoint ℝ (x : E) (y : E),
          hs (midpoint_mem_symmetricLens hhalf)⟩ : t) : F) =
      midpoint ℝ ((f x : t) : F) ((f y : t) : F) := by
  let g := restrictToSymmetricLens f x y r hs ht
  have hdist : dist ((f x : t) : F) ((f y : t) : F) = dist (x : E) (y : E) := by
    simpa only [Subtype.dist_eq] using f.dist_eq x y
  have hhalf' : 2⁻¹ * dist ((f x : t) : F) ((f y : t) : F) ≤ r := by
    rwa [hdist]
  exact map_midpoint_of_symmetricLens hhalf hhalf' g

/-- If corresponding ambient balls lie in the source and target sets, then a
set isometry preserves midpoints on the concentric quarter ball. -/
theorem map_midpoint_of_mem_ball
    {s : Set E} {t : Set F} (f : s ≃ᵢ t) (c : s) {R : ℝ} (hR : 0 < R)
    (hsball : ball (c : E) R ⊆ s)
    (htball : ball ((f c : t) : F) R ⊆ t)
    (x y : s) (hx : (x : E) ∈ ball (c : E) (R / 4))
    (hy : (y : E) ∈ ball (c : E) (R / 4)) :
    ((f ⟨midpoint ℝ (x : E) (y : E),
          hsball (by
            rw [mem_ball]
            calc
              dist (midpoint ℝ (x : E) (y : E)) (c : E) ≤
                  (dist (x : E) (c : E) + dist (y : E) (c : E)) / 2 := by
                    simpa [dist_comm] using
                      dist_midpoint_midpoint_le (x : E) (y : E) (c : E) (c : E)
              _ < R := by rw [mem_ball] at hx hy; linarith)⟩ : t) : F) =
      midpoint ℝ ((f x : t) : F) ((f y : t) : F) := by
  have hxy_lt : dist (x : E) (y : E) < R / 2 := by
    calc
      dist (x : E) (y : E) ≤ dist (x : E) (c : E) + dist (c : E) (y : E) :=
        dist_triangle _ _ _
      _ < R / 4 + R / 4 := by
        rw [mem_ball] at hx hy
        exact add_lt_add hx (by simpa [dist_comm] using hy)
      _ = R / 2 := by ring
  have hhalf : 2⁻¹ * dist (x : E) (y : E) ≤ R / 2 := by
    have := hxy_lt.le
    norm_num at ⊢
    linarith
  have hsLens : symmetricLens (x : E) (y : E) (R / 2) ⊆ s := by
    intro z hz
    apply hsball
    rw [mem_ball]
    have hzx : dist z (x : E) ≤ R / 2 := hz.1
    rw [mem_ball] at hx
    calc
      dist z (c : E) ≤ dist z (x : E) + dist (x : E) (c : E) := dist_triangle _ _ _
      _ < R / 2 + R / 4 := add_lt_add_of_le_of_lt hzx hx
      _ < R := by linarith
  have hfx : dist ((f x : t) : F) ((f c : t) : F) < R / 4 := by
    rw [← Subtype.dist_eq, f.dist_eq, Subtype.dist_eq]
    exact hx
  have htLens :
      symmetricLens ((f x : t) : F) ((f y : t) : F) (R / 2) ⊆ t := by
    intro z hz
    apply htball
    rw [mem_ball]
    have hzx : dist z ((f x : t) : F) ≤ R / 2 := hz.1
    calc
      dist z ((f c : t) : F) ≤
          dist z ((f x : t) : F) + dist ((f x : t) : F) ((f c : t) : F) :=
        dist_triangle _ _ _
      _ < R / 2 + R / 4 := add_lt_add_of_le_of_lt hzx hfx
      _ < R := by linarith
  exact map_midpoint_of_symmetricLens_subset f x y (R / 2) hhalf hsLens htLens

private theorem map_lineMap_of_map_midpoint
    {u : Set E} (hu : Convex ℝ u) (g : u → F) (hg : Continuous g)
    (hm : ∀ x y : u,
      g ⟨midpoint ℝ (x : E) (y : E), hu.midpoint_mem x.2 y.2⟩ =
        midpoint ℝ (g x) (g y))
    (x y : u) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
    g ⟨AffineMap.lineMap (x : E) (y : E) r,
        hu.lineMap_mem x.2 y.2 hr⟩ =
      AffineMap.lineMap (g x) (g y) r := by
  let p : Icc (0 : ℝ) 1 → u := fun a ↦
    ⟨AffineMap.lineMap (x : E) (y : E) (a : ℝ),
      hu.lineMap_mem x.2 y.2 a.2⟩
  have hp : Continuous p := Continuous.subtype_mk
    (AffineMap.lineMap_continuous.comp continuous_subtype_val) _
  have hrat (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
      g (p ⟨(q : ℝ), by
        constructor
        · exact_mod_cast hq0
        · exact_mod_cast hq1⟩) =
        AffineMap.lineMap (g x) (g y) (q : ℝ) := by
    let n : ℕ := q.den
    let k : ℕ := q.num.natAbs
    have hn : 0 < n := q.den_pos
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq0
    have hq_cast : (q : ℝ) = (k : ℝ) / (n : ℝ) := by
      have hknumZ : (k : ℤ) = q.num := by
        dsimp [k]
        exact Int.natAbs_of_nonneg hnum
      have hknumR : (k : ℝ) = (q.num : ℝ) := by exact_mod_cast hknumZ
      rw [Rat.cast_def, hknumR]
    have hq1R : (q : ℝ) ≤ 1 := by exact_mod_cast hq1
    have hkR : (k : ℝ) ≤ (n : ℝ) := by
      rw [hq_cast, div_le_one hnR] at hq1R
      exact hq1R
    have hk : k ≤ n := by exact_mod_cast hkR
    have hcoeff {i : ℕ} (hi : i ≤ n) :
        (i : ℝ) / (n : ℝ) ∈ Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · rw [div_le_one hnR]
        exact_mod_cast hi
    let Q : ℕ → F := fun i ↦
      if hi : i ≤ n then
        g ⟨AffineMap.lineMap (x : E) (y : E) ((i : ℝ) / (n : ℝ)),
          hu.lineMap_mem x.2 y.2 (hcoeff hi)⟩
      else 0
    have hQmid : ∀ i, i + 2 ≤ n →
        Q (i + 1) = midpoint ℝ (Q i) (Q (i + 2)) := by
      intro i hi
      have hi0 : i ≤ n := by omega
      have hi1 : i + 1 ≤ n := by omega
      have hi2 : i + 2 ≤ n := hi
      let z0 : u := ⟨AffineMap.lineMap (x : E) (y : E)
          ((i : ℝ) / (n : ℝ)), hu.lineMap_mem x.2 y.2 (hcoeff hi0)⟩
      let z1 : u := ⟨AffineMap.lineMap (x : E) (y : E)
          (((i + 1 : ℕ) : ℝ) / (n : ℝ)), hu.lineMap_mem x.2 y.2 (hcoeff hi1)⟩
      let z2 : u := ⟨AffineMap.lineMap (x : E) (y : E)
          (((i + 2 : ℕ) : ℝ) / (n : ℝ)), hu.lineMap_mem x.2 y.2 (hcoeff hi2)⟩
      have hz : midpoint ℝ (z0 : E) (z2 : E) = (z1 : E) := by
        change midpoint ℝ
          (AffineMap.lineMap (x : E) (y : E) ((i : ℝ) / (n : ℝ)))
          (AffineMap.lineMap (x : E) (y : E) (((i + 2 : ℕ) : ℝ) / (n : ℝ))) =
          AffineMap.lineMap (x : E) (y : E) (((i + 1 : ℕ) : ℝ) / (n : ℝ))
        calc
          _ = AffineMap.lineMap (x : E) (y : E)
              (midpoint ℝ ((i : ℝ) / (n : ℝ))
                (((i + 2 : ℕ) : ℝ) / (n : ℝ))) :=
            ((AffineMap.lineMap (x : E) (y : E)).map_midpoint _ _).symm
          _ = _ := by
            congr 1
            simp only [midpoint_eq_smul_add, invOf_eq_inv, smul_eq_mul]
            push_cast
            field_simp
            ring
      simp only [Q, dif_pos hi0, dif_pos hi1, dif_pos hi2]
      change g z1 = midpoint ℝ (g z0) (g z2)
      simpa only [hz] using hm z0 z2
    have hformula : ∀ j, j ≤ n → Q j = Q 0 + (j : ℝ) • (Q 1 - Q 0) := by
      intro j
      induction j using Nat.twoStepInduction with
      | zero => intro _; simp
      | one => intro _; simp
      | more j hj hj1 =>
          intro hj2n
          have hj_le : j ≤ n := by omega
          have hj1_le : j + 1 ≤ n := by omega
          have hmid := hQmid j hj2n
          have hmid' := congrArg (fun z : F ↦ z + z) hmid
          rw [midpoint_add_self] at hmid'
          have hj2 : Q (j + 2) = Q (j + 1) + Q (j + 1) - Q j := by
            apply (eq_sub_iff_add_eq).2
            simpa [add_comm, add_left_comm, add_assoc] using hmid'.symm
          rw [hj2, hj hj_le, hj1 hj1_le]
          simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
          module
    have H := hformula k hk
    have Hn := hformula n le_rfl
    have Q0 : Q 0 = g x := by
      simp only [Q, dif_pos (Nat.zero_le n)]
      congr 1
      apply Subtype.ext
      simp
    have Qn : Q n = g y := by
      simp only [Q, dif_pos le_rfl]
      congr 1
      apply Subtype.ext
      simp [hn.ne']
    have Qk : Q k = g (p ⟨(q : ℝ), by
        constructor
        · exact_mod_cast hq0
        · exact_mod_cast hq1⟩) := by
      simp only [Q, dif_pos hk]
      congr 1
      apply Subtype.ext
      exact congrArg (AffineMap.lineMap (x : E) (y : E)) hq_cast.symm
    rw [Qk, Q0] at H
    rw [Qn, Q0] at Hn
    rw [AffineMap.lineMap_apply_module]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hkn : ((k : ℝ) / (n : ℝ)) * (n : ℝ) = (k : ℝ) := by field_simp
    calc
      g (p ⟨(q : ℝ), by
          constructor
          · exact_mod_cast hq0
          · exact_mod_cast hq1⟩) =
          g x + (k : ℝ) • (Q 1 - g x) := H
      _ = (1 - (q : ℝ)) • g x + (q : ℝ) • g y := by
        rw [Hn, hq_cast, smul_add, smul_smul, hkn]
        module
  let C : ℝ → Icc (0 : ℝ) 1 := fun a ↦
    ⟨max 0 (min 1 a), by constructor <;> simp⟩
  have hCcont : Continuous C := Continuous.subtype_mk
    (continuous_const.max (continuous_const.min continuous_id)) _
  have hCsurj : Function.Surjective C := by
    intro a
    refine ⟨a, Subtype.ext ?_⟩
    simp [C, a.2.1, a.2.2]
  have hdense : DenseRange (C ∘ ((↑) : ℚ → ℝ)) :=
    hCsurj.denseRange.comp Rat.denseRange_cast hCcont
  let rr : Icc (0 : ℝ) 1 := ⟨r, hr⟩
  change g (p rr) = AffineMap.lineMap (g x) (g y) (rr : ℝ)
  refine hdense.induction_on rr ?_ ?_
  · exact isClosed_eq (hg.comp hp)
      (AffineMap.lineMap_continuous.comp continuous_subtype_val)
  · intro q
    let u : ℚ := max 0 (min 1 q)
    have hu0 : 0 ≤ u := le_max_left _ _
    have hu1 : u ≤ 1 := max_le zero_le_one (min_le_left _ _)
    have hCu : C (q : ℝ) =
        ⟨(u : ℝ), by
          constructor
          · exact_mod_cast hu0
          · exact_mod_cast hu1⟩ := by
      apply Subtype.ext
      simp [C, u]
    rw [Function.comp_apply, hCu]
    exact hrat u hu0 hu1

/-- Under the same local ball hypotheses as
`map_midpoint_of_mem_ball`, the isometry preserves every point of a
segment contained in the quarter ball. -/
theorem map_lineMap_of_mem_ball
    {s : Set E} {t : Set F} (f : s ≃ᵢ t) (c : s) {R : ℝ} (hR : 0 < R)
    (hsball : ball (c : E) R ⊆ s)
    (htball : ball ((f c : t) : F) R ⊆ t)
    (x y : s) (hx : (x : E) ∈ ball (c : E) (R / 4))
    (hy : (y : E) ∈ ball (c : E) (R / 4))
    (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
    ((f ⟨AffineMap.lineMap (x : E) (y : E) a,
          hsball (ball_subset_ball (by linarith : R / 4 ≤ R)
            ((convex_ball (c : E) (R / 4)).lineMap_mem hx hy ha))⟩ : t) : F) =
      AffineMap.lineMap ((f x : t) : F) ((f y : t) : F) a := by
  let u : Set E := ball (c : E) (R / 4)
  let i : u → s := fun z ↦
    ⟨z, hsball (ball_subset_ball (by linarith : R / 4 ≤ R) z.property)⟩
  let g : u → F := fun z ↦ ((f (i z) : t) : F)
  have hi : Continuous i := Continuous.subtype_mk continuous_subtype_val _
  have hg : Continuous g :=
    continuous_subtype_val.comp (f.continuous.comp hi)
  have hm : ∀ z w : u,
      g ⟨midpoint ℝ (z : E) (w : E),
        (convex_ball (c : E) (R / 4)).midpoint_mem z.2 w.2⟩ =
        midpoint ℝ (g z) (g w) := by
    intro z w
    have h := map_midpoint_of_mem_ball f c hR hsball htball
      (i z) (i w) z.property w.property
    simpa only [g, i] using h
  let xu : u := ⟨x, hx⟩
  let yu : u := ⟨y, hy⟩
  have h := map_lineMap_of_map_midpoint
    (convex_ball (c : E) (R / 4)) g hg hm xu yu a ha
  simpa only [g, i, xu, yu] using h

private def radialSourcePoint (c : E) (r : ℝ) (x : E) : E :=
  c + (r / ‖x‖) • x

private theorem dist_radialSourcePoint {c : E} {r : ℝ} (hr : 0 < r)
    {x : E} (hx : x ≠ 0) : dist (radialSourcePoint c r x) c = r := by
  rw [radialSourcePoint, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos (div_pos hr (norm_pos_iff.mpr hx))]
  field_simp

private theorem radialSourcePoint_mem_ball {c : E} {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) {x : E} (hx : x ≠ 0) : radialSourcePoint c r x ∈ ball c R := by
  rw [mem_ball, dist_radialSourcePoint hr hx]
  exact hrR

private noncomputable def radialMap
    {s : Set E} {t : Set F} (f : s ≃ᵢ t) (c : s) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) (hsball : ball (c : E) R ⊆ s) : E → F := by
  classical
  exact fun x ↦ if hx : x = 0 then 0 else
    (‖x‖ / r) •
      (((f ⟨radialSourcePoint (c : E) r x,
        hsball (radialSourcePoint_mem_ball hr hrR hx)⟩ : t) : F) - ((f c : t) : F))

@[simp] private theorem radialMap_zero
    {s : Set E} {t : Set F} (f : s ≃ᵢ t) (c : s) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) (hsball : ball (c : E) R ⊆ s) :
    radialMap f c r R hr hrR hsball 0 = 0 := by
  simp [radialMap]

private theorem radialSourcePoint_smul_of_pos {c : E} {r a : ℝ}
    (ha : 0 < a) {x : E} (hx : x ≠ 0) :
    radialSourcePoint c r (a • x) = radialSourcePoint c r x := by
  have hnx : ‖x‖ ≠ 0 := (norm_pos_iff.mpr hx).ne'
  rw [radialSourcePoint, radialSourcePoint, norm_smul, Real.norm_eq_abs,
    abs_of_pos ha, smul_smul]
  congr 1
  field_simp

private theorem radialSourcePoint_neg {c : E} {r : ℝ} {x : E} :
    radialSourcePoint c r (-x) = c - (r / ‖x‖) • x := by
  simp [radialSourcePoint, sub_eq_add_neg]

private theorem radialMap_smul_of_pos
    {s : Set E} {t : Set F} (f : s ≃ᵢ t) (c : s) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) (hsball : ball (c : E) R ⊆ s)
    {a : ℝ} (ha : 0 < a) (x : E) :
    radialMap f c r R hr hrR hsball (a • x) =
      a • radialMap f c r R hr hrR hsball x := by
  by_cases hx : x = 0
  · subst x
    simp
  have hax : a • x ≠ 0 := smul_ne_zero ha.ne' hx
  simp only [radialMap, dif_neg hax, dif_neg hx]
  have hfpoint :
      ((f ⟨radialSourcePoint (c : E) r (a • x),
        hsball (radialSourcePoint_mem_ball hr hrR hax)⟩ : t) : F) =
      ((f ⟨radialSourcePoint (c : E) r x,
        hsball (radialSourcePoint_mem_ball hr hrR hx)⟩ : t) : F) := by
    apply congrArg Subtype.val
    apply congrArg f
    apply Subtype.ext
    exact radialSourcePoint_smul_of_pos ha hx
  rw [hfpoint, norm_smul, Real.norm_eq_abs, abs_of_pos ha, smul_smul]
  congr 1
  ring

private theorem radialMap_neg
    {s : Set E} {t : Set F} (f : s ≃ᵢ t) (c : s) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) (hR : 0 < R) (hrq : r < R / 4)
    (hsball : ball (c : E) R ⊆ s)
    (htball : ball ((f c : t) : F) R ⊆ t) (x : E) :
    radialMap f c r R hr hrR hsball (-x) =
      -radialMap f c r R hr hrR hsball x := by
  by_cases hx : x = 0
  · subst x
    simp
  have hnx : -x ≠ 0 := neg_ne_zero.mpr hx
  let px : s := ⟨radialSourcePoint (c : E) r x,
    hsball (radialSourcePoint_mem_ball hr hrR hx)⟩
  let nx : s := ⟨radialSourcePoint (c : E) r (-x),
    hsball (radialSourcePoint_mem_ball hr hrR hnx)⟩
  have hpx : (px : E) ∈ ball (c : E) (R / 4) := by
    rw [mem_ball]
    exact (dist_radialSourcePoint hr hx).trans_lt hrq
  have hnx' : (nx : E) ∈ ball (c : E) (R / 4) := by
    rw [mem_ball]
    exact (dist_radialSourcePoint hr hnx).trans_lt hrq
  have hsource : midpoint ℝ (px : E) (nx : E) = (c : E) := by
    change midpoint ℝ (radialSourcePoint (c : E) r x)
      (radialSourcePoint (c : E) r (-x)) = (c : E)
    rw [radialSourcePoint, radialSourcePoint_neg]
    simp only [midpoint_eq_smul_add, invOf_eq_inv]
    module
  have hm := map_midpoint_of_mem_ball f c hR hsball htball
    px nx hpx hnx'
  have hfc : ((f c : t) : F) =
      midpoint ℝ ((f px : t) : F) ((f nx : t) : F) := by
    rw [← hm]
    congr 2
    apply Subtype.ext
    exact hsource.symm
  have hdiff : ((f nx : t) : F) - ((f c : t) : F) =
      -(((f px : t) : F) - ((f c : t) : F)) := by
    rw [hfc]
    simp only [midpoint_eq_smul_add, invOf_eq_inv]
    module
  simp only [radialMap, dif_neg hnx, dif_neg hx]
  rw [norm_neg]
  change (‖x‖ / r) • (((f nx : t) : F) - ((f c : t) : F)) =
    -((‖x‖ / r) • (((f px : t) : F) - ((f c : t) : F)))
  rw [hdiff]
  module

private theorem norm_radialMap
    {s : Set E} {t : Set F} (f : s ≃ᵢ t) (c : s) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) (hsball : ball (c : E) R ⊆ s)
    (x : E) : ‖radialMap f c r R hr hrR hsball x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp
  rw [radialMap, dif_neg hx, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (norm_nonneg x) hr.le)]
  have hd :
      ‖((f ⟨radialSourcePoint (c : E) r x,
          hsball (radialSourcePoint_mem_ball hr hrR hx)⟩ : t) : F) -
          ((f c : t) : F)‖ = r := by
    rw [← dist_eq_norm, ← Subtype.dist_eq, f.dist_eq, Subtype.dist_eq,
      dist_radialSourcePoint hr hx]
  rw [hd]
  field_simp

private theorem map_midpoint_of_local_of_smul_pos (T : E → F) {r : ℝ} (hr : 0 < r)
    (hsmul : ∀ (a : ℝ), 0 < a → ∀ x, T (a • x) = a • T x)
    (hlocal : ∀ x y, ‖x‖ < r → ‖y‖ < r →
      T (midpoint ℝ x y) = midpoint ℝ (T x) (T y)) :
    ∀ x y, T (midpoint ℝ x y) = midpoint ℝ (T x) (T y) := by
  intro x y
  let d : ℝ := ‖x‖ + ‖y‖ + 1
  let q : ℝ := r / d
  have hd : 0 < d := by dsimp [d]; positivity
  have hq : 0 < q := div_pos hr hd
  have hqx : ‖q • x‖ < r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq]
    have hxlt : ‖x‖ < d := by dsimp [d]; linarith [norm_nonneg y]
    calc
      q * ‖x‖ < q * d := mul_lt_mul_of_pos_left hxlt hq
      _ = r := by dsimp [q]; field_simp
  have hqy : ‖q • y‖ < r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq]
    have hylt : ‖y‖ < d := by dsimp [d]; linarith [norm_nonneg x]
    calc
      q * ‖y‖ < q * d := mul_lt_mul_of_pos_left hylt hq
      _ = r := by dsimp [q]; field_simp
  have h := hlocal (q • x) (q • y) hqx hqy
  have hmid : midpoint ℝ (q • x) (q • y) = q • midpoint ℝ x y := by
    simp only [midpoint_eq_smul_add, invOf_eq_inv, smul_add, smul_smul]
    module
  rw [hmid, hsmul q hq, hsmul q hq, hsmul q hq] at h
  have hc := congrArg (fun z : F ↦ q⁻¹ • z) h
  have hcoeff : q⁻¹ * ((2 : ℝ)⁻¹ * q) = (2 : ℝ)⁻¹ := by field_simp
  simpa only [smul_smul, inv_mul_cancel₀ hq.ne', one_smul,
    midpoint_eq_smul_add, invOf_eq_inv, smul_add, hcoeff] using hc

private def midpointAddMonoidHom (T : E → F) (h0 : T 0 = 0)
    (hm : ∀ x y, T (midpoint ℝ x y) = midpoint ℝ (T x) (T y)) : E →+ F :=
  AddMonoidHom.ofMapMidpoint ℝ ℝ T h0 hm

@[simp] private theorem coe_midpointAddMonoidHom (T : E → F) (h0) (hm) :
    ⇑(midpointAddMonoidHom T h0 hm) = T := rfl

private theorem isometry_midpointAddMonoidHom (T : E → F) (h0 : T 0 = 0)
    (hm : ∀ x y, T (midpoint ℝ x y) = midpoint ℝ (T x) (T y))
    (hnorm : ∀ x, ‖T x‖ = ‖x‖) : Isometry T := by
  rw [isometry_iff_dist_eq]
  intro x y
  rw [dist_eq_norm]
  have hsub := (midpointAddMonoidHom T h0 hm).map_sub x y
  change T (x - y) = T x - T y at hsub
  rw [← hsub, hnorm, ← dist_eq_norm]

private noncomputable def midpointLinearIsometry (T : E → F) (h0 : T 0 = 0)
    (hm : ∀ x y, T (midpoint ℝ x y) = midpoint ℝ (T x) (T y))
    (hnorm : ∀ x, ‖T x‖ = ‖x‖) : E →ₗᵢ[ℝ] F :=
  { (midpointAddMonoidHom T h0 hm).toRealLinearMap
      (isometry_midpointAddMonoidHom T h0 hm hnorm).continuous with
    norm_map' := hnorm }

@[simp] private theorem coe_midpointLinearIsometry (T : E → F) (h0) (hm) (hnorm) :
    ⇑(midpointLinearIsometry T h0 hm hnorm) = T := rfl

private theorem radialMap_eq_sub_of_norm_lt
    {s : Set E} {t : Set F} (f : s ≃ᵢ t) (c : s) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) (hR : 0 < R) (hrq : r < R / 4)
    (hsball : ball (c : E) R ⊆ s)
    (htball : ball ((f c : t) : F) R ⊆ t)
    (x : E) (hxnorm : ‖x‖ < r) :
    radialMap f c r R hr hrR hsball x =
      ((f ⟨(c : E) + x, hsball (by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
        exact hxnorm.trans hrR)⟩ : t) : F) - ((f c : t) : F) := by
  let cx : s := ⟨(c : E) + x, hsball (by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hxnorm.trans hrR)⟩
  by_cases hx : x = 0
  · subst x
    simp
  let p : s := ⟨radialSourcePoint (c : E) r x,
    hsball (radialSourcePoint_mem_ball hr hrR hx)⟩
  have hcq : (c : E) ∈ ball (c : E) (R / 4) := by
    rw [mem_ball, dist_self]
    linarith
  have hpq : (p : E) ∈ ball (c : E) (R / 4) := by
    rw [mem_ball]
    exact (dist_radialSourcePoint hr hx).trans_lt hrq
  let a : ℝ := ‖x‖ / r
  have ha : a ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (norm_nonneg x) hr.le
    · rw [div_le_one hr]
      exact hxnorm.le
  have hcoef : a * (r / ‖x‖) = 1 := by
    dsimp [a]
    field_simp [hr.ne', (norm_pos_iff.mpr hx).ne']
  have harg : AffineMap.lineMap (c : E) (p : E) a = (cx : E) := by
    change AffineMap.lineMap (c : E) (radialSourcePoint (c : E) r x) a =
      (c : E) + x
    rw [AffineMap.lineMap_apply_module, radialSourcePoint, smul_add, smul_smul,
      hcoef, one_smul]
    module
  have hline := map_lineMap_of_mem_ball f c hR hsball htball
    c p hcq hpq a ha
  have hinput :
      (⟨AffineMap.lineMap (c : E) (p : E) a,
        hsball (ball_subset_ball (by linarith : R / 4 ≤ R)
          ((convex_ball (c : E) (R / 4)).lineMap_mem hcq hpq ha))⟩ : s) = cx := by
    apply Subtype.ext
    exact harg
  rw [hinput] at hline
  simp only [radialMap, dif_neg hx]
  change a • (((f p : t) : F) - ((f c : t) : F)) =
    ((f cx : t) : F) - ((f c : t) : F)
  rw [hline, AffineMap.lineMap_apply_module]
  module

private theorem radialMap_midpoint_of_norm_lt
    {s : Set E} {t : Set F} (f : s ≃ᵢ t) (c : s) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) (hR : 0 < R) (hrq : r < R / 4)
    (hsball : ball (c : E) R ⊆ s)
    (htball : ball ((f c : t) : F) R ⊆ t)
    (x y : E) (hx : ‖x‖ < r) (hy : ‖y‖ < r) :
    radialMap f c r R hr hrR hsball (midpoint ℝ x y) =
      midpoint ℝ (radialMap f c r R hr hrR hsball x)
        (radialMap f c r R hr hrR hsball y) := by
  have hxb : x ∈ ball (0 : E) r := by simpa [mem_ball] using hx
  have hyb : y ∈ ball (0 : E) r := by simpa [mem_ball] using hy
  have hmb : midpoint ℝ x y ∈ ball (0 : E) r :=
    (convex_ball (0 : E) r).midpoint_mem hxb hyb
  have hmnorm : ‖midpoint ℝ x y‖ < r := by simpa [mem_ball] using hmb
  let xs : s := ⟨(c : E) + x, hsball (by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hx.trans hrR)⟩
  let ys : s := ⟨(c : E) + y, hsball (by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hy.trans hrR)⟩
  let ms : s := ⟨(c : E) + midpoint ℝ x y, hsball (by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hmnorm.trans hrR)⟩
  have hxsq : (xs : E) ∈ ball (c : E) (R / 4) := by
    rw [mem_ball]
    change dist ((c : E) + x) (c : E) < R / 4
    rw [dist_eq_norm, add_sub_cancel_left]
    exact hx.trans hrq
  have hysq : (ys : E) ∈ ball (c : E) (R / 4) := by
    rw [mem_ball]
    change dist ((c : E) + y) (c : E) < R / 4
    rw [dist_eq_norm, add_sub_cancel_left]
    exact hy.trans hrq
  have hfm := map_midpoint_of_mem_ball f c hR hsball htball
    xs ys hxsq hysq
  have hsource : midpoint ℝ (xs : E) (ys : E) = (ms : E) := by
    change midpoint ℝ ((c : E) + x) ((c : E) + y) =
      (c : E) + midpoint ℝ x y
    simp only [midpoint_eq_smul_add, invOf_eq_inv, smul_add]
    module
  have hinput :
      (⟨midpoint ℝ (xs : E) (ys : E), hsball (by
        rw [mem_ball]
        calc
          dist (midpoint ℝ (xs : E) (ys : E)) (c : E) ≤
              (dist (xs : E) (c : E) + dist (ys : E) (c : E)) / 2 := by
                simpa [dist_comm] using
                  dist_midpoint_midpoint_le (xs : E) (ys : E) (c : E) (c : E)
          _ < R := by rw [mem_ball] at hxsq hysq; linarith)⟩ : s) = ms := by
    apply Subtype.ext
    exact hsource
  rw [hinput] at hfm
  rw [radialMap_eq_sub_of_norm_lt f c r R hr hrR hR hrq hsball htball
      (midpoint ℝ x y) hmnorm,
    radialMap_eq_sub_of_norm_lt f c r R hr hrR hR hrq hsball htball x hx,
    radialMap_eq_sub_of_norm_lt f c r R hr hrR hR hrq hsball htball y hy]
  change ((f ms : t) : F) - ((f c : t) : F) =
    midpoint ℝ (((f xs : t) : F) - ((f c : t) : F))
      (((f ys : t) : F) - ((f c : t) : F))
  rw [hfm]
  simp only [midpoint_eq_smul_add, invOf_eq_inv]
  module

/-- An isometry between subsets that contain corresponding ambient balls has
an ambient affine-isometry extension on a smaller concentric ball. -/
theorem exists_affineExtension_eqOn_ball
    {s : Set E} {t : Set F} (f : s ≃ᵢ t) (c : s) {R : ℝ} (hR : 0 < R)
    (hsball : ball (c : E) R ⊆ s)
    (htball : ball ((f c : t) : F) R ⊆ t) :
    ∃ A : E ≃ᵃⁱ[ℝ] F, ∀ x : s,
      (x : E) ∈ ball (c : E) (R / 8) → A (x : E) = ((f x : t) : F) := by
  let r : ℝ := R / 8
  have hr : 0 < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r]; linarith
  have hrq : r < R / 4 := by dsimp [r]; linarith
  let T : E → F := radialMap f c r R hr hrR hsball
  have hT0 : T 0 = 0 := by simp [T]
  have hTnorm : ∀ x, ‖T x‖ = ‖x‖ := by
    intro x
    exact norm_radialMap f c r R hr hrR hsball x
  have hTmid : ∀ x y, T (midpoint ℝ x y) = midpoint ℝ (T x) (T y) :=
    map_midpoint_of_local_of_smul_pos T hr
      (fun a ha x ↦ radialMap_smul_of_pos f c r R hr hrR hsball ha x)
      (fun x y hx hy ↦
        radialMap_midpoint_of_norm_lt f c r R hr hrR hR hrq hsball htball
          x y hx hy)
  let L : E →ₗᵢ[ℝ] F := midpointLinearIsometry T hT0 hTmid hTnorm
  have hball_range : ball (0 : F) r ⊆
      ((LinearMap.range L.toLinearMap : Submodule ℝ F) : Set F) := by
    intro y hy
    rw [mem_ball] at hy
    have hynorm : ‖y‖ < r := by simpa using hy
    let yt : t := ⟨((f c : t) : F) + y, htball (by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hynorm.trans hrR)⟩
    let xs : s := f.symm yt
    let z : E := (xs : E) - (c : E)
    have hz : ‖z‖ < r := by
      change ‖(xs : E) - (c : E)‖ < r
      rw [← dist_eq_norm, ← Subtype.dist_eq, ← f.dist_eq, f.apply_symm_apply,
        Subtype.dist_eq]
      change dist (((f c : t) : F) + y) ((f c : t) : F) < r
      simpa [dist_eq_norm] using hynorm
    have hlocal := radialMap_eq_sub_of_norm_lt f c r R hr hrR hR hrq
      hsball htball z hz
    have hpoint :
        (⟨(c : E) + z, hsball (by
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
          exact hz.trans hrR)⟩ : s) = xs := by
      apply Subtype.ext
      dsimp [z]
      abel
    rw [hpoint, show f xs = yt from f.apply_symm_apply yt] at hlocal
    have hTy : T z = y := by
      change radialMap f c r R hr hrR hsball z = y
      change radialMap f c r R hr hrR hsball z =
        (((f c : t) : F) + y) - ((f c : t) : F) at hlocal
      simpa using hlocal
    refine ⟨z, ?_⟩
    change L z = y
    rw [coe_midpointLinearIsometry]
    exact hTy
  have hrange_interior :
      (interior ((LinearMap.range L.toLinearMap : Submodule ℝ F) : Set F)).Nonempty := by
    refine ⟨0, mem_interior_iff_mem_nhds.2 ?_⟩
    exact Filter.mem_of_superset (ball_mem_nhds (0 : F) hr) hball_range
  have hrange_top : LinearMap.range L.toLinearMap = ⊤ :=
    Submodule.eq_top_of_nonempty_interior' (LinearMap.range L.toLinearMap) hrange_interior
  have hsurj : Function.Surjective L := LinearMap.range_eq_top.mp hrange_top
  let e : E ≃ₗᵢ[ℝ] F := LinearIsometryEquiv.ofSurjective L hsurj
  let A : E ≃ᵃⁱ[ℝ] F := AffineIsometryEquiv.mk'
    (fun x : E ↦ e (x - (c : E)) + ((f c : t) : F)) e (c : E) (by
      intro x
      simp)
  refine ⟨A, ?_⟩
  intro x hx
  have hxnorm : ‖(x : E) - (c : E)‖ < r := by
    rw [mem_ball, dist_eq_norm] at hx
    exact hx
  have hlocal := radialMap_eq_sub_of_norm_lt f c r R hr hrR hR hrq
    hsball htball ((x : E) - (c : E)) hxnorm
  have hpoint :
      (⟨(c : E) + ((x : E) - (c : E)), hsball (by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
        exact hxnorm.trans hrR)⟩ : s) = x := by
    apply Subtype.ext
    abel_nf
  rw [hpoint] at hlocal
  change e ((x : E) - (c : E)) + ((f c : t) : F) = ((f x : t) : F)
  change L ((x : E) - (c : E)) + ((f c : t) : F) = ((f x : t) : F)
  rw [coe_midpointLinearIsometry]
  change radialMap f c r R hr hrR hsball ((x : E) - (c : E)) +
    ((f c : t) : F) = ((f x : t) : F)
  rw [hlocal]
  abel

end IsometryEquiv

end

end MathlibAnnex
