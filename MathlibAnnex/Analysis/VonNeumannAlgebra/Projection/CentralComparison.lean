/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import Mathlib.Order.Zorn
import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.Comparison
import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.OrthogonalSum
import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.CentralSplit

/-!
# Central comparison of internal projections

A maximal doubly orthogonal family of internal partial isometries is
summed over the net of all finite subsets. Its initial and final
projections are identified with the corresponding projection suprema.
The residual projections have orthogonal central supports, which gives
the central cut for comparison.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped BigOperators CStarAlgebra

namespace VonNeumannAlgebra

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A fixed left identity for every summand remains a left identity for
their strong sum. -/
theorem mul_strong_sum_eq_of_forall_mul_eq (M : VonNeumannAlgebra H)
    {ι : Type v} (p : ι → M.toStarSubalgebra) {q a : M.toStarSubalgebra}
    (hlim : ContinuousLinearMap.StronglyConverges
      (fun s : Finset ι ↦ ∑ i ∈ s, (p i : H →L[ℂ] H)) atTop (q : H →L[ℂ] H))
    (ha : ∀ i, a * p i = p i) : a * q = q := by
  classical
  have hfinite (s : Finset ι) :
      (a : H →L[ℂ] H) * (∑ i ∈ s, (p i : H →L[ℂ] H)) =
        ∑ i ∈ s, (p i : H →L[ℂ] H) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun x : M.toStarSubalgebra ↦ (x : H →L[ℂ] H)) (ha i)
  apply Subtype.ext
  ext ξ
  have hleft : Tendsto
      (fun s : Finset ι ↦
        ((a : H →L[ℂ] H) * (∑ i ∈ s, (p i : H →L[ℂ] H))) ξ)
      atTop (𝓝 ((a : H →L[ℂ] H) ((q : H →L[ℂ] H) ξ))) :=
    ((a : H →L[ℂ] H).continuous.tendsto _).comp (hlim ξ)
  have hleft' : Tendsto
      (fun s : Finset ι ↦ (∑ i ∈ s, (p i : H →L[ℂ] H)) ξ)
      atTop (𝓝 ((a : H →L[ℂ] H) ((q : H →L[ℂ] H) ξ))) := by
    simpa only [hfinite] using hleft
  exact tendsto_nhds_unique hleft' (hlim ξ)

/-- A projection which is the strong finite-subset sum of an orthogonal
projection family is precisely its supremum in the projection order. -/
theorem eq_iSupProjection_of_stronglyConverges_finset
    (M : VonNeumannAlgebra H) {ι : Type v}
    (p : ι → M.toStarSubalgebra) (hp : ∀ i, IsStarProjection (p i))
    (horth : Pairwise (fun i j ↦ p i * p j = 0))
    {q : M.toStarSubalgebra} (hq : IsStarProjection q)
    (hlim : ContinuousLinearMap.StronglyConverges
      (fun s : Finset ι ↦ ∑ i ∈ s, (p i : H →L[ℂ] H)) atTop (q : H →L[ℂ] H)) :
    q = iSupProjection M p hp := by
  classical
  have hupper (i : ι) : p i ≤ q := by
    apply ((hp i).le_iff_mul_eq_right hq).2
    have hfinite (s : Finset ι) (his : i ∈ s) :
        (∑ j ∈ s, (p j : H →L[ℂ] H)) * (p i : H →L[ℂ] H) =
          (p i : H →L[ℂ] H) := by
      rw [Finset.sum_mul]
      calc
        (∑ j ∈ s, (p j : H →L[ℂ] H) * (p i : H →L[ℂ] H)) =
            (p i : H →L[ℂ] H) * (p i : H →L[ℂ] H) := by
          apply Finset.sum_eq_single i
          · intro j _ hji
            exact congrArg (fun x : M.toStarSubalgebra ↦ (x : H →L[ℂ] H))
              (horth hji)
          · intro hnot
            exact (hnot his).elim
        _ = (p i : H →L[ℂ] H) :=
          congrArg (fun x : M.toStarSubalgebra ↦ (x : H →L[ℂ] H))
            (hp i).isIdempotentElem.eq
    apply Subtype.ext
    ext ξ
    have hevent : ∀ᶠ s : Finset ι in atTop,
        (∑ j ∈ s, (p j : H →L[ℂ] H)) ((p i : H →L[ℂ] H) ξ) =
          (p i : H →L[ℂ] H) ξ := by
      refine (eventually_ge_atTop ({i} : Finset ι)).mono ?_
      intro s hs
      exact congrArg (fun T : H →L[ℂ] H ↦ T ξ)
        (hfinite s (hs (by simp)))
    have hconstant : Tendsto
        (fun s : Finset ι ↦
          (∑ j ∈ s, (p j : H →L[ℂ] H)) ((p i : H →L[ℂ] H) ξ))
        atTop (𝓝 ((p i : H →L[ℂ] H) ξ)) :=
      (tendsto_congr' hevent).2 tendsto_const_nhds
    exact tendsto_nhds_unique (hlim ((p i : H →L[ℂ] H) ξ)) hconstant
  apply iSupProjection_unique M p hp hq hupper
  intro r hr hpr
  apply (hq.le_iff_mul_eq_right hr).2
  exact mul_strong_sum_eq_of_forall_mul_eq M p hlim
    (fun i ↦ ((hp i).le_iff_mul_eq_right hr).1 (hpr i))

/-- The internal strong orthogonal sum has initial and final projections
equal to the two arbitrary projection suprema. -/
theorem exists_orthogonal_sum_partial_isometry_with_sup
    (M : VonNeumannAlgebra H) {ι : Type v}
    (V : ι → M.toStarSubalgebra) (hV : ∀ i, IsPartialIsometry (V i))
    (hi : Pairwise (fun i j ↦ star (V i) * V j = 0))
    (hf : Pairwise (fun i j ↦ V i * star (V j) = 0)) :
    ∃ S : M.toStarSubalgebra, IsPartialIsometry S ∧
      star S * S = iSupProjection M (fun i ↦ star (V i) * V i)
        (fun i ↦ (hV i).isStarProjection_star_mul_self) ∧
      S * star S = iSupProjection M (fun i ↦ V i * star (V i))
        (fun i ↦ (hV i).isStarProjection_mul_star_self) := by
  obtain ⟨S, hS, _, _, _, hInitial, hFinal⟩ :=
    exists_orthogonal_sum_partial_isometry M V hV hi hf
  have horthI : Pairwise (fun i j ↦ (star (V i) * V i) * (star (V j) * V j) = 0) := by
    intro i j hij
    calc
      (star (V i) * V i) * (star (V j) * V j) =
          star (V i) * (V i * star (V j)) * V j := by simp only [mul_assoc]
      _ = 0 := by rw [hf hij, mul_zero, zero_mul]
  have horthF : Pairwise (fun i j ↦ (V i * star (V i)) * (V j * star (V j)) = 0) := by
    intro i j hij
    calc
      (V i * star (V i)) * (V j * star (V j)) =
          V i * (star (V i) * V j) * star (V j) := by simp only [mul_assoc]
      _ = 0 := by rw [hi hij, mul_zero, zero_mul]
  exact ⟨S, hS,
    eq_iSupProjection_of_stronglyConverges_finset M
      (fun i ↦ star (V i) * V i) (fun i ↦ (hV i).isStarProjection_star_mul_self)
      horthI hS.isStarProjection_star_mul_self hInitial,
    eq_iSupProjection_of_stronglyConverges_finset M
      (fun i ↦ V i * star (V i)) (fun i ↦ (hV i).isStarProjection_mul_star_self)
      horthF hS.isStarProjection_mul_star_self hFinal⟩

/-- Zorn's lemma supplies a maximal doubly orthogonal family whose
initial and final projections lie under two prescribed bounds. -/
theorem exists_maximal_bounded_orthogonal_partial_isometries
    (M : VonNeumannAlgebra H) (p q : M.toStarSubalgebra) :
    ∃ s : Set M.toStarSubalgebra,
      (∀ v ∈ s, IsPartialIsometry v ∧ star v * v ≤ p ∧ v * star v ≤ q) ∧
      s.Pairwise (fun v w ↦ star v * w = 0 ∧ v * star w = 0) ∧
      ∀ t : Set M.toStarSubalgebra,
        (∀ v ∈ t, IsPartialIsometry v ∧ star v * v ≤ p ∧ v * star v ≤ q) →
        t.Pairwise (fun v w ↦ star v * w = 0 ∧ v * star w = 0) →
        s ⊆ t → t ⊆ s := by
  classical
  let F : Set (Set M.toStarSubalgebra) := {s |
    (∀ v ∈ s, IsPartialIsometry v ∧ star v * v ≤ p ∧ v * star v ≤ q) ∧
    s.Pairwise (fun v w ↦ star v * w = 0 ∧ v * star w = 0)}
  have hchain : ∀ c ⊆ F, IsChain (· ⊆ ·) c →
      ∃ ub ∈ F, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hordered
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs ↦ Set.subset_sUnion_of_mem hs⟩
    · intro v hv
      obtain ⟨s, hs, hvs⟩ := Set.mem_sUnion.mp hv
      exact (hc hs).1 v hvs
    · intro v hv w hw hvw
      obtain ⟨s, hs, hvs⟩ := Set.mem_sUnion.mp hv
      obtain ⟨t, ht, hwt⟩ := Set.mem_sUnion.mp hw
      rcases hordered.total hs ht with hst | hts
      · exact (hc ht).2 (hst hvs) hwt hvw
      · exact (hc hs).2 hvs (hts hwt) hvw
  obtain ⟨s, hs⟩ := zorn_subset F hchain
  exact ⟨s, hs.1.1, hs.1.2, fun t hbound horth hst ↦ hs.2 ⟨hbound, horth⟩ hst⟩

private theorem mul_eq_zero_of_complementary_absorption
    {M : VonNeumannAlgebra H} {a b p e : M.toStarSubalgebra}
    (he : IsStarProjection e) (hep : e * p = e)
    (hae : a * e = a) (hb : (p - e) * b = b) : a * b = 0 := by
  have hcut : e * (p - e) = 0 := by
    rw [mul_sub, hep, he.isIdempotentElem.eq, sub_self]
  calc
    a * b = (a * e) * ((p - e) * b) := by rw [hae, hb]
    _ = a * (e * (p - e)) * b := by simp only [mul_assoc]
    _ = 0 := by rw [hcut, mul_zero, zero_mul]


/-- Two projections admit a maximal internal partial matching whose
unmatched remainders have orthogonal central supports. -/
theorem exists_partial_isometry_with_centrally_orthogonal_remainders
    (M : VonNeumannAlgebra H) {p q : M.toStarSubalgebra}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ∃ S : M.toStarSubalgebra, IsPartialIsometry S ∧
      star S * S ≤ p ∧ S * star S ≤ q ∧
      centralSupport M (p - star S * S) * centralSupport M (q - S * star S) = 0 := by
  classical
  obtain ⟨s, hs, horth, hmax⟩ :=
    exists_maximal_bounded_orthogonal_partial_isometries M p q
  let V : s → M.toStarSubalgebra := fun i ↦ i.1
  have hV : ∀ i, IsPartialIsometry (V i) := fun i ↦ (hs i.1 i.2).1
  have hi : Pairwise (fun i j ↦ star (V i) * V j = 0) := by
    intro i j hij
    exact (horth i.2 j.2 (fun heq ↦ hij (Subtype.ext heq))).1
  have hf : Pairwise (fun i j ↦ V i * star (V j) = 0) := by
    intro i j hij
    exact (horth i.2 j.2 (fun heq ↦ hij (Subtype.ext heq))).2
  obtain ⟨S, hS, hInitial, hFinal⟩ :=
    exists_orthogonal_sum_partial_isometry_with_sup M V hV hi hf
  let e : M.toStarSubalgebra := star S * S
  let f : M.toStarSubalgebra := S * star S
  have he : IsStarProjection e := hS.isStarProjection_star_mul_self
  have hprojf : IsStarProjection f := hS.isStarProjection_mul_star_self
  have hep_le : e ≤ p := by
    change star S * S ≤ p
    rw [hInitial]
    exact iSupProjection_le M (fun i ↦ star (V i) * V i)
      (fun i ↦ (hV i).isStarProjection_star_mul_self) hp
      (fun i ↦ (hs i.1 i.2).2.1)
  have hfq_le : f ≤ q := by
    change S * star S ≤ q
    rw [hFinal]
    exact iSupProjection_le M (fun i ↦ V i * star (V i))
      (fun i ↦ (hV i).isStarProjection_mul_star_self) hq
      (fun i ↦ (hs i.1 i.2).2.2)
  have hep : e * p = e := (he.le_iff_mul_eq_left hp).1 hep_le
  have hfq : f * q = f := (hprojf.le_iff_mul_eq_left hq).1 hfq_le
  have hInitialLower (v : M.toStarSubalgebra) (hv : v ∈ s) : star v * v ≤ e := by
    change star v * v ≤ star S * S
    rw [hInitial]
    exact le_iSupProjection M (fun i ↦ star (V i) * V i)
      (fun i ↦ (hV i).isStarProjection_star_mul_self) ⟨v, hv⟩
  have hFinalLower (v : M.toStarSubalgebra) (hv : v ∈ s) : v * star v ≤ f := by
    change v * star v ≤ S * star S
    rw [hFinal]
    exact le_iSupProjection M (fun i ↦ V i * star (V i))
      (fun i ↦ (hV i).isStarProjection_mul_star_self) ⟨v, hv⟩
  let r : M.toStarSubalgebra := p - e
  let t : M.toStarSubalgebra := q - f
  have hr : IsStarProjection r := he.sub_of_mul_eq_left hp hep
  have ht : IsStarProjection t := hprojf.sub_of_mul_eq_left hq hfq
  have hrp : r ≤ p := by
    apply (hr.le_iff_mul_eq_left hp).2
    change (p - e) * p = p - e
    rw [sub_mul, hp.isIdempotentElem.eq, hep]
  have htq : t ≤ q := by
    apply (ht.le_iff_mul_eq_left hq).2
    change (q - f) * q = q - f
    rw [sub_mul, hq.isIdempotentElem.eq, hfq]
  refine ⟨S, hS, hep_le, hfq_le, ?_⟩
  change centralSupport M r * centralSupport M t = 0
  apply centralSupport_mul_eq_zero_of_no_nonzero_equivalent_subprojections M hr ht
  intro r' t' heq hr'r ht't
  by_contra hr'0
  obtain ⟨w, hw, hwi, hwf⟩ := heq.2.2
  have hwbounds : IsPartialIsometry w ∧ star w * w ≤ p ∧ w * star w ≤ q := by
    refine ⟨hw, ?_, ?_⟩
    · rw [hwi]
      exact hr'r.trans hrp
    · rw [hwf]
      exact ht't.trans htq
  have hcross (v : M.toStarSubalgebra) (hv : v ∈ s) :
      star v * w = 0 ∧ v * star w = 0 := by
    have hvpi := (hs v hv).1
    have hve : (star v * v) * e = star v * v :=
      (hvpi.isStarProjection_star_mul_self.le_iff_mul_eq_left he).1
        (hInitialLower v hv)
    have hvf : (v * star v) * f = v * star v :=
      (hvpi.isStarProjection_mul_star_self.le_iff_mul_eq_left hprojf).1
        (hFinalLower v hv)
    have hri : (p - e) * (star w * w) = star w * w := by
      rw [hwi]
      exact (heq.1.le_iff_mul_eq_right hr).1 hr'r
    have htf : (q - f) * (w * star w) = w * star w := by
      rw [hwf]
      exact (heq.2.1.le_iff_mul_eq_right ht).1 ht't
    have horthI : (star v * v) * (star w * w) = 0 :=
      mul_eq_zero_of_complementary_absorption he hep hve hri
    have horthF : (v * star v) * (w * star w) = 0 :=
      mul_eq_zero_of_complementary_absorption hprojf hfq hvf htf
    exact ⟨hvpi.star_mul_eq_zero_of_final_mul_final_eq_zero hw horthF,
      hvpi.mul_star_eq_zero_of_initial_mul_initial_eq_zero hw horthI⟩
  have hcross' (v : M.toStarSubalgebra) (hv : v ∈ s) :
      star w * v = 0 ∧ w * star v = 0 := by
    constructor
    · simpa only [star_mul, star_star, star_zero] using congrArg star (hcross v hv).1
    · simpa only [star_mul, star_star, star_zero] using congrArg star (hcross v hv).2
  have hnewbounds : ∀ v ∈ insert w s,
      IsPartialIsometry v ∧ star v * v ≤ p ∧ v * star v ≤ q := by
    intro v hv
    rcases Set.mem_insert_iff.mp hv with rfl | hv
    · exact hwbounds
    · exact hs v hv
  have hneworth : (insert w s).Pairwise
      (fun v z ↦ star v * z = 0 ∧ v * star z = 0) := by
    intro v hv z hz hvz
    rcases Set.mem_insert_iff.mp hv with hvw | hvs
    · rcases Set.mem_insert_iff.mp hz with hzw | hzs
      · exact (hvz (hvw.trans hzw.symm)).elim
      · rw [hvw]
        exact hcross' z hzs
    · rcases Set.mem_insert_iff.mp hz with hzw | hzs
      · rw [hzw]
        exact hcross v hvs
      · exact horth hvs hzs hvz
  have hws : w ∈ s :=
    hmax (insert w s) hnewbounds hneworth (Set.subset_insert w s) (Set.mem_insert w s)
  apply hr'0
  rw [← hwi]
  exact (hcross w hws).1

/-- Multiplication by a central projection transports internal
equivalence, using the proved nonunital corner homomorphism. -/
theorem murrayVonNeumannEquivalent_mul_central
    (M : VonNeumannAlgebra H) {p q : M.toStarSubalgebra}
    (h : MurrayVonNeumannEquivalent p q)
    (z : M.toStarSubalgebra) (hz : IsStarProjection z)
    (hc : ∀ a : M.toStarSubalgebra, a * z = z * a) :
    MurrayVonNeumannEquivalent (p * z) (q * z) := by
  let φ : M.toStarSubalgebra →⋆ₙₐ[ℂ] M.toStarSubalgebra :=
    (NonUnitalStarSubalgebraClass.subtype (R := ℂ) (corner M z hz)).comp
      (centralCornerHom M z hz hc)
  have hφ := h.map φ
  change MurrayVonNeumannEquivalent (z * p) (z * q) at hφ
  simpa only [← hc p, ← hc q] using hφ

private theorem mul_central_le
    (M : VonNeumannAlgebra H) {a b : M.toStarSubalgebra}
    (ha : IsStarProjection a) (hb : IsStarProjection b) (hab : a ≤ b)
    (z : M.toStarSubalgebra) (hz : IsStarProjection z)
    (hc : ∀ x : M.toStarSubalgebra, x * z = z * x) : a * z ≤ b * z := by
  apply ((ha.mul hz (hc a)).le_iff_mul_eq_left (hb.mul hz (hc b))).2
  have hab' : a * b = a := (ha.le_iff_mul_eq_left hb).1 hab
  calc
    (a * z) * (b * z) = a * (z * b) * z := by simp only [mul_assoc]
    _ = a * (b * z) * z := by rw [← hc b]
    _ = (a * b) * (z * z) := by simp only [mul_assoc]
    _ = a * z := by rw [hab', hz.isIdempotentElem.eq]

/-- Central comparison of two projections in their specified von Neumann
algebra. On one central part `p` is subequivalent to `q`; on the
complementary central part the direction is reversed. -/
theorem exists_central_projection_comparison
    (M : VonNeumannAlgebra H) {p q : M.toStarSubalgebra}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ∃ z : M.toStarSubalgebra,
      IsStarProjection z ∧
      (∀ a : M.toStarSubalgebra, a * z = z * a) ∧
      MurrayVonNeumannSubequivalent (p * z) (q * z) ∧
      MurrayVonNeumannSubequivalent (q * (1 - z)) (p * (1 - z)) := by
  obtain ⟨S, hS, hep_le, hfq_le, hres⟩ :=
    exists_partial_isometry_with_centrally_orthogonal_remainders M hp hq
  let e : M.toStarSubalgebra := star S * S
  let f : M.toStarSubalgebra := S * star S
  let r : M.toStarSubalgebra := p - e
  let t : M.toStarSubalgebra := q - f
  let c : M.toStarSubalgebra := centralSupport M r
  let z : M.toStarSubalgebra := 1 - c
  have he : IsStarProjection e := hS.isStarProjection_star_mul_self
  have hf : IsStarProjection f := hS.isStarProjection_mul_star_self
  have hc : IsStarProjection c := isStarProjection_centralSupport M r
  have hcentral : ∀ a : M.toStarSubalgebra, a * c = c * a := centralSupport_commute M r
  have hz : IsStarProjection z := hc.one_sub
  have hzcentral : ∀ a : M.toStarSubalgebra, a * z = z * a :=
    one_sub_commutes M c hcentral
  have hrt : c * centralSupport M t = 0 := hres
  have htc : t * c = 0 := by
    calc
      t * c = (t * centralSupport M t) * c := by rw [self_mul_centralSupport]
      _ = t * (centralSupport M t * c) := mul_assoc _ _ _
      _ = t * (c * centralSupport M t) := by rw [hcentral (centralSupport M t)]
      _ = 0 := by rw [hrt, mul_zero]
  have hrz : r * z = 0 := by
    change r * (1 - centralSupport M r) = 0
    rw [mul_sub, mul_one, self_mul_centralSupport, sub_self]
  have hpe : p * z = e * z := by
    apply sub_eq_zero.mp
    simpa only [r, sub_mul] using hrz
  have hqf : q * c = f * c := by
    apply sub_eq_zero.mp
    simpa only [t, sub_mul] using htc
  have heq : MurrayVonNeumannEquivalent e f := ⟨he, hf, S, hS, rfl, rfl⟩
  have heqz : MurrayVonNeumannEquivalent (e * z) (f * z) :=
    murrayVonNeumannEquivalent_mul_central M heq z hz hzcentral
  have heqc : MurrayVonNeumannEquivalent (e * c) (f * c) :=
    murrayVonNeumannEquivalent_mul_central M heq c hc hcentral
  have hleft : MurrayVonNeumannSubequivalent (p * z) (q * z) := by
    apply murrayVonNeumannSubequivalent_iff_exists_le.mpr
    refine ⟨hq.mul hz (hzcentral q), f * z, ?_,
      mul_central_le M hf hq hfq_le z hz hzcentral⟩
    simpa only [hpe] using heqz
  have hright : MurrayVonNeumannSubequivalent (q * c) (p * c) := by
    apply murrayVonNeumannSubequivalent_iff_exists_le.mpr
    refine ⟨hp.mul hc (hcentral p), e * c, ?_,
      mul_central_le M he hp hep_le c hc hcentral⟩
    simpa only [hqf] using heqc.symm
  refine ⟨z, hz, hzcentral, hleft, ?_⟩
  simpa only [z, sub_sub_cancel] using hright

end VonNeumannAlgebra
