/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartSemilinear
import MathlibAnnex.Analysis.InnerProductSpace.MatrixCoefficient.Proportionality
import MathlibAnnex.Analysis.InnerProductSpace.ConjugateAdjoint

/-!
# Full continuity of coefficient transport

Unlike finite continuity, full continuity detects the concrete operator
subspace. The necessity proof takes the proper zero-incidence family of a
nonzero target operator. Non-density of its preimage supplies a nonzero
source operator, and the genuine operator proportionality theorem gives
membership of the pulled-back operator. The transfer identity below is an
explicit scalar identity; the following module supplies it using actual
linear and conjugate-linear adjoints.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable (T : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K))
variable [IsClosed (S : Set (H →L[ℂ] H))] [IsClosed (T : Set (K →L[ℂ] K))]
variable (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
variable (hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T))
variable {σ : ℂ →+* ℂ} [RingHomInvPair σ σ]
variable (hσ : ∀ c : ℂ, σ (star c) = star (σ c)) (U V : H ≃ₛₗ[σ] K)

/-- A zero-incidence family is closed for the original inherited normal-part closure. -/
theorem isClosed_normalPart_zeroIncidence (a : S) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).IsClosed
      {I : normalPart S | a ∈ I.val.val} := by
  apply (ClosureSpace.isClosed_iff_closure_subset _ _).2
  intro I hI
  exact (mem_normalPart_closure_iff S _ I).1 hI a (fun _ hJ => hJ)

include hS in
/-- A nonzero operator is excluded from at least one actual coefficient kernel. -/
theorem exists_normalPart_notMem (a : S) (ha : a ≠ 0) :
    ∃ I : normalPart S, a ∉ I.val.val := by
  classical
  have ha' : (a : H →L[ℂ] H) ≠ 0 := fun h => ha (Subtype.ext h)
  have hex : ∃ x : H, (a : H →L[ℂ] H) x ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha' (ContinuousLinearMap.ext h)
  obtain ⟨x, hx⟩ := hex
  have hx0 : x ≠ 0 := by intro h; subst x; exact hx (map_zero _)
  refine ⟨normalPartPoint S hS x ((a : H →L[ℂ] H) x) hx0 hx, ?_⟩
  change inner ℂ ((a : H →L[ℂ] H) x) ((a : H →L[ℂ] H) x) ≠ 0
  exact inner_self_ne_zero.mpr hx

include hS hσ in
/-- Full (all-subset) continuity is equivalent to concrete operator inclusion.
No assertion about full continuity is deduced merely from finite continuity. -/
theorem continuous_normalPartSemilinearMap_iff
    (Q : (K →L[ℂ] K) → (H →L[ℂ] H))
    (hQ : ∀ (b : K →L[ℂ] K) (x y : H),
      inner ℂ (V y) (b (U x)) = σ (inner ℂ y (Q b x))) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T))
      (normalPartSemilinearMap S T hT U V) ↔
      ∀ b : T, Q (b : K →L[ℂ] K) ∈ S := by
  classical
  have hzero (c : ℂ) : σ c = 0 ↔ c = 0 := by
    constructor
    · intro hc
      have hh := congrArg σ hc
      simpa only [RingHomInvPair.comp_apply_eq, map_zero] using hh
    · rintro rfl
      exact map_zero σ
  let P := normalPartSemilinearMap S T hT U V
  have htransport (I : normalPart S) (b : T) :
      b ∈ (P I).val.val ↔ inner ℂ (normalPartTarget S I)
        (Q (b : K →L[ℂ] K) (normalPartSource S I)) = 0 := by
    change inner ℂ (V (normalPartTarget S I))
      ((b : K →L[ℂ] K) (U (normalPartSource S I))) = 0 ↔ _
    rw [hQ]
    exact hzero _
  constructor
  · intro hcont b
    by_cases hb : b = 0
    · subst b
      have hQ0 : Q 0 = 0 := by
        ext x
        apply ext_inner_left ℂ
        intro y
        have hh := hQ 0 x y
        have hz : inner ℂ y (Q 0 x) = 0 := (hzero _).1 (by simpa using hh.symm)
        simpa only [ContinuousLinearMap.zero_apply, inner_zero_right] using hz
      change Q (0 : K →L[ℂ] K) ∈ S
      rw [hQ0]
      exact S.zero_mem
    let Z : Set (normalPart T) := {J | b ∈ J.val.val}
    let D : Set (normalPart S) := P ⁻¹' Z
    obtain ⟨J, hJ⟩ := exists_normalPart_notMem T hT b hb
    let e := normalPartSemilinearEquiv S T hS hT hσ U V
    let I : normalPart S := e.symm J
    have hPI : P I = J := e.apply_symm_apply J
    have hnondense : I ∉
        ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure D := by
      intro hi
      have hp := hcont D ⟨I, hi, rfl⟩
      have hz : b ∈ (P I).val.val :=
        (mem_normalPart_closure_iff T (P '' D) (P I)).1 hp b (by
          rintro L ⟨M, hM, rfl⟩
          exact hM)
      exact hJ (hPI ▸ hz)
    rw [mem_normalPart_closure_iff S D I] at hnondense
    push_neg at hnondense
    obtain ⟨a, haD, haI⟩ := hnondense
    have ha : (a : H →L[ℂ] H) ≠ 0 := by
      intro ha0
      apply haI
      rw [mem_normalPart_val_iff]
      simp only [ha0, ContinuousLinearMap.zero_apply, inner_zero_right]
    have himp : ∀ x y : H, inner ℂ y (Q (b : K →L[ℂ] K) x) = 0 →
        inner ℂ y ((a : H →L[ℂ] H) x) = 0 := by
      intro x y hxy
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      let L := normalPartPoint S hS x y hx hy
      have hLD : L ∈ D := by
        change b ∈ (normalPartSemilinearMap S T hT U V L).val.val
        rw [normalPartSemilinearMap_point S T hS hT hσ]
        change inner ℂ (V y) ((b : K →L[ℂ] K) (U x)) = 0
        rw [hQ, hxy, map_zero]
      exact haD L hLD
    obtain ⟨c, hc⟩ := ContinuousLinearMap.exists_eq_smul_of_forall_inner_eq_zero_imp
      (Q (b : K →L[ℂ] K)) (a : H →L[ℂ] H) himp
    have hc0 : c ≠ 0 := by
      intro h
      exact ha (by simpa [h] using hc)
    have hscale : Q (b : K →L[ℂ] K) = c⁻¹ • (a : H →L[ℂ] H) := by
      rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [hscale]
    exact SMulMemClass.smul_mem c⁻¹ a.property
  · intro hinc D J hJ
    obtain ⟨I, hI, rfl⟩ := hJ
    apply (mem_normalPart_closure_iff T _ _).2
    intro b hb
    let a : S := ⟨Q (b : K →L[ℂ] K), hinc b⟩
    apply (htransport I b).2
    apply (mem_normalPart_val_iff S I a).1
    apply (mem_normalPart_closure_iff S D I).1 hI a
    intro L hL
    apply (mem_normalPart_val_iff S L a).2
    exact (htransport L b).1 (hb (P L) ⟨L, hL, rfl⟩)

include hσ in
/-- Full continuity in both directions is exactly equality of the concrete
pulled-back operator subspace, once the explicit opposite coefficient identities hold. -/
theorem continuous_normalPartSemilinearMap_and_inverse_iff
    (Q : (K →L[ℂ] K) → (H →L[ℂ] H))
    (R : (H →L[ℂ] H) → (K →L[ℂ] K))
    (hQ : ∀ (b : K →L[ℂ] K) (x y : H),
      inner ℂ (V y) (b (U x)) = σ (inner ℂ y (Q b x)))
    (hR : ∀ (a : H →L[ℂ] H) (x y : K),
      inner ℂ (V.symm y) (a (U.symm x)) = σ (inner ℂ y (R a x))) :
    (((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
        ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T))
        (normalPartSemilinearMap S T hT U V) ∧
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).Continuous
        ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
        (normalPartSemilinearMap T S hS U.symm V.symm)) ↔
      Q '' (T : Set (K →L[ℂ] K)) = (S : Set (H →L[ℂ] H)) := by
  rw [continuous_normalPartSemilinearMap_iff S T hS hT hσ U V Q hQ,
    continuous_normalPartSemilinearMap_iff T S hT hS hσ U.symm V.symm R hR]
  have hQR := InnerProductSpace.leftInverse_of_inner_semilinear_transport U V Q R hQ hR
  have hRQ := InnerProductSpace.leftInverse_of_inner_semilinear_transport U.symm V.symm R Q hR hQ
  constructor
  · rintro ⟨hQmem, hRmem⟩
    apply Set.Subset.antisymm
    · rintro _ ⟨b, hb, rfl⟩
      exact hQmem ⟨b, hb⟩
    · intro a ha
      exact ⟨R a, hRmem ⟨a, ha⟩, hQR a⟩
  · intro heq
    constructor
    · intro b
      change Q b.val ∈ (S : Set (H →L[ℂ] H))
      rw [← heq]
      exact ⟨b, b.property, rfl⟩
    · intro a
      have ha : (a : H →L[ℂ] H) ∈ Q '' (T : Set (K →L[ℂ] K)) := heq.symm ▸ a.property
      obtain ⟨b, hb, hba⟩ := ha
      rw [← hba, hRQ b]
      exact hb

/-- Bundle the actual kernel equivalence as a full closure-space homeomorphism.
The operator-subspace equality is the concrete criterion, not an assumed
continuity or a field storing the theorem to be proved. -/
def normalPartSemilinearHomeomorphOfOperatorImage
    (Q : (K →L[ℂ] K) → (H →L[ℂ] H))
    (R : (H →L[ℂ] H) → (K →L[ℂ] K))
    (hQ : ∀ (b : K →L[ℂ] K) (x y : H),
      inner ℂ (V y) (b (U x)) = σ (inner ℂ y (Q b x)))
    (hR : ∀ (a : H →L[ℂ] H) (x y : K),
      inner ℂ (V.symm y) (a (U.symm x)) = σ (inner ℂ y (R a x)))
    (heq : Q '' (T : Set (K →L[ℂ] K)) = (S : Set (H →L[ℂ] H))) :
    ClosureSpace.Homeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) where
  toEquiv := normalPartSemilinearEquiv S T hS hT hσ U V
  continuous_toFun :=
    ((continuous_normalPartSemilinearMap_and_inverse_iff S T hS hT hσ U V Q R hQ hR).2 heq).1
  continuous_invFun :=
    ((continuous_normalPartSemilinearMap_and_inverse_iff S T hS hT hσ U V Q R hQ hR).2 heq).2

end MathlibAnnex.Analysis.CStarAlgebra
