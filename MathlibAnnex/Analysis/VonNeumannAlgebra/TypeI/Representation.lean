/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeI.MinimalCorner
import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.CentralSupport
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.RepresentedBidualBall
import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.NormalExtension

/-!
# Irreducible restrictions of von Neumann algebras

The represented-bidual extension of the inclusion takes values in the
original algebra by the general containing-algebra theorem. The general
extension-intertwining theorem applies to the inclusion of a reducing
subspace. Consequently an irreducible reducing restriction is onto the full
bounded-operator algebra, using the proved bidual ball lifting theorem.
-/

set_option autoImplicit false
noncomputable section

open Set
open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.RepresentedBidual
open scoped CStarAlgebra

namespace VonNeumannAlgebra

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The represented bidual extension of the inclusion lands in the same
von Neumann algebra. This specializes the general containing-algebra theorem
to the canonical inclusion, with no image-membership hypothesis to supply. -/
theorem bidual_extension_subtype_mem (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (StrongDual ℂ M.toStarSubalgebra)) :
    extension M.toStarSubalgebra.subtype.toNonUnitalStarAlgHom F ∈ M :=
  MathlibAnnex.RepresentedBidual.extension_mem_vonNeumannAlgebra
    M.toStarSubalgebra.subtype.toNonUnitalStarAlgHom M (fun a ↦ a.property) F

/-- An irreducible reducing restriction of a von Neumann algebra has
literal full operator range. No normal-range-closedness assumption is used. -/
theorem surjective_restrict_to_reducing_of_irreducible
    (M : VonNeumannAlgebra H) (K : Submodule ℂ H) [CompleteSpace K] [Nontrivial K]
    (hK : Representation.Reduces M.toStarSubalgebra.subtype K)
    (hirr : StarAlgHom.IsIrreducible
      (Representation.restrictToReducing M.toStarSubalgebra.subtype K hK)) :
    Function.Surjective
      (Representation.restrictToReducing M.toStarSubalgebra.subtype K hK) := by
  let pi := M.toStarSubalgebra.subtype
  let rho := Representation.restrictToReducing pi K hK
  intro T
  obtain ⟨F, _, hFT⟩ := exists_extension_preimage_norm_le rho hirr T
  let a : M.toStarSubalgebra :=
    ⟨extension pi.toNonUnitalStarAlgHom F, bidual_extension_subtype_mem M F⟩
  refine ⟨a, ?_⟩
  apply ContinuousLinearMap.ext
  intro ξ
  apply Subtype.ext
  have hnatural : (a : H →L[ℂ] H) (ξ : H) =
      ((extension rho.toNonUnitalStarAlgHom F ξ : K) : H) :=
    congrArg (fun U : K →L[ℂ] H ↦ U ξ)
      (MathlibAnnex.RepresentedBidual.intertwines_extension
        rho.toNonUnitalStarAlgHom pi.toNonUnitalStarAlgHom K.subtypeL
        (fun b ↦ by
          apply ContinuousLinearMap.ext
          intro η
          rfl) F)
  change (a : H →L[ℂ] H) (ξ : H) = ((T ξ : K) : H)
  rw [hnatural, hFT]

/-- A minimal projection with full central support yields an actual
faithful irreducible cyclic restriction on a nonzero closed subspace of the
original Hilbert space. The corner scalar theorem is proved using von Neumann
closure, and faithfulness uses the full central support of the same projection. -/
theorem exists_faithful_irreducible_restriction_of_minimal_projection
    (M : VonNeumannAlgebra H) {p : M.toStarSubalgebra}
    (hp : IsMinimalStarProjection p) (hcentral : centralSupport M p = 1) :
    ∃ (K : Submodule ℂ H) (hKclosed : IsClosed (K : Set H)),
      letI : CompleteSpace K := hKclosed.completeSpace_coe
      ∃ hK : Representation.Reduces M.toStarSubalgebra.subtype K,
        Nontrivial K ∧
        Function.Injective (Representation.restrictToReducing M.toStarSubalgebra.subtype K hK) ∧
        StarAlgHom.IsIrreducible
          (Representation.restrictToReducing M.toStarSubalgebra.subtype K hK) := by
  classical
  have hsome : ¬ ∀ ξ : H, (p : H →L[ℂ] H) ξ = 0 := by
    intro h
    apply hp.2.1
    apply Subtype.ext
    ext ξ
    exact h ξ
  obtain ⟨ξ₀, hξ₀⟩ := not_forall.mp hsome
  let η : H := (p : H →L[ℂ] H) ξ₀
  have hη : η ≠ 0 := hξ₀
  have hpη : (p : H →L[ℂ] H) η = η :=
    congrArg (fun T : M.toStarSubalgebra ↦ (T : H →L[ℂ] H) ξ₀)
      hp.1.isIdempotentElem.eq
  let pi : Representation M.toStarSubalgebra H := M.toStarSubalgebra.subtype
  let K : Submodule ℂ H := Representation.cyclicSubspace pi η
  have hKclosed : IsClosed (K : Set H) := Representation.isClosed_cyclicSubspace pi η
  letI : CompleteSpace K := hKclosed.completeSpace_coe
  have hK : pi.Reduces K := Representation.reduces_cyclicSubspace pi η
  let rho : Representation M.toStarSubalgebra K := Representation.restrictToReducing pi K hK
  let e : K := ⟨η, Representation.self_mem_cyclicSubspace pi η⟩
  have he : e ≠ 0 := fun h ↦ hη (congrArg Subtype.val h)
  letI : Nontrivial K := ⟨⟨e, 0, he⟩⟩
  have hpe : rho p e = e := Subtype.ext hpη
  have hdense : DenseRange (StarAlgHom.orbitMap rho e) :=
    Representation.denseRange_orbitMap_restrictCyclic pi η
  have hline : ∀ ξ : K, rho p ξ ∈ ℂ ∙ e := by
    have hclosed : IsClosed {ξ : K | rho p ξ ∈ ℂ ∙ e} :=
      (Submodule.closed_of_finiteDimensional (ℂ ∙ e)).preimage (rho p).continuous
    have hsub : Set.range (StarAlgHom.orbitMap rho e) ⊆
        {ξ : K | rho p ξ ∈ ℂ ∙ e} := by
      rintro _ ⟨a, rfl⟩
      obtain ⟨c, hc⟩ := exists_scalar_corner_of_minimal_projection M hp a
      have h := congrArg (fun b : M.toStarSubalgebra ↦ rho b e) hc
      simp only [map_mul, FunLike.coe_mul_eq_comp, Function.comp_apply, map_smul,
        ContinuousLinearMap.smul_apply, hpe] at h
      exact Submodule.mem_span_singleton.mpr ⟨c, h.symm⟩
    exact fun ξ ↦ closure_minimal hsub hclosed (hdense ξ)
  have hirr : StarAlgHom.IsIrreducible rho := by
    intro L hL hLreduces
    letI : CompleteSpace L := hL.completeSpace_coe
    have hcomm (a : M.toStarSubalgebra) :
        L.starProjection * rho a = rho a * L.starProjection :=
      (hLreduces a).starProjection_commute
    have hpe' : rho p (L.starProjection e) = L.starProjection e := by
      calc
        rho p (L.starProjection e) = L.starProjection (rho p e) :=
          congrArg (fun T : K →L[ℂ] K ↦ T e) (hcomm p).symm
        _ = L.starProjection e := by rw [hpe]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hpe' ▸ hline (L.starProjection e))
    by_cases hc0 : c = 0
    · left
      have hPe : L.starProjection e = 0 := by simpa only [hc0, zero_smul] using hc.symm
      have hclosed : IsClosed {ξ : K | L.starProjection ξ = 0} :=
        isClosed_eq L.starProjection.continuous continuous_const
      have hsub : Set.range (StarAlgHom.orbitMap rho e) ⊆
          {ξ : K | L.starProjection ξ = 0} := by
        rintro _ ⟨a, rfl⟩
        calc
          L.starProjection (rho a e) = rho a (L.starProjection e) :=
            congrArg (fun T : K →L[ℂ] K ↦ T e) (hcomm a)
          _ = 0 := by rw [hPe, map_zero]
      have hzero : ∀ ξ : K, L.starProjection ξ = 0 :=
        fun ξ ↦ closure_minimal hsub hclosed (hdense ξ)
      apply le_antisymm
      · intro ξ hξ
        change ξ = 0
        exact (Submodule.starProjection_eq_self_iff.mpr hξ).symm.trans (hzero ξ)
      · exact bot_le
    · right
      have hce : c • e ∈ L := by rw [hc]; exact L.starProjection_apply_mem e
      have heL : e ∈ L := by
        have h := L.smul_mem c⁻¹ hce
        simpa only [smul_smul, inv_mul_cancel₀ hc0, one_smul] using h
      have hsub : Set.range (StarAlgHom.orbitMap rho e) ⊆ (L : Set K) := by
        rintro _ ⟨a, rfl⟩
        exact (hLreduces a).1 heL
      apply eq_top_iff.mpr
      intro ξ _
      exact closure_minimal hsub hL (hdense ξ)
  have hfaith : Function.Injective rho := by
    have hzero (a : M.toStarSubalgebra) (ha : rho a = 0) : a = 0 := by
      have hcorner_zero (b : M.toStarSubalgebra) : a * b * p = 0 := by
        let x : M.toStarSubalgebra := a * b * p
        have hxη : (x : H →L[ℂ] H) η = 0 := by
          have hr : rho x e = 0 := by
            simp only [x, map_mul, ha, zero_mul, ContinuousLinearMap.zero_apply]
          exact congrArg Subtype.val hr
        obtain ⟨c, hc⟩ := exists_scalar_corner_of_minimal_projection M hp
          (star (a * b) * (a * b))
        have hxx : star x * x = c • p := by
          calc
            star x * x = p * (star (a * b) * (a * b)) * p := by
              simp only [x, star_mul, hp.1.isSelfAdjoint.star_eq, mul_assoc]
            _ = c • p := hc
        have hce : c • η = 0 := by
          calc
            c • η = ((c • p : M.toStarSubalgebra) : H →L[ℂ] H) η := by
              change c • η = c • (p : H →L[ℂ] H) η
              rw [hpη]
            _ = ((star x * x : M.toStarSubalgebra) : H →L[ℂ] H) η := by rw [hxx]
            _ = 0 := by
              change star (x : H →L[ℂ] H) ((x : H →L[ℂ] H) η) = 0
              rw [hxη, map_zero]
        have hc0 : c = 0 := (smul_eq_zero.mp hce).resolve_right hη
        apply star_mul_self_eq_zero.mp
        change star x * x = 0
        rw [hxx, hc0, zero_smul]
      have hac : a * centralSupport M p = 0 := by
        apply (mul_centralHull_eq_zero_iff M {p} a).mpr
        intro p' hp' b
        have hp'p : p' = p := Set.mem_singleton_iff.mp hp'
        simpa only [hp'p] using hcorner_zero b
      simpa only [hcentral, mul_one] using hac
    intro a b hab
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hab, sub_self]
  exact ⟨K, hKclosed, hK, inferInstance, hfaith, hirr⟩

end VonNeumannAlgebra
