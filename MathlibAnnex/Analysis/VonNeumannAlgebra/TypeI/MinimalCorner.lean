/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.Basic
import MathlibAnnex.Analysis.CStarAlgebra.Ideal.MinimalCompactCorner
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CyclicRestriction
import MathlibAnnex.Analysis.CStarAlgebra.Schur

/-!
# Minimal projections have scalar corners in a von Neumann algebra

This conclusion uses von Neumann closure. The commutant acts irreducibly
on the range of a minimal projection: a closed reducing subspace would
give an internal subprojection by the bicommutant property. The existing
arbitrary-dimensional bounded Schur theorem then makes the corner scalar.
The scalar-corner proof for faithfully compact representations is not used.
-/

set_option autoImplicit false
noncomputable section

open Set
open MathlibAnnex.Analysis.CStarAlgebra
open scoped CStarAlgebra

namespace VonNeumannAlgebra

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A minimal internal projection of a concrete von Neumann algebra has
scalar corner. No compactness, finite rank, or separability is assumed. -/
theorem exists_scalar_corner_of_minimal_projection (M : VonNeumannAlgebra H)
    {p : M.toStarSubalgebra} (hp : IsMinimalStarProjection p)
    (a : M.toStarSubalgebra) : ∃ c : ℂ, p * a * p = c • p := by
  classical
  let K : Submodule ℂ H := (p : H →L[ℂ] H).range
  have hp' : IsStarProjection (p : H →L[ℂ] H) := hp.1.map M.toStarSubalgebra.subtype
  have hKclosed : IsClosed (K : Set H) :=
    ContinuousLinearMap.IsIdempotentElem.isClosed_range hp'.isIdempotentElem
  letI : CompleteSpace K := hKclosed.completeSpace_coe
  have hsome : ¬ ∀ ξ : H, (p : H →L[ℂ] H) ξ = 0 := by
    intro h
    apply hp.2.1
    apply Subtype.ext
    ext ξ
    exact h ξ
  obtain ⟨ξ₀, hξ₀⟩ := not_forall.mp hsome
  let η₀ : K := ⟨(p : H →L[ℂ] H) ξ₀, ⟨ξ₀, rfl⟩⟩
  letI : Nontrivial K := ⟨⟨η₀, 0, fun h ↦ hξ₀ (congrArg Subtype.val h)⟩⟩
  let pi : Representation M.commutant.toStarSubalgebra H :=
    M.commutant.toStarSubalgebra.subtype
  have hKinvariant (y : H →L[ℂ] H) (hy : y ∈ M.commutant) :
      Set.MapsTo y K K := by
    rintro ξ ⟨η, rfl⟩
    refine ⟨y η, ?_⟩
    exact congrArg (fun T : H →L[ℂ] H ↦ T η)
      ((mem_commutant_iff.mp hy) p p.property)
  have hKreduces : pi.Reduces K := by
    refine ⟨hKclosed, ?_⟩
    intro y ξ hξ
    refine ⟨hKinvariant y y.property hξ, ?_⟩
    change (ContinuousLinearMap.adjoint (y : H →L[ℂ] H)) ξ ∈ (K : Set H)
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      hKinvariant (star (y : H →L[ℂ] H)) (star_mem y.property) hξ
  let rho : Representation M.commutant.toStarSubalgebra K :=
    Representation.restrictToReducing pi K hKreduces
  have hirr : StarAlgHom.IsIrreducible rho := by
    intro L hL hLreduces
    let J : Submodule ℂ H := L.map K.subtype
    have hJclosed : IsClosed (J : Set H) :=
      hKclosed.isClosedMap_subtype_val (L : Set K) hL
    letI : CompleteSpace J := hJclosed.completeSpace_coe
    have hJinvariant (y : H →L[ℂ] H) (hy : y ∈ M.commutant) :
        J ∈ Module.End.invtSubmodule y.toLinearMap := by
      rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
      rintro ξ ⟨η, hη, rfl⟩
      refine ⟨rho ⟨y, hy⟩ η, (hLreduces ⟨y, hy⟩).1 hη, ?_⟩
      rfl
    let q : M.toStarSubalgebra :=
      ⟨J.starProjection, starProjection_mem M J hJinvariant⟩
    have hq : IsStarProjection q := by
      have h : IsStarProjection J.starProjection := isStarProjection_starProjection
      exact ⟨Subtype.ext h.isIdempotentElem.eq, Subtype.ext h.isSelfAdjoint.star_eq⟩
    have hqp : q ≤ p := by
      apply (projection_le_iff_range_le M hq hp.1).mpr
      change J.starProjection.range ≤ K
      rw [Submodule.range_starProjection]
      rintro ξ ⟨η, _, rfl⟩
      exact η.property
    by_cases hq0 : q = 0
    · left
      apply le_antisymm
      · intro η hη
        change η = 0
        apply Subtype.ext
        have hηJ : (η : H) ∈ J := ⟨η, hη, rfl⟩
        have hfix : J.starProjection (η : H) = (η : H) :=
          Submodule.starProjection_eq_self_iff.mpr hηJ
        have hzero : J.starProjection (η : H) = 0 :=
          congrArg (fun T : M.toStarSubalgebra ↦ (T : H →L[ℂ] H) (η : H)) hq0
        exact hfix.symm.trans hzero
      · exact bot_le
    · right
      have hqp_eq : q = p := hp.2.2 q hq hq0 hqp
      apply eq_top_iff.mpr
      intro η _
      have hηJ : (η : H) ∈ J := by
        rw [← Submodule.range_starProjection J]
        change (η : H) ∈ (q : H →L[ℂ] H).range
        rw [hqp_eq]
        exact η.property
      obtain ⟨ζ, hζ, hζη⟩ := hηJ
      have hζη' : ζ = η := Subtype.ext hζη
      exact hζη' ▸ hζ
  let b : M.toStarSubalgebra := p * a * p
  have hpb : p * b = b := by
    change p * (p * a * p) = p * a * p
    calc
      p * (p * a * p) = (p * p) * a * p := by simp only [mul_assoc]
      _ = p * a * p := by rw [hp.1.isIdempotentElem.eq]
  have hbp : b * p = b := by
    change (p * a * p) * p = p * a * p
    rw [mul_assoc, hp.1.isIdempotentElem.eq]
  have hbK : ∀ ξ : H, ξ ∈ K → (b : H →L[ℂ] H) ξ ∈ K := by
    intro ξ _
    refine ⟨(b : H →L[ℂ] H) ξ, ?_⟩
    exact congrArg (fun T : M.toStarSubalgebra ↦ (T : H →L[ℂ] H) ξ) hpb
  let B : K →L[ℂ] K := (b : H →L[ℂ] H).restrict hbK
  have hcomm : StarAlgHom.InCommutant rho B := by
    intro y
    apply ContinuousLinearMap.ext
    intro ξ
    apply Subtype.ext
    exact congrArg (fun T : H →L[ℂ] H ↦ T (ξ : H))
      ((mem_commutant_iff.mp y.property) b b.property)
  obtain ⟨c, hc⟩ := StarAlgHom.eq_algebraMap_of_irreducible rho hirr B hcomm
  refine ⟨c, ?_⟩
  change b = c • p
  apply Subtype.ext
  ext ξ
  let η : K := ⟨(p : H →L[ℂ] H) ξ, ⟨ξ, rfl⟩⟩
  have hpoint := congrArg (fun T : K →L[ℂ] K ↦ ((T η : K) : H)) hc
  change (b : H →L[ℂ] H) ((p : H →L[ℂ] H) ξ) =
    c • (p : H →L[ℂ] H) ξ at hpoint
  calc
    (b : H →L[ℂ] H) ξ = (b : H →L[ℂ] H) ((p : H →L[ℂ] H) ξ) :=
      (congrArg (fun T : M.toStarSubalgebra ↦ (T : H →L[ℂ] H) ξ) hbp).symm
    _ = c • (p : H →L[ℂ] H) ξ := hpoint

end VonNeumannAlgebra
