/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

/-!
# Bounded right inverses of surjections with a Hilbert domain

Restrict a surjective bounded linear map to the orthogonal complement of its
kernel. This restriction is bijective, so the Banach inverse theorem provides
its bounded inverse. No splitting assertion for arbitrary Banach domains is
made. The codomain is allowed to be a Banach space, not necessarily a Hilbert
space. Zero spaces are included.
-/

set_option autoImplicit false
noncomputable section
open Set Function

universe uF uH uK

namespace ContinuousLinearMap

variable {𝕜 : Type uF} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {K : Type uK} [NormedAddCommGroup K] [NormedSpace 𝕜 K]
variable [hH : CompleteSpace H] [hK : CompleteSpace K]

include hH hK in
/-- The restriction of a surjection to the orthogonal complement of its kernel
is a continuous linear equivalence. Its bijectivity is proved before using the
bounded inverse theorem. -/
def kerOrthogonalEquiv (A : H →L[𝕜] K) (hA : Surjective A) : A.kerᗮ ≃L[𝕜] K := by
  letI : CompleteSpace A.ker := A.isClosed_ker.completeSpace_coe
  let q : A.kerᗮ →L[𝕜] K := A.comp A.kerᗮ.subtypeL
  have hi : Injective q := by
    intro x y hxy
    apply Subtype.ext
    have hz : (x : H) - (y : H) ∈ A.ker := by
      change A ((x : H) - (y : H)) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hxy
    have ho : (x : H) - (y : H) ∈ A.kerᗮ :=
      A.kerᗮ.sub_mem x.property y.property
    have hh : inner 𝕜 ((x : H) - (y : H)) ((x : H) - (y : H)) = 0 := ho _ hz
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hh)
  have hs : Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := hA y
    refine ⟨⟨x - A.ker.starProjection x,
      Submodule.sub_starProjection_mem_orthogonal (K := A.ker) x⟩, ?_⟩
    change A (x - A.ker.starProjection x) = y
    have hp : A (A.ker.starProjection x) = 0 :=
      A.ker.starProjection_apply_mem x
    rw [map_sub, hp, sub_zero, hx]
  exact (LinearEquiv.ofBijective q.toLinearMap ⟨hi, hs⟩).toContinuousLinearEquivOfContinuous
    (by exact q.continuous)

/-- The equivalence uses the original map, not a replacement operator. -/
@[simp]
theorem kerOrthogonalEquiv_apply (A : H →L[𝕜] K) (hA : Surjective A)
    (x : A.kerᗮ) : A.kerOrthogonalEquiv hA x = A x := rfl

include hH hK in
/-- A bounded right inverse taking values in the kernel's orthogonal complement. -/
def orthogonalRightInverse (A : H →L[𝕜] K) (hA : Surjective A) : K →L[𝕜] H :=
  A.kerᗮ.subtypeL.comp (A.kerOrthogonalEquiv hA).symm.toContinuousLinearMap

/-- The constructed inverse is an actual right inverse. -/
@[simp]
theorem apply_orthogonalRightInverse (A : H →L[𝕜] K) (hA : Surjective A) (y : K) :
    A (A.orthogonalRightInverse hA y) = y := by
  change A.kerOrthogonalEquiv hA ((A.kerOrthogonalEquiv hA).symm y) = y
  exact (A.kerOrthogonalEquiv hA).apply_symm_apply y

/-- Every value of the right inverse is orthogonal to the kernel. -/
theorem orthogonalRightInverse_mem_ker_orthogonal
    (A : H →L[𝕜] K) (hA : Surjective A) (y : K) :
    A.orthogonalRightInverse hA y ∈ A.kerᗮ :=
  ((A.kerOrthogonalEquiv hA).symm y).property

/-- The right-inverse equation as an equality of bounded linear maps. -/
@[simp]
theorem comp_orthogonalRightInverse (A : H →L[𝕜] K) (hA : Surjective A) :
    A.comp (A.orthogonalRightInverse hA) = ContinuousLinearMap.id 𝕜 K := by
  ext y
  exact A.apply_orthogonalRightInverse hA y

include hH hK in
/-- Existence of a bounded linear right inverse for a Hilbert-domain surjection. -/
theorem exists_orthogonal_rightInverse_of_surjective (A : H →L[𝕜] K) (hA : Surjective A) :
    ∃ R : K →L[𝕜] H, A.comp R = ContinuousLinearMap.id 𝕜 K ∧
      ∀ y, R y ∈ A.kerᗮ :=
  ⟨A.orthogonalRightInverse hA, A.comp_orthogonalRightInverse hA,
    A.orthogonalRightInverse_mem_ker_orthogonal hA⟩

/-- Uniqueness of the preimage orthogonal to the kernel. -/
theorem orthogonalRightInverse_eq_of_mem_ker_orthogonal
    (A : H →L[𝕜] K) (hA : Surjective A) (y : K)
    {x : H} (hx : x ∈ A.kerᗮ) (hxy : A x = y) :
    A.orthogonalRightInverse hA y = x := by
  have he : (A.kerOrthogonalEquiv hA).symm y = ⟨x, hx⟩ := by
    apply (A.kerOrthogonalEquiv hA).injective
    simpa only [ContinuousLinearEquiv.apply_symm_apply, kerOrthogonalEquiv_apply]
      using hxy.symm
  exact congrArg (fun z : A.kerᗮ => (z : H)) he

end ContinuousLinearMap
