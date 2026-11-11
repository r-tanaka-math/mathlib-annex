import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.Basic
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.Basic
import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.Support
import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeI.Basic

/-!
# Abelian hereditary algebras and their support corners

Commutativity of the original closed sandwich algebra gives commutativity
of represented sandwiches. Weak operator density extends this identity in
each middle variable separately. For a self-adjoint sandwich operator,
the resulting identity implies commutativity of its support corner.

The last step uses the existing support/kernel identity to cancel the
sandwich operator on its support. Commuting with its square and cancelling
twice replaces the use of inverse spectral cutoffs. No inverse of the
positive generator, bounded joint multiplication on WOT, or extra density
hypothesis for its hereditary algebra is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Commuting sandwiches extend to weak operator limits of the middle
coefficients. The two variables are closed successively, so only separate
continuity of multiplication is used. -/
theorem sandwiches_commute_of_mem_wotClosure_range
    {I : Type u} (R : I → H →L[ℂ] H) (s : H →L[ℂ] H)
    (hcomm : ∀ i j : I, (s * R i * s) * (s * R j * s) =
      (s * R j * s) * (s * R i * s))
    {T U : H →L[ℂ] H}
    (hT : ContinuousLinearMapWOT.ofCLM T ∈
      closure (Set.range (fun i : I => ContinuousLinearMapWOT.ofCLM (R i))))
    (hU : ContinuousLinearMapWOT.ofCLM U ∈
      closure (Set.range (fun i : I => ContinuousLinearMapWOT.ofCLM (R i)))) :
    (s * T * s) * (s * U * s) = (s * U * s) * (s * T * s) := by
  let sw : H →WOT[ℂ] H := ContinuousLinearMapWOT.ofCLM s
  have hfirst (i : I) :
      (sw * ContinuousLinearMapWOT.ofCLM (R i) * sw) *
          (sw * ContinuousLinearMapWOT.ofCLM U * sw) =
        (sw * ContinuousLinearMapWOT.ofCLM U * sw) *
          (sw * ContinuousLinearMapWOT.ofCLM (R i) * sw) := by
    apply closure_minimal ?_ (isClosed_eq
      (show Continuous (fun X : H →WOT[ℂ] H =>
        (sw * ContinuousLinearMapWOT.ofCLM (R i) * sw) * (sw * X * sw)) by fun_prop)
      (show Continuous (fun X : H →WOT[ℂ] H =>
        (sw * X * sw) * (sw * ContinuousLinearMapWOT.ofCLM (R i) * sw)) by
          fun_prop)) hU
    rintro _ ⟨j, rfl⟩
    exact congrArg ContinuousLinearMapWOT.ofCLM (hcomm i j)
  have hsecond :
      (sw * ContinuousLinearMapWOT.ofCLM T * sw) *
          (sw * ContinuousLinearMapWOT.ofCLM U * sw) =
        (sw * ContinuousLinearMapWOT.ofCLM U * sw) *
          (sw * ContinuousLinearMapWOT.ofCLM T * sw) := by
    apply closure_minimal ?_ (isClosed_eq
      (show Continuous (fun X : H →WOT[ℂ] H =>
        (sw * X * sw) * (sw * ContinuousLinearMapWOT.ofCLM U * sw)) by fun_prop)
      (show Continuous (fun X : H →WOT[ℂ] H =>
        (sw * ContinuousLinearMapWOT.ofCLM U * sw) * (sw * X * sw)) by
          fun_prop)) hT
    rintro _ ⟨i, rfl⟩
    exact hfirst i
  exact ContinuousLinearMapWOT.ofCLM_injective hsecond

private theorem support_left_cancel (M : VonNeumannAlgebra H)
    (s : M.toStarSubalgebra) (hs : IsSelfAdjoint s)
    {x y : M.toStarSubalgebra}
    (hx : M.leftSupport s * x = x) (hy : M.leftSupport s * y = y)
    (h : s * x = s * y) : x = y := by
  have hzero : s * (x - y) = 0 := by rw [mul_sub, h, sub_self]
  have hsupport : M.rightSupport s = M.leftSupport s := by
    rw [VonNeumannAlgebra.rightSupport, hs.star_eq]
  have hpzero : M.leftSupport s * (x - y) = 0 := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro xi
    change (M.leftSupport s : H →L[ℂ] H) (((x - y : M.toStarSubalgebra) : H →L[ℂ] H) xi) = 0
    rw [← hsupport]
    change (((x - y : M.toStarSubalgebra) : H →L[ℂ] H) xi) ∈
      (M.rightSupport s : H →L[ℂ] H).ker
    rw [VonNeumannAlgebra.ker_rightSupport]
    exact congrArg (fun z : M.toStarSubalgebra => (z : H →L[ℂ] H) xi) hzero
  rw [mul_sub, hx, hy] at hpzero
  exact sub_eq_zero.mp hpzero

private theorem support_right_cancel (M : VonNeumannAlgebra H)
    (s : M.toStarSubalgebra) (hs : IsSelfAdjoint s)
    {x y : M.toStarSubalgebra}
    (hx : x * M.leftSupport s = x) (hy : y * M.leftSupport s = y)
    (h : x * s = y * s) : x = y := by
  have hp : star (M.leftSupport s) = M.leftSupport s :=
    (M.isStarProjection_leftSupport s).isSelfAdjoint.star_eq
  have hx' : M.leftSupport s * star x = star x := by
    simpa only [star_mul, hp] using congrArg star hx
  have hy' : M.leftSupport s * star y = star y := by
    simpa only [star_mul, hp] using congrArg star hy
  have h' : s * star x = s * star y := by
    simpa only [star_mul, hs.star_eq] using congrArg star h
  have heq := support_left_cancel M s hs hx' hy' h'
  simpa only [star_star] using congrArg star heq

private theorem support_sandwich_cancel (M : VonNeumannAlgebra H)
    (s : M.toStarSubalgebra) (hs : IsSelfAdjoint s)
    {x y : M.toStarSubalgebra}
    (hpx : M.leftSupport s * x = x) (hxp : x * M.leftSupport s = x)
    (hpy : M.leftSupport s * y = y) (hyp : y * M.leftSupport s = y)
    (h : s * x * s = s * y * s) : x = y := by
  have hxs : x * s = y * s := support_left_cancel M s hs
    (by rw [← mul_assoc, hpx]) (by rw [← mul_assoc, hpy])
    (by simpa only [mul_assoc] using h)
  exact support_right_cancel M s hs hxp hyp hxs

/-- Commutativity of all sandwiches by a self-adjoint element forces its
actual support corner in the specified von Neumann algebra to be abelian. -/
theorem isAbelianProjection_leftSupport_of_sandwiches_commute
    (M : VonNeumannAlgebra H) (s : M.toStarSubalgebra) (hs : IsSelfAdjoint s)
    (hcomm : ∀ x y : M.toStarSubalgebra,
      (s * x * s) * (s * y * s) = (s * y * s) * (s * x * s)) :
    M.IsAbelianProjection (M.leftSupport s) := by
  have hps : M.leftSupport s * s = s := M.leftSupport_mul s
  have hsp : s * M.leftSupport s = s := by
    simpa only [VonNeumannAlgebra.rightSupport, hs.star_eq] using M.mul_rightSupport s
  have hcomm_sq (x : M.toStarSubalgebra)
      (hpx : M.leftSupport s * x = x) (hxp : x * M.leftSupport s = x) :
      x * (s * s) = (s * s) * x := by
    apply support_sandwich_cancel M s hs
    · rw [← mul_assoc, hpx]
    · simp only [mul_assoc, hsp]
    · simp only [← mul_assoc, hps]
    · rw [mul_assoc, hxp]
    · simpa only [mul_one, one_mul, mul_assoc] using hcomm x 1
  refine ⟨M.isStarProjection_leftSupport s, ?_⟩
  intro x y hpx hxp hpy hyp
  have hmiddle : x * (s * s) * y = y * (s * s) * x := by
    apply support_sandwich_cancel M s hs
    · simp only [← mul_assoc, hpx]
    · simp only [mul_assoc, hyp]
    · simp only [← mul_assoc, hpy]
    · simp only [mul_assoc, hxp]
    · simpa only [mul_assoc] using hcomm x y
  rw [hcomm_sq x hpx hxp, hcomm_sq y hpy hyp] at hmiddle
  have htwice : s * (s * (x * y)) = s * (s * (y * x)) := by
    simpa only [mul_assoc] using hmiddle
  have honce : s * (x * y) = s * (y * x) := support_left_cancel M s hs
    (by rw [← mul_assoc, hps]) (by rw [← mul_assoc, hps]) htwice
  exact support_left_cancel M s hs
    (by rw [← mul_assoc, hpx]) (by rw [← mul_assoc, hpy]) honce

variable {A : Type u} [NonUnitalCStarAlgebra A]

attribute [local instance 100] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- An abelian positive element has an abelian support corner in every
weakly generated representation. The hereditary algebra belongs to the
original source, and all corner variables belong to the target algebra. -/
theorem IsAbelianPositiveElement.isAbelianProjection_leftSupport_of_wotDense
    {a : A} (ha : IsAbelianPositiveElement a)
    (M : VonNeumannAlgebra H) (rho : A →⋆ₙₐ[ℂ] M.toStarSubalgebra)
    (hdense : ∀ T : M.toStarSubalgebra,
      ContinuousLinearMapWOT.ofCLM (T : H →L[ℂ] H) ∈
        closure (Set.range (fun b : A =>
          ContinuousLinearMapWOT.ofCLM (rho b : H →L[ℂ] H)))) :
    M.IsAbelianProjection (M.leftSupport (rho a)) := by
  apply isAbelianProjection_leftSupport_of_sandwiches_commute M (rho a)
    (ha.nonneg.isSelfAdjoint.map rho)
  intro T U
  apply Subtype.ext
  apply sandwiches_commute_of_mem_wotClosure_range
    (fun b : A => (rho b : H →L[ℂ] H)) (rho a) ?_ (hdense T) (hdense U)
  intro b c
  have hb : a * b * a ∈ hereditarySubalgebra a := by
    simpa only [ha.nonneg.isSelfAdjoint.star_eq] using
      sandwich_mem_hereditarySubalgebra a b
  have hc : a * c * a ∈ hereditarySubalgebra a := by
    simpa only [ha.nonneg.isSelfAdjoint.star_eq] using
      sandwich_mem_hereditarySubalgebra a c
  let f := M.toStarSubalgebra.subtype.toNonUnitalStarAlgHom.comp rho
  change f a * f b * f a * (f a * f c * f a) = f a * f c * f a * (f a * f b * f a)
  simpa only [map_mul] using congrArg f (ha.mul_comm hb hc)

/-- In the actual all-state envelope, the support of an original abelian
positive element is an abelian projection. Zero generators are included. -/
theorem IsAbelianPositiveElement.isAbelianProjection_leftSupport_envelopingInclusion
    {a : A} (ha : IsAbelianPositiveElement a) :
    (envelopingVonNeumannAlgebra (A := A)).IsAbelianProjection
      ((envelopingVonNeumannAlgebra (A := A)).leftSupport (envelopingInclusion (A := A) a)) := by
  apply ha.isAbelianProjection_leftSupport_of_wotDense
    (envelopingVonNeumannAlgebra (A := A)) (envelopingInclusion (A := A))
  intro T
  change ContinuousLinearMapWOT.ofCLM T.val ∈ closure (Set.range (fun a : A =>
    ContinuousLinearMapWOT.ofCLM (universalRepresentation (A := A) a)))
  simpa only [← Set.range_comp, Function.comp_def] using
    (mem_envelopingVonNeumannAlgebra_iff_mem_wotClosure T.val).mp T.property

end MathlibAnnex.Analysis.CStarAlgebra
