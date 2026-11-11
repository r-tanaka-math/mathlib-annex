import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.HereditarySupport

/-! Typed consumers of the hereditary-to-support argument. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra.HereditarySupportConsumers

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance 100] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- Only separate WOT closure of the middle coefficients is required. -/
example (R : A → H →L[ℂ] H) (s T U : H →L[ℂ] H)
    (hcomm : ∀ a b, (s * R a * s) * (s * R b * s) =
      (s * R b * s) * (s * R a * s))
    (hT : ContinuousLinearMapWOT.ofCLM T ∈
      closure (Set.range (fun a => ContinuousLinearMapWOT.ofCLM (R a))))
    (hU : ContinuousLinearMapWOT.ofCLM U ∈
      closure (Set.range (fun a => ContinuousLinearMapWOT.ofCLM (R a)))) :
    (s * T * s) * (s * U * s) = (s * U * s) * (s * T * s) :=
  sandwiches_commute_of_mem_wotClosure_range R s hcomm hT hU

/-- A noninvertible self-adjoint sandwich operator is allowed. -/
example (M : VonNeumannAlgebra H) (s : M.toStarSubalgebra)
    (hs : IsSelfAdjoint s)
    (hcomm : ∀ x y : M.toStarSubalgebra,
      (s * x * s) * (s * y * s) = (s * y * s) * (s * x * s)) :
    M.IsAbelianProjection (M.leftSupport s) :=
  isAbelianProjection_leftSupport_of_sandwiches_commute M s hs hcomm

/-- A general representation is used with its actual WOT-generated algebra. -/
example (M : VonNeumannAlgebra H) (rho : A →⋆ₙₐ[ℂ] M.toStarSubalgebra)
    (hdense : ∀ T : M.toStarSubalgebra,
      ContinuousLinearMapWOT.ofCLM (T : H →L[ℂ] H) ∈
        closure (Set.range (fun b : A =>
          ContinuousLinearMapWOT.ofCLM (rho b : H →L[ℂ] H))))
    {a : A} (ha : IsAbelianPositiveElement a) :
    M.IsAbelianProjection (M.leftSupport (rho a)) :=
  ha.isAbelianProjection_leftSupport_of_wotDense M rho hdense

/-- The actual all-state envelope discharges density without a consumer premise. -/
example {a : A} (ha : IsAbelianPositiveElement a) :
    (envelopingVonNeumannAlgebra (A := A)).IsAbelianProjection
      ((envelopingVonNeumannAlgebra (A := A)).leftSupport (envelopingInclusion (A := A) a)) :=
  ha.isAbelianProjection_leftSupport_envelopingInclusion

/-- Arbitrary elements of the resulting support corner commute. -/
example {a : A} (ha : IsAbelianPositiveElement a)
    (x y : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra)
    (hpx : (envelopingVonNeumannAlgebra (A := A)).leftSupport
      (envelopingInclusion (A := A) a) * x = x)
    (hxp : x * (envelopingVonNeumannAlgebra (A := A)).leftSupport
      (envelopingInclusion (A := A) a) = x)
    (hpy : (envelopingVonNeumannAlgebra (A := A)).leftSupport
      (envelopingInclusion (A := A) a) * y = y)
    (hyp : y * (envelopingVonNeumannAlgebra (A := A)).leftSupport
      (envelopingInclusion (A := A) a) = y) : x * y = y * x :=
  ha.isAbelianProjection_leftSupport_envelopingInclusion.mul_comm hpx hxp hpy hyp

/-- The zero generator is included without a nonzero-algebra assumption. -/
example :
    (envelopingVonNeumannAlgebra (A := A)).IsAbelianProjection
      ((envelopingVonNeumannAlgebra (A := A)).leftSupport
        (envelopingInclusion (A := A) (0 : A))) :=
  (isAbelianPositiveElement_zero (A := A)).isAbelianProjection_leftSupport_envelopingInclusion

end MathlibAnnex.Analysis.CStarAlgebra.HereditarySupportConsumers
