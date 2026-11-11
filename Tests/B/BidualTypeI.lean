import MathlibAnnex.Analysis.CStarAlgebra.TypeI.Bidual

/-! Typed consumers connect internal type I with the literal Banach bidual. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Set
open MathlibAnnex.RepresentedBidual
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra.BidualTypeIConsumers

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance 100] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- The endpoint has no separability, unit, order or supplied representation premise. -/
example (hA : IsInternalTypeI A) : IsTypeIBidual A :=
  hA.isTypeIBidual

/-- The stronger intermediate conclusion applies to any weakly generated algebra. -/
example (hA : IsInternalTypeI A)
    (M : VonNeumannAlgebra H) (rho : A →⋆ₙₐ[ℂ] M.toStarSubalgebra)
    (hdense : ∀ T : M.toStarSubalgebra,
      ContinuousLinearMapWOT.ofCLM (T : H →L[ℂ] H) ∈
        closure (Set.range (fun a : A =>
          ContinuousLinearMapWOT.ofCLM (rho a : H →L[ℂ] H)))) :
    M.IsTypeI :=
  hA.isTypeI_of_wotDense M rho hdense

/-- Every nonzero envelope projection dominates a nonzero internal abelian one. -/
example (hA : IsInternalTypeI A)
    (p : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra)
    (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra,
      (envelopingVonNeumannAlgebra (A := A)).IsAbelianProjection q ∧
        q ≠ 0 ∧ q * p = q :=
  hA.isTypeI_envelopingVonNeumannAlgebra p hp hp0

/-- The conclusion is consumed directly on literal double strong duals. -/
example (hA : IsInternalTypeI A) (P : StrongDual ℂ (StrongDual ℂ A))
    (hPP : arensProduct P P = P) (hPs : bidualStar P = P) (hP0 : P ≠ 0) :
    ∃ Q : StrongDual ℂ (StrongDual ℂ A),
      arensProduct Q Q = Q ∧ bidualStar Q = Q ∧ Q ≠ 0 ∧
      arensProduct Q P = Q ∧
      ∀ X Y : StrongDual ℂ (StrongDual ℂ A),
        arensProduct Q X = X → arensProduct X Q = X →
        arensProduct Q Y = Y → arensProduct Y Q = Y →
        arensProduct X Y = arensProduct Y X :=
  (isTypeIBidual_iff_arensProduct (A := A)).mp hA.isTypeIBidual P hPP hPs hP0

/-- The original bidual operations characterize projections in the represented model. -/
example (P : StrongDual ℂ (StrongDual ℂ A)) :
    IsStarProjection (bidualEnvelopingEquiv (A := A) P) ↔
      arensProduct P P = P ∧ bidualStar P = P :=
  isStarProjection_bidualEnvelopingEquiv_iff P

/-- An abelian positive element yields an actual inverse-image projection,
with its original bidual norm and a commutative raw Arens corner. -/
example {a : A} (ha : IsAbelianPositiveElement a) :
    ∃ Q : StrongDual ℂ (StrongDual ℂ A),
      bidualEnvelopingEquiv (A := A) Q =
        (envelopingVonNeumannAlgebra (A := A)).leftSupport (envelopingInclusion (A := A) a) ∧
      ‖Q‖ = ‖(envelopingVonNeumannAlgebra (A := A)).leftSupport
        (envelopingInclusion (A := A) a)‖ ∧
      arensProduct Q Q = Q ∧ bidualStar Q = Q ∧
      ∀ X Y : StrongDual ℂ (StrongDual ℂ A),
        arensProduct Q X = X → arensProduct X Q = X →
        arensProduct Q Y = Y → arensProduct Y Q = Y →
        arensProduct X Y = arensProduct Y X := by
  let p := (envelopingVonNeumannAlgebra (A := A)).leftSupport (envelopingInclusion (A := A) a)
  let E := bidualEnvelopingEquiv (A := A)
  have hp : (envelopingVonNeumannAlgebra (A := A)).IsAbelianProjection p :=
    ha.isAbelianProjection_leftSupport_envelopingInclusion
  have hraw := (isAbelianProjection_bidualEnvelopingEquiv_iff (A := A) (E.symm p)).mp
    (by simpa only [E, LinearIsometryEquiv.apply_symm_apply] using hp)
  exact ⟨E.symm p, E.apply_symm_apply p, E.symm.norm_map p,
    hraw.1, hraw.2.1, hraw.2.2⟩

/-- A zero source algebra stays within the theorem's actual scope. -/
example [Subsingleton A] : IsTypeIBidual A :=
  (isInternalTypeI_of_subsingleton (A := A)).isTypeIBidual

/-- Nonunital commutative C-star algebras are included through the existing
internal quotient theorem, without a unitization of the conclusion. -/
example (hcomm : ∀ x y : A, x * y = y * x) : IsTypeIBidual A :=
  (isInternalTypeI_of_commutative hcomm).isTypeIBidual

end MathlibAnnex.Analysis.CStarAlgebra.BidualTypeIConsumers
