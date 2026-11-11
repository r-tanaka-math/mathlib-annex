import MathlibAnnex.Analysis.CStarAlgebra.TypeI.QuotientPureState

set_option autoImplicit false
noncomputable section

open Set
open scoped ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
variable [PartialOrder D] [StarOrderedRing D]

private theorem isClosed_starHom_range {X Y : Type*} [CStarAlgebra X] [CStarAlgebra Y]
    (r : X →⋆ₐ[ℂ] Y) : IsClosed (r.range : Set Y) := by
  letI := _root_.CStarAlgebra.spectralOrder X
  letI := _root_.CStarAlgebra.spectralOrderedRing X
  letI := _root_.CStarAlgebra.spectralOrder Y
  letI := _root_.CStarAlgebra.spectralOrderedRing Y
  exact HomKernelQuotient.isClosed_image r.toNonUnitalStarAlgHom

-- The state lives on the literal algebraic image inside the actual quotient,
-- with the inherited norm and a proved closedness instance. Its pullback is
-- the prescribed pure state on D, and norm one is an explicit conclusion.
example (phi : D →L[ℂ] ℂ) (hphi : IsPureState D phi)
    (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (hker : ∀ d : D, (d : A) ∈ J →
      (positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom d = 0) :
    letI := ClosedIdealQuotient.quotientCStarAlgebra J hJ
    let orderQ : PartialOrder (ClosedIdealQuotient.Quotient J hJ) :=
      _root_.CStarAlgebra.spectralOrder (ClosedIdealQuotient.Quotient J hJ)
    letI : LE (ClosedIdealQuotient.Quotient J hJ) := orderQ.toLE
    letI : LT (ClosedIdealQuotient.Quotient J hJ) := orderQ.toLT
    letI : PartialOrder (ClosedIdealQuotient.Quotient J hJ) := orderQ
    letI : StarOrderedRing (ClosedIdealQuotient.Quotient J hJ) :=
      _root_.CStarAlgebra.spectralOrderedRing (ClosedIdealQuotient.Quotient J hJ)
    let q := ClosedIdealQuotient.mkStarAlgHom J hJ
    let r := q.comp D.subtype
    let E := r.range
    letI : IsClosed (E : Set (ClosedIdealQuotient.Quotient J hJ)) :=
      isClosed_starHom_range r
    let orderE : PartialOrder E := _root_.CStarAlgebra.spectralOrder E
    letI : LE E := orderE.toLE
    letI : LT E := orderE.toLT
    letI : PartialOrder E := orderE
    letI : StarOrderedRing E := _root_.CStarAlgebra.spectralOrderedRing E
    ∃ eta : E →L[ℂ] ℂ,
      eta ∈ stateSpace E ∧ IsPureState E eta ∧ ‖eta‖ = 1 ∧
      ∀ d : D, eta (r.rangeRestrict d) = phi d := by
  letI := ClosedIdealQuotient.quotientCStarAlgebra J hJ
  let orderQ : PartialOrder (ClosedIdealQuotient.Quotient J hJ) :=
    _root_.CStarAlgebra.spectralOrder (ClosedIdealQuotient.Quotient J hJ)
  letI : LE (ClosedIdealQuotient.Quotient J hJ) := orderQ.toLE
  letI : LT (ClosedIdealQuotient.Quotient J hJ) := orderQ.toLT
  letI : PartialOrder (ClosedIdealQuotient.Quotient J hJ) := orderQ
  letI : StarOrderedRing (ClosedIdealQuotient.Quotient J hJ) :=
    _root_.CStarAlgebra.spectralOrderedRing (ClosedIdealQuotient.Quotient J hJ)
  let q := ClosedIdealQuotient.mkStarAlgHom J hJ
  let r := q.comp D.subtype
  let E := r.range
  letI : IsClosed (E : Set (ClosedIdealQuotient.Quotient J hJ)) :=
    isClosed_starHom_range r
  let orderE : PartialOrder E := _root_.CStarAlgebra.spectralOrder E
  letI : LE E := orderE.toLE
  letI : LT E := orderE.toLT
  letI : PartialOrder E := orderE
  letI : StarOrderedRing E := _root_.CStarAlgebra.spectralOrderedRing E
  have hr : Function.Surjective r.rangeRestrict := by
    intro b
    obtain ⟨d, hd⟩ := b.property
    exact ⟨d, Subtype.ext hd⟩
  apply exists_pure_state_descent_of_surjective r.rangeRestrict hr phi hphi
  intro d hd
  apply hker d
  apply (ClosedIdealQuotient.mkStarAlgHom_eq_zero_iff J hJ (d : A)).1
  exact congrArg Subtype.val hd

-- The extension has the original D-values, and every element of J acts as
-- zero on the entire ambient GNS Hilbert space.
example (phi : D →L[ℂ] ℂ) (hphi : IsPureState D phi)
    (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (hker : ∀ d : D, (d : A) ∈ J →
      (positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom d = 0) :
    ∃ (psi : A →L[ℂ] ℂ) (hpsi : psi ∈ stateSpace A),
      IsPureState A psi ∧ ‖psi‖ = 1 ∧ (∀ d : D, psi d = phi d) ∧
      ∀ a : A, a ∈ J →
        (positiveLinearMapOfMemStateSpace psi hpsi).gnsStarAlgHom a = 0 := by
  obtain ⟨psi, hpsi, hpure, hext, hann⟩ :=
    exists_pure_state_extension_annihilating_ideal D phi hphi J hJ hker
  exact ⟨psi, hpsi, hpure, norm_eq_one_of_mem_stateSpace psi hpsi, hext, hann⟩

-- Compatibility with a normalized state itself excludes the whole ideal;
-- no unproved properness hypothesis is added to the extension theorem.
example (phi : D →L[ℂ] ℂ) (hphi : IsPureState D phi)
    (J : TwoSidedIdeal A)
    (hker : ∀ d : D, (d : A) ∈ J →
      (positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom d = 0) :
    J ≠ ⊤ := by
  intro htop
  have hmem : ((1 : D) : A) ∈ J := by rw [htop]; trivial
  have hzero := hker (1 : D) hmem
  have hcoeff := inner_gnsStarAlgHom_stateGNSVector phi hphi.1 (1 : D)
  rw [hzero] at hcoeff
  have hphi_zero : phi 1 = 0 := by simpa using hcoeff.symm
  exact one_ne_zero (hphi.1.2.symm.trans hphi_zero)

-- Pure pullback is checked on every source element, not only on a quotient
-- representative chosen by the construction.
example {B : Type v} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (theta : B →L[ℂ] ℂ) (htheta : IsPureState B theta) :
    ∃ psi : A →L[ℂ] ℂ,
      IsPureState A psi ∧ ‖psi‖ = 1 ∧
      (∀ a : A, psi a = theta (q a)) ∧
      ∀ a : A, q a = 0 → psi a = 0 := by
  obtain ⟨psi, hpsi, hpure, hnorm, hpull⟩ :=
    exists_pure_state_pullback_of_surjective q hq theta htheta
  refine ⟨psi, hpure, hnorm, hpull, ?_⟩
  intro a ha
  rw [hpull, ha, map_zero]

end MathlibAnnex.Analysis.CStarAlgebra
