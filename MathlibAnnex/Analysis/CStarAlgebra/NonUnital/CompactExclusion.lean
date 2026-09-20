import Mathlib.RingTheory.TwoSidedIdeal.Operations
import MathlibAnnex.Analysis.CStarAlgebra.ClosedIdealCharacter
import MathlibAnnex.Analysis.CStarAlgebra.CompactPreimage
import MathlibAnnex.Analysis.CStarAlgebra.MaximalAbelianContaining
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.CompactRange
import MathlibAnnex.Analysis.InnerProductSpace.RankOne

/-!
# Excluding noncompact elements from a non-unital singleton model

If a represented self-adjoint element were noncompact, put it in a maximal
abelian subalgebra of the unitization.  The compact-preimage ideal in that
subalgebra is closed.  A character separating the element from this ideal is
non-scalar, hence is realized by a unit eigenvector.  The corresponding
rank-one projection is already in the range of the original algebra.  Its
operator commutes with the maximal abelian subalgebra, so faithfulness puts
the projection itself in that subalgebra.  The separating character must
then take both values zero and one on it, a contradiction.
-/

set_option autoImplicit false

open Set
open scoped ComplexOrder ComplexStarModule InnerProduct IsMulCommutative

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace NonUnitalCStarRepresentation

/-- If an operator-valued complex-linear map sends both real and imaginary
parts of an element to compact operators, it sends the element itself to a
compact operator. -/
private theorem isCompactOperator_of_realPart_of_imaginaryPart
    (pi : NonUnitalCStarRepresentation A H) (a : A)
    (hre : IsCompactOperator (pi (ℜ a : A)))
    (him : IsCompactOperator (pi (ℑ a : A))) :
    IsCompactOperator (pi a) := by
  have hsum : IsCompactOperator
      (pi (ℜ a : A) + Complex.I • pi (ℑ a : A)) :=
    hre.add (him.smul Complex.I)
  have hop : pi a = pi (ℜ a : A) + Complex.I • pi (ℑ a : A) := by
    calc
      pi a = pi ((ℜ a : A) + Complex.I • (ℑ a : A)) := by
        rw [realPart_add_I_smul_imaginaryPart]
      _ = pi (ℜ a : A) + Complex.I • pi (ℑ a : A) := by simp
  rw [hop]
  exact hsum

/-- A noncompact represented element has a self-adjoint part whose image is
still noncompact. -/
private theorem exists_selfAdjoint_not_isCompactOperator
    (pi : NonUnitalCStarRepresentation A H) {a : A}
    (ha : ¬ IsCompactOperator (pi a)) :
    ∃ b : A, IsSelfAdjoint b ∧ ¬ IsCompactOperator (pi b) := by
  by_cases hre : IsCompactOperator (pi (ℜ a : A))
  · refine ⟨(ℑ a : A), (ℑ a).property, ?_⟩
    intro him
    exact ha (isCompactOperator_of_realPart_of_imaginaryPart pi a hre him)
  · exact ⟨(ℜ a : A), (ℜ a).property, hre⟩

/-- In a genuinely non-unital separable singleton irreducible model every
represented operator is compact.  No simplicity assumption is used. -/
theorem isCompactOperator_map_of_singleton [Nontrivial A]
    [TopologicalSpace.SeparableSpace H]
    (pi : NonUnitalCStarRepresentation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi) :
    ∀ a : A, IsCompactOperator (pi a) := by
  intro a
  by_contra ha
  obtain ⟨b, hbself, hbcompact⟩ :=
    exists_selfAdjoint_not_isCompactOperator pi ha
  have hbinrself : IsSelfAdjoint (b : Unitization ℂ A) := hbself.inr ℂ
  obtain ⟨D, hD, hbD⟩ :=
    exists_maximalAbelian_containing_isSelfAdjoint
      (b : Unitization ℂ A) hbinrself
  letI : IsClosed (D : Set (Unitization ℂ A)) := hD.isClosed
  letI : IsMulCommutative D := hD.1
  letI : CommCStarAlgebra D := {}
  let rhoD : Representation D H := pi.unitization.comp D.subtype
  let Jtwo : TwoSidedIdeal D :=
    MathlibAnnex.CStarAlgebra.compactPreimageIdeal
      rhoD.toNonUnitalStarAlgHom
  let J : Ideal D := Jtwo.asIdeal
  have hJclosed : IsClosed (J : Set D) := by
    change IsClosed (Jtwo : Set D)
    exact MathlibAnnex.CStarAlgebra.isClosed_compactPreimageIdeal
      rhoD.toNonUnitalStarAlgHom
  let d : D := ⟨(b : Unitization ℂ A), hbD⟩
  have hdnot : d ∉ J := by
    intro hd
    have hdTwo : d ∈ Jtwo := hd
    have hcompact : IsCompactOperator (rhoD d) :=
      (MathlibAnnex.CStarAlgebra.mem_compactPreimageIdeal
        rhoD.toNonUnitalStarAlgHom d).1 hdTwo
    apply hbcompact
    simpa [rhoD, d] using hcompact
  obtain ⟨chi, hchiJ, hchid⟩ :=
    exists_character_annihilating_closedIdeal_of_not_mem J hJclosed hdnot
  have hchiInf : chi ≠ infinityCharacterOn (A := A) D := by
    intro heq
    apply hchid
    rw [heq]
    simp [d]
  obtain ⟨eta, heta, heigen⟩ :=
    exists_unit_eigenvector_of_character_ne_infinity
      pi hsingle D chi hchiInf
  obtain ⟨q, hq⟩ :=
    exists_preimage_rankOne_of_singleton pi hsingle eta eta
  have hinj : Function.Injective pi := injective_of_singleton pi hsingle
  have heta_ne : eta ≠ 0 := by
    intro hzero
    simp [hzero] at heta
  have hcommute (x : D) :
      (q : Unitization ℂ A) * (x : Unitization ℂ A) =
        (x : Unitization ℂ A) * (q : Unitization ℂ A) := by
    have hadj : ContinuousLinearMap.adjoint (rhoD x) eta =
        star (chi x) • eta := by
      have hadjmap : ContinuousLinearMap.adjoint (rhoD x) = rhoD (star x) := by
        rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
      rw [hadjmap]
      exact heigen (star x) |>.trans (by rw [map_star])
    have hoperator :
        rhoD x * InnerProductSpace.rankOne ℂ eta eta =
          InnerProductSpace.rankOne ℂ eta eta * rhoD x :=
      MathlibAnnex.Analysis.InnerProductSpace.commute_rankOne_self_of_apply_eq_smul_of_adjoint_apply_eq_star_smul
          (rhoD x) eta (chi x) (heigen x) hadj
    have hrhoD : rhoD x =
        (x : Unitization ℂ A).fst • (1 : H →L[ℂ] H) +
          pi (x : Unitization ℂ A).snd := by
      change pi.unitization (x : Unitization ℂ A) = _
      induction (x : Unitization ℂ A) using Unitization.ind with
      | inl_add_inr c y => simp [unitization, Algebra.algebraMap_eq_smul_one]
    have hpiComm :
        pi (x : Unitization ℂ A).snd *
            InnerProductSpace.rankOne ℂ eta eta =
          InnerProductSpace.rankOne ℂ eta eta *
            pi (x : Unitization ℂ A).snd := by
      apply add_left_cancel (a :=
        (x : Unitization ℂ A).fst •
          InnerProductSpace.rankOne ℂ eta eta)
      simpa [hrhoD, add_mul, mul_add, smul_mul_assoc, mul_smul_comm] using
        hoperator
    have hqCommA : q * (x : Unitization ℂ A).snd =
        (x : Unitization ℂ A).snd * q := by
      apply hinj
      simpa [map_mul, hq] using hpiComm.symm
    apply Unitization.ext
    · simp
    · simpa [hqCommA]
  have hqDmem : (q : Unitization ℂ A) ∈ D :=
    hD.mem_of_commute hcommute
  let r : D := ⟨(q : Unitization ℂ A), hqDmem⟩
  have hrJ : r ∈ J := by
    have hcompactr : IsCompactOperator (rhoD r) := by
      rw [show rhoD r = pi q by simp [rhoD, r], hq]
      exact isCompactOperator_rankOne eta eta
    have hrTwo : r ∈ Jtwo :=
      (MathlibAnnex.CStarAlgebra.mem_compactPreimageIdeal
        rhoD.toNonUnitalStarAlgHom r).2 hcompactr
    exact hrTwo
  have hchirZero : chi r = 0 := hchiJ r hrJ
  have hmapr : rhoD r = InnerProductSpace.rankOne ℂ eta eta := by
    simpa [rhoD, r] using hq
  have hprojectionEta :
      InnerProductSpace.rankOne ℂ eta eta eta = eta := by
    simp [InnerProductSpace.rankOne_apply,
      inner_self_eq_norm_sq_to_K, heta]
  have hchirOne : chi r = 1 := by
    apply smul_left_injective ℂ heta_ne
    calc
      chi r • eta = rhoD r eta := (heigen r).symm
      _ = InnerProductSpace.rankOne ℂ eta eta eta := by rw [hmapr]
      _ = eta := hprojectionEta
      _ = (1 : ℂ) • eta := (one_smul ℂ eta).symm
  exact one_ne_zero (hchirOne ▸ hchirZero)

end NonUnitalCStarRepresentation

end MathlibAnnex.Analysis.CStarAlgebra
