import Mathlib.RingTheory.TwoSidedIdeal.Operations
import MathlibAnnex.Analysis.CStarAlgebra.ClosedIdealCharacter
import MathlibAnnex.Analysis.CStarAlgebra.CompactPreimage
import MathlibAnnex.Analysis.CStarAlgebra.MaximalAbelianContaining
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.CompactRange
import MathlibAnnex.Analysis.InnerProductSpace.RankOne

/-!
# Compactness from rank-one preimages in a singleton model

This extracts the part of the original Rosenberg proof that uses no density
or separability assumption.  The only range input is a preimage for every
rank-one operator.  It does not assume simplicity of the nonunital algebra.
-/

set_option autoImplicit false

open Set
open scoped ComplexOrder ComplexStarModule InnerProduct IsMulCommutative

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace NonUnitalCStarRepresentation

/-- Decompose the represented value of a unitized element. -/
private theorem unitization_apply_eq_fst_smul_add
    (pi : NonUnitalCStarRepresentation A H) (z : Unitization ℂ A) :
    pi.unitization z = z.fst • (1 : H →L[ℂ] H) + pi z.snd := by
  induction z using Unitization.ind with
  | inl_add_inr c a => simp [unitization, Algebra.algebraMap_eq_smul_one]

/-- The rank-one operator associated with a character eigenvector commutes
with the represented commutative algebra. -/
private theorem mul_rankOne_eq_rankOne_mul_of_character_eigenvector
    (pi : NonUnitalCStarRepresentation A H)
    (D : StarSubalgebra ℂ (Unitization ℂ A))
    [IsClosed (D : Set (Unitization ℂ A))]
    (chi : WeakDual.characterSpace ℂ D) (eta : H)
    (heigen : ∀ x : D, pi.unitization (x : Unitization ℂ A) eta = chi x • eta)
    (x : D) :
    pi.unitization (x : Unitization ℂ A) * InnerProductSpace.rankOne ℂ eta eta =
      InnerProductSpace.rankOne ℂ eta eta * pi.unitization (x : Unitization ℂ A) := by
  let rhoD : Representation D H := pi.unitization.comp D.subtype
  have hadj : ContinuousLinearMap.adjoint (rhoD x) eta = star (chi x) • eta := by
    have hadjmap : ContinuousLinearMap.adjoint (rhoD x) = rhoD (star x) := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    rw [hadjmap]
    exact heigen (star x) |>.trans (by rw [map_star])
  exact MathlibAnnex.Analysis.InnerProductSpace.commute_rankOne_self_of_apply_eq_smul_of_adjoint_apply_eq_star_smul
      (rhoD x) eta (chi x) (heigen x) hadj

/-- A rank-one projection onto a joint character eigenvector lies in the
chosen maximal abelian subalgebra after unitization. -/
theorem mem_maximalAbelian_of_map_eq_rankOne_of_eigenvector
    (pi : NonUnitalCStarRepresentation A H) (hinj : Function.Injective pi)
    (D : StarSubalgebra ℂ (Unitization ℂ A)) (hD : IsMaximalAbelian D)
    (chi : WeakDual.characterSpace ℂ D) (eta : H)
    (heigen : ∀ x : D, pi.unitization (x : Unitization ℂ A) eta = chi x • eta)
    (q : A) (hq : pi q = InnerProductSpace.rankOne ℂ eta eta) :
    (q : Unitization ℂ A) ∈ D := by
  letI : IsClosed (D : Set (Unitization ℂ A)) := hD.isClosed
  apply hD.mem_of_commute
  intro x
  have hoperator := mul_rankOne_eq_rankOne_mul_of_character_eigenvector pi D chi eta heigen x
  have hpiComm :
      pi (x : Unitization ℂ A).snd * InnerProductSpace.rankOne ℂ eta eta =
        InnerProductSpace.rankOne ℂ eta eta * pi (x : Unitization ℂ A).snd := by
    apply add_left_cancel (a :=
      (x : Unitization ℂ A).fst • InnerProductSpace.rankOne ℂ eta eta)
    simpa [unitization_apply_eq_fst_smul_add, add_mul, mul_add,
      smul_mul_assoc, mul_smul_comm] using hoperator
  have hqCommA : q * (x : Unitization ℂ A).snd = (x : Unitization ℂ A).snd * q := by
    apply hinj
    simpa [map_mul, hq] using hpiComm.symm
  apply Unitization.ext
  · simp
  · simpa [hqCommA]

/-- A character eigenvector of norm one makes its rank-one preimage evaluate
to one. -/
theorem character_apply_eq_one_of_map_eq_rankOne
    (pi : NonUnitalCStarRepresentation A H)
    (D : StarSubalgebra ℂ (Unitization ℂ A))
    (chi : WeakDual.characterSpace ℂ D) (eta : H) (heta : ‖eta‖ = 1)
    (heigen : ∀ x : D, pi.unitization (x : Unitization ℂ A) eta = chi x • eta)
    (r : D) (hr : pi.unitization (r : Unitization ℂ A) =
      InnerProductSpace.rankOne ℂ eta eta) :
    chi r = 1 := by
  have heta_ne : eta ≠ 0 := by
    intro hzero
    simp [hzero] at heta
  apply smul_left_injective ℂ heta_ne
  calc
    chi r • eta = pi.unitization (r : Unitization ℂ A) eta := (heigen r).symm
    _ = InnerProductSpace.rankOne ℂ eta eta eta := by rw [hr]
    _ = eta := by simp [InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, heta]
    _ = (1 : ℂ) • eta := (one_smul ℂ eta).symm

/-- Compactness of both scalar parts implies compactness of their sum. -/
private theorem isCompactOperator_map_of_realPart_of_imaginaryPart
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
private theorem exists_isSelfAdjoint_and_not_isCompactOperator_map
    (pi : NonUnitalCStarRepresentation A H) {a : A}
    (ha : ¬ IsCompactOperator (pi a)) :
    ∃ b : A, IsSelfAdjoint b ∧ ¬ IsCompactOperator (pi b) := by
  by_cases hre : IsCompactOperator (pi (ℜ a : A))
  · refine ⟨(ℑ a : A), (ℑ a).property, ?_⟩
    intro him
    exact ha (isCompactOperator_map_of_realPart_of_imaginaryPart pi a hre him)
  · exact ⟨(ℜ a : A), (ℜ a).property, hre⟩

/-- Separate a noncompact represented element with zero scalar part from
the compact-preimage ideal by a non-scalar character. -/
theorem exists_character_ne_infinity_annihilating_compact_preimage
    (pi : NonUnitalCStarRepresentation A H)
    (D : StarSubalgebra ℂ (Unitization ℂ A))
    [IsClosed (D : Set (Unitization ℂ A))] [IsMulCommutative D]
    (d : D) (hdfst : (d : Unitization ℂ A).fst = 0)
    (hd : ¬ IsCompactOperator (pi.unitization (d : Unitization ℂ A))) :
    ∃ chi : WeakDual.characterSpace ℂ D,
      chi ≠ infinityCharacterOn (A := A) D ∧
      ∀ r : D, IsCompactOperator (pi.unitization (r : Unitization ℂ A)) → chi r = 0 := by
  letI : CommCStarAlgebra D := {}
  let rhoD : Representation D H := pi.unitization.comp D.subtype
  let Jtwo : TwoSidedIdeal D :=
    MathlibAnnex.CStarAlgebra.compactPreimageIdeal rhoD.toNonUnitalStarAlgHom
  let J : Ideal D := Jtwo.asIdeal
  have hJclosed : IsClosed (J : Set D) := by
    change IsClosed (Jtwo : Set D)
    exact MathlibAnnex.CStarAlgebra.isClosed_compactPreimageIdeal rhoD.toNonUnitalStarAlgHom
  have hdnot : d ∉ J := by
    intro h
    exact hd ((MathlibAnnex.CStarAlgebra.mem_compactPreimageIdeal
      rhoD.toNonUnitalStarAlgHom d).1 h)
  obtain ⟨chi, hchiJ, hchid⟩ :=
    exists_character_annihilating_closedIdeal_of_not_mem J hJclosed hdnot
  refine ⟨chi, ?_, ?_⟩
  · intro hchi
    apply hchid
    rw [hchi]
    exact hdfst
  · intro r hr
    exact hchiJ r ((MathlibAnnex.CStarAlgebra.mem_compactPreimageIdeal
      rhoD.toNonUnitalStarAlgHom r).2 hr)

/-- Once rank-one preimages are available, a represented self-adjoint
element cannot be noncompact.  This step has no density hypothesis. -/
theorem isCompactOperator_map_of_isSelfAdjoint_of_singleton_of_rankOne_preimages
    [Nontrivial A] (pi : NonUnitalCStarRepresentation A H)
    (b : A) (hb : IsSelfAdjoint b)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (hpre : ∀ x y : H, ∃ a : A, pi a = InnerProductSpace.rankOne ℂ x y) :
    IsCompactOperator (pi b) := by
  by_contra hbcompact
  obtain ⟨D, hD, hbD⟩ :=
    exists_maximalAbelian_containing_isSelfAdjoint (b : Unitization ℂ A) (hb.inr ℂ)
  letI : IsClosed (D : Set (Unitization ℂ A)) := hD.isClosed
  letI : IsMulCommutative D := hD.1
  let d : D := ⟨(b : Unitization ℂ A), hbD⟩
  have hd : ¬ IsCompactOperator (pi.unitization (d : Unitization ℂ A)) := by
    simpa [d] using hbcompact
  obtain ⟨chi, hchiInf, hchiCompact⟩ :=
    exists_character_ne_infinity_annihilating_compact_preimage pi D d rfl hd
  obtain ⟨eta, heta, heigen⟩ :=
    exists_unit_eigenvector_of_character_ne_infinity pi hsingle D chi hchiInf
  obtain ⟨q, hq⟩ := hpre eta eta
  have hqD : (q : Unitization ℂ A) ∈ D :=
    mem_maximalAbelian_of_map_eq_rankOne_of_eigenvector
      pi (injective_of_singleton pi hsingle) D hD chi eta heigen q hq
  let r : D := ⟨(q : Unitization ℂ A), hqD⟩
  have hr : pi.unitization (r : Unitization ℂ A) = InnerProductSpace.rankOne ℂ eta eta := by
    simpa [r] using hq
  have hzero : chi r = 0 := hchiCompact r (hr.symm ▸ isCompactOperator_rankOne eta eta)
  have hone : chi r = 1 := character_apply_eq_one_of_map_eq_rankOne pi D chi eta heta heigen r hr
  exact one_ne_zero (hone ▸ hzero)

/-- A singleton irreducible model containing all rank-one operators contains
no noncompact represented operator.  No nonunital simplicity premise is added. -/
theorem isCompactOperator_map_of_singleton_of_rankOne_preimages [Nontrivial A]
    (pi : NonUnitalCStarRepresentation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (hpre : ∀ x y : H, ∃ a : A, pi a = InnerProductSpace.rankOne ℂ x y) :
    ∀ a : A, IsCompactOperator (pi a) := by
  intro a
  by_contra ha
  obtain ⟨b, hb, hbnot⟩ := exists_isSelfAdjoint_and_not_isCompactOperator_map pi ha
  exact hbnot (isCompactOperator_map_of_isSelfAdjoint_of_singleton_of_rankOne_preimages
    pi b hb hsingle hpre)

end NonUnitalCStarRepresentation
end MathlibAnnex.Analysis.CStarAlgebra
