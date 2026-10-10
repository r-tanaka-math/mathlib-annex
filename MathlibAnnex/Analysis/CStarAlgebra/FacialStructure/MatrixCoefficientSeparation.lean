/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.MatrixCoefficient.Separation
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.SimultaneousClipping
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.CoefficientTranslate

/-!
# Separation of distinct irreducible unit matrix coefficients

Positive exact interpolation is applied in the original algebra. For one
representation it realizes the action of the projection onto the source
line on both requested source vectors. A unitary of the unitization then
moves the target line. The resulting two coefficient values agree with
the appropriate rank-one test, but the rank-one operator itself is never
asserted to lie in the represented algebra.

For inequivalent coordinates, positive simultaneous interpolation fixes one
source vector and kills the other. For equivalent coordinates, the actual
unitary intertwiner transfers the first coefficient to the second space.
The rank-one equality criterion includes dependent source vectors and phases.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Multiplication by an element of the unitization intertwines the original
representation with its canonical extension. The result remains in A. -/
theorem map_unitizationLeftMul (pi : NonUnitalCStarRepresentation A H)
    (z : Unitization ℂ A) (a : A) :
    pi (unitizationLeftMul z a) = pi.unitization z * pi a := by
  calc
    _ = pi.unitization (unitizationLeftMul z a : Unitization ℂ A) :=
      (unitization_inr pi _).symm
    _ = _ := by rw [inr_unitizationLeftMul, map_mul, unitization_inr]

variable [PartialOrder A] [StarOrderedRing A]

/-- The singleton specialization of the proved simultaneous positive exact
interpolation theorem, retaining arbitrary Hilbert-space dimension. -/
theorem exists_nonneg_norm_le_eq_on_of_isIrreducible
    (pi : NonUnitalCStarRepresentation A H) (hirr : pi.IsIrreducible)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (T : H →L[ℂ] H) (hT : 0 ≤ T) (C : ℝ) (hC : 0 ≤ C) (hTC : ‖T‖ ≤ C) :
    ∃ a : A, 0 ≤ a ∧ ‖a‖ ≤ C ∧ ∀ x : H, x ∈ E → pi a x = T x := by
  obtain ⟨a, ha, hn, heq⟩ := exists_nonneg_norm_le_forall_eq_on
    (I := Unit) (H := fun _ => H) (fun _ => pi) (fun _ => hirr)
    (fun i j hij => (hij (Subsingleton.elim i j)).elim)
    (fun _ => E) (fun _ => T) (fun _ => hT) C hC (fun _ => hTC)
  exact ⟨a, ha, hn, heq ()⟩

/-- Distinct unit coefficients in a single irreducible representation have
nonincluded value-one slices. No independence of either pair is assumed. -/
theorem exists_norm_le_one_matrixCoefficient_eq_one_ne_one_of_isIrreducible
    (pi : NonUnitalCStarRepresentation A H) (hirr : pi.IsIrreducible)
    (x v y w : H) (hx : ‖x‖ = 1) (hv : ‖v‖ = 1)
    (hy : ‖y‖ = 1) (hw : ‖w‖ = 1)
    (hne : matrixCoefficient pi x y ≠ matrixCoefficient pi v w) :
    ∃ a : A, ‖a‖ ≤ 1 ∧ matrixCoefficient pi x y a = 1 ∧
      matrixCoefficient pi v w a ≠ 1 := by
  let E : Submodule ℂ H := Submodule.span ℂ {x, v}
  letI : FiniteDimensional ℂ E :=
    FiniteDimensional.span_of_finite ℂ (Set.toFinite {x, v})
  let P : Submodule ℂ H := Submodule.span ℂ {x}
  letI : FiniteDimensional ℂ P :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_singleton x)
  have hP : IsStarProjection P.starProjection := isStarProjection_starProjection
  obtain ⟨b, _, hbn, hb⟩ := exists_nonneg_norm_le_eq_on_of_isIrreducible
    pi hirr E P.starProjection hP.nonneg 1 zero_le_one P.starProjection_norm_le
  have hxE : x ∈ E := Submodule.subset_span (by simp)
  have hvE : v ∈ E := Submodule.subset_span (by simp)
  have hbx : pi b x = x := by
    rw [hb x hxE]
    exact P.starProjection_eq_self_iff.mpr (Submodule.subset_span (by simp))
  have hbv : pi b v = inner ℂ x v • x := by
    rw [hb v hvE]
    exact Submodule.starProjection_unit_singleton ℂ hx v
  obtain ⟨u, hu⟩ := Representation.exists_unitary_apply_eq_of_isIrreducible
    pi.unitization (isIrreducible_unitization pi hirr) x y hx hy
  let a : A := unitizationLeftMul (u : Unitization ℂ A) b
  have han : ‖a‖ ≤ 1 := (norm_unitizationLeftMul_unitary u b).trans_le hbn
  have hax : pi a x = y := by
    rw [show pi a = pi.unitization (u : Unitization ℂ A) * pi b from
      map_unitizationLeftMul pi _ b]
    change pi.unitization (u : Unitization ℂ A) (pi b x) = y
    rw [hbx, hu]
  have hav : pi a v = inner ℂ x v • y := by
    rw [show pi a = pi.unitization (u : Unitization ℂ A) * pi b from
      map_unitizationLeftMul pi _ b]
    change pi.unitization (u : Unitization ℂ A) (pi b v) = _
    rw [hbv, map_smul, hu]
  refine ⟨a, han, ?_, ?_⟩
  · rw [matrixCoefficient_apply, hax]
    exact inner_self_eq_one_of_norm_eq_one hy
  · intro heq
    have htest : InnerProductSpace.matrixCoefficient ℂ v w
        (InnerProductSpace.rankOne ℂ y x) = 1 := by
      simpa only [matrixCoefficient_apply, hav, inner_smul_right,
        InnerProductSpace.matrixCoefficient_apply_rankOne] using heq
    have hcoeff := InnerProductSpace.matrixCoefficient_eq_of_apply_rankOne_eq_one
      x v y w hx hv hy hw htest
    apply hne
    apply ContinuousLinearMap.ext
    intro c
    exact congrArg (fun f : (H →L[ℂ] H) →L[ℂ] ℂ => f (pi c)) hcoeff

section TwoRepresentations
variable {K : Bool → Type v}
variable [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℂ (K i)]
variable [∀ i, CompleteSpace (K i)]

/-- Inequivalent irreducible coordinates admit a contractive original-algebra
witness with coefficient values exactly one and zero, respectively. -/
theorem exists_norm_le_one_matrixCoefficient_eq_one_eq_zero_of_not_unitaryEquivalent
    (pi : ∀ i, NonUnitalCStarRepresentation A (K i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ¬ (pi false).UnitaryEquivalent (pi true))
    (x y : ∀ i, K i) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1) :
    ∃ a : A, ‖a‖ ≤ 1 ∧ matrixCoefficient (pi false) (x false) (y false) a = 1 ∧
      matrixCoefficient (pi true) (x true) (y true) a = 0 := by
  have hpair : ∀ i j, i ≠ j → ¬ (pi i).UnitaryEquivalent (pi j) := by
    intro i j hij hequiv
    cases i <;> cases j
    · exact hij rfl
    · exact hne hequiv
    · apply hne
      obtain ⟨U, hU⟩ := hequiv
      refine ⟨U.symm, ?_⟩
      intro a z
      apply U.injective
      simpa only [U.apply_symm_apply] using (hU a (U.symm z)).symm
    · exact hij rfl
  let E : ∀ i, Submodule ℂ (K i) := fun i => Submodule.span ℂ {x i}
  letI (i : Bool) : FiniteDimensional ℂ (E i) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_singleton (x i))
  let T : ∀ i, K i →L[ℂ] K i := fun i => if i = false then 1 else 0
  have hT : ∀ i, 0 ≤ T i := by
    intro i
    cases i
    · simpa [T] using (star_mul_self_nonneg (1 : K false →L[ℂ] K false))
    · simp [T]
  have hTn : ∀ i, ‖T i‖ ≤ 1 := by
    intro i
    cases i
    · change ‖ContinuousLinearMap.id ℂ (K false)‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le
    · simp [T]
  obtain ⟨b, _, hbn, hb⟩ := exists_nonneg_norm_le_forall_eq_on
    pi hirr hpair E T hT 1 zero_le_one hTn
  have hbx : pi false b (x false) = x false := by
    simpa [T] using hb false (x false) (Submodule.subset_span (by simp))
  have hbv : pi true b (x true) = 0 := by
    simpa [T] using hb true (x true) (Submodule.subset_span (by simp))
  obtain ⟨u, hu⟩ := Representation.exists_unitary_apply_eq_of_isIrreducible
    (pi false).unitization (isIrreducible_unitization (pi false) (hirr false))
    (x false) (y false) (hx false) (hy false)
  let a : A := unitizationLeftMul (u : Unitization ℂ A) b
  refine ⟨a, (norm_unitizationLeftMul_unitary u b).trans_le hbn, ?_, ?_⟩
  · rw [matrixCoefficient_apply, show pi false a =
        (pi false).unitization (u : Unitization ℂ A) * pi false b from
      map_unitizationLeftMul (pi false) _ b]
    change inner ℂ (y false) ((pi false).unitization (u : Unitization ℂ A)
      (pi false b (x false))) = 1
    rw [hbx, hu]
    exact inner_self_eq_one_of_norm_eq_one (hy false)
  · rw [matrixCoefficient_apply, show pi true a =
        (pi true).unitization (u : Unitization ℂ A) * pi true b from
      map_unitizationLeftMul (pi true) _ b]
    change inner ℂ (y true) ((pi true).unitization (u : Unitization ℂ A)
      (pi true b (x true))) = 0
    simp only [hbv, map_zero, inner_zero_right]

/-- Distinct irreducible unit coefficients have nonincluded value-one slices,
regardless of whether the two actual representations are equivalent. -/
theorem exists_norm_le_one_matrixCoefficient_eq_one_ne_one
    (pi : ∀ i, NonUnitalCStarRepresentation A (K i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (x y : ∀ i, K i) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hne : matrixCoefficient (pi false) (x false) (y false) ≠
      matrixCoefficient (pi true) (x true) (y true)) :
    ∃ a : A, ‖a‖ ≤ 1 ∧ matrixCoefficient (pi false) (x false) (y false) a = 1 ∧
      matrixCoefficient (pi true) (x true) (y true) a ≠ 1 := by
  by_cases hequiv : (pi false).UnitaryEquivalent (pi true)
  · obtain ⟨U, hU⟩ := hequiv
    have hc := matrixCoefficient_eq_of_intertwines (pi false) (pi true) U hU
      (x false) (y false)
    have hne' : matrixCoefficient (pi true) (U (x false)) (U (y false)) ≠
        matrixCoefficient (pi true) (x true) (y true) := by rwa [hc]
    obtain ⟨a, han, ha, hta⟩ :=
      exists_norm_le_one_matrixCoefficient_eq_one_ne_one_of_isIrreducible
        (pi true) (hirr true) (U (x false)) (x true) (U (y false)) (y true)
        (by simpa using hx false) (hx true) (by simpa using hy false) (hy true) hne'
    exact ⟨a, han, by simpa only [hc] using ha, hta⟩
  · obtain ⟨a, han, ha, hta⟩ :=
      exists_norm_le_one_matrixCoefficient_eq_one_eq_zero_of_not_unitaryEquivalent
        pi hirr hequiv x y hx hy
    exact ⟨a, han, ha, by rw [hta]; exact zero_ne_one⟩

end TwoRepresentations
end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
