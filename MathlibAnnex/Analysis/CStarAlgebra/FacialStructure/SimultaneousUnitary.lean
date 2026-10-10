/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.SimultaneousClipping
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.UnitaryTranslate
import MathlibAnnex.Analysis.CStarAlgebra.SmallUnitary

/-!
# Simultaneous unit-vector transport in the original algebra

The logarithms below are taken only for finite-dimensional unitaries at distance
strictly less than two from the identity. Two such transports suffice, including
antipodal vectors. The shared self-adjoint interpolants belong to the original
algebra; their exponentials belong to its formal unitization. Only after a
separate positive simultaneous interpolation do we multiply by an original-
algebra contraction. Thus neither an image-norm bound nor a unitization element
is passed off as an original-algebra contractive witness.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open NormedSpace
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

/-- Split any unit-vector transport into two steps of distance less than two. -/
theorem exists_norm_eq_one_norm_sub_lt_two
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∃ z : H, ‖z‖ = 1 ∧ ‖x - z‖ < 2 ∧ ‖z - y‖ < 2 := by
  by_cases hxy : ‖x - y‖ < 2
  · exact ⟨x, hx, by simp, hxy⟩
  have hlarge : 2 ≤ ‖x - y‖ := le_of_not_gt hxy
  have hplus := norm_add_sq (𝕜 := ℂ) x y
  have hminus := norm_sub_sq (𝕜 := ℂ) x y
  rw [hx, hy] at hplus hminus
  have hlarge_sq : (2 : ℝ) ^ 2 ≤ ‖x - y‖ ^ 2 :=
    (sq_le_sq₀ (by norm_num) (norm_nonneg _)).2 hlarge
  have hsum : ‖x + y‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖x + y‖]
  have hyx : y = -x := by
    have hz : x + y = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hsum)
    calc
      y = (x + y) - x := by abel
      _ = -x := by rw [hz, zero_sub]
  have hz : ‖Complex.I • x‖ = 1 := by simp [norm_smul, hx]
  have hleft : RCLike.re (inner ℂ x (Complex.I • x)) = 0 := by
    simp [inner_smul_right, inner_self_eq_norm_sq_to_K, hx]
  have hright : RCLike.re (inner ℂ (Complex.I • x) y) = 0 := by
    simp [hyx, inner_smul_left, inner_neg_right, inner_self_eq_norm_sq_to_K, hx]
  refine ⟨Complex.I • x, hz, ?_, ?_⟩
  · have h := norm_sub_sq (𝕜 := ℂ) x (Complex.I • x)
    rw [hx, hz, hleft] at h
    nlinarith
  · have h := norm_sub_sq (𝕜 := ℂ) (Complex.I • x) y
    rw [hz, hy, hright] at h
    nlinarith

/-- A close pair has a finite reducing logarithm. This is a Hilbert-space
construction, not a claim that the logarithm lies in a represented image. -/
theorem exists_selfAdjoint_exp_apply_eq_of_norm_sub_lt_two
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ‖x - y‖ < 2) :
    ∃ T : H →L[ℂ] H, IsSelfAdjoint T ∧
      Set.MapsTo T (Submodule.span ℂ {x, y}) (Submodule.span ℂ {x, y}) ∧
      exp (Complex.I • T) x = y := by
  let E : Submodule ℂ H := Submodule.span ℂ {x, y}
  letI : FiniteDimensional ℂ E :=
    FiniteDimensional.span_of_finite ℂ (Set.toFinite {x, y})
  have hxE : x ∈ E := Submodule.subset_span (Set.mem_insert x {y})
  have hyE : y ∈ E :=
    Submodule.subset_span (Set.mem_insert_of_mem x (Set.mem_singleton y))
  let xE : E := ⟨x, hxE⟩
  let yE : E := ⟨y, hyE⟩
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by rw [hx]; exact one_ne_zero)
  letI : Nontrivial H := ⟨⟨x, 0, hx0⟩⟩
  letI : Nontrivial E := ⟨⟨xE, 0, fun h => hx0 (congrArg Subtype.val h)⟩⟩
  letI : E.HasOrthogonalProjection := inferInstance
  letI : NormedRing (E →L[ℂ] E) := ContinuousLinearMap.toNormedRing
  obtain ⟨v, hv, hvnorm⟩ :=
    MathlibAnnex.Analysis.InnerProductSpace.exists_unitary_apply_eq_and_norm_sub_one_eq
      xE yE (by simpa [xE] using hx) (by simpa [yE] using hy)
  have hv2 : ‖(v : E →L[ℂ] E) - 1‖ < 2 := by
    rw [hvnorm]
    exact hxy
  let t : selfAdjoint (E →L[ℂ] E) := Unitary.argSelfAdjoint v
  let T : H →L[ℂ] H := zeroExtension E (t : E →L[ℂ] E)
  refine ⟨T, isSelfAdjoint_zeroExtension E _ t.property, mapsTo_zeroExtension E _, ?_⟩
  have hsmul : Complex.I • T = zeroExtension E (Complex.I • (t : E →L[ℂ] E)) := by
    ext z
    simp [T, zeroExtension, ContinuousLinearMap.comp_apply]
  rw [hsmul]
  change exp (zeroExtension E (Complex.I • (t : E →L[ℂ] E))) (xE : H) = y
  rw [exp_zeroExtension_apply]
  have hlog : selfAdjoint.expUnitary t = v := expUnitary_argSelfAdjoint hv2
  have happ := congrArg (fun q : unitary (E →L[ℂ] E) => (q : E →L[ℂ] E) xE) hlog
  rw [selfAdjoint.expUnitary_coe] at happ
  exact congrArg Subtype.val (happ.trans hv)

namespace NonUnitalCStarRepresentation

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {I : Type v} [Fintype I] {H : I → Type w}
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

/-- Simultaneous close transport uses the received finite-family self-adjoint
interpolation, never irreducibility of a direct sum. -/
theorem exists_unitary_forall_apply_eq_of_norm_sub_lt_two
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i j, i ≠ j → ¬ (pi i).UnitaryEquivalent (pi j))
    (x y : ∀ i, H i) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hxy : ∀ i, ‖x i - y i‖ < 2) :
    ∃ u : unitary (Unitization ℂ A), ∀ i,
      (pi i).unitization (u : Unitization ℂ A) (x i) = y i := by
  classical
  choose T hT hTE hTx using
    fun i => exists_selfAdjoint_exp_apply_eq_of_norm_sub_lt_two (x i) (y i) (hx i) (hy i) (hxy i)
  let E : ∀ i, Submodule ℂ (H i) := fun i => Submodule.span ℂ {x i, y i}
  letI (i : I) : FiniteDimensional ℂ (E i) :=
    FiniteDimensional.span_of_finite ℂ (Set.toFinite {x i, y i})
  let C : ℝ := ∑ i, ‖T i‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => norm_nonneg (T i))
  have hTC (i : I) : ‖T i‖ ≤ C :=
    Finset.single_le_sum (fun j _ => norm_nonneg (T j)) (Finset.mem_univ i)
  obtain ⟨a, ha, -, haeq⟩ := exists_selfAdjoint_norm_le_forall_eq_on pi hirr hne E T hT C hC hTC
  let s : selfAdjoint (Unitization ℂ A) :=
    ⟨(a : Unitization ℂ A), ha.map (Unitization.inrNonUnitalStarAlgHom ℂ A)⟩
  refine ⟨selfAdjoint.expUnitary s, fun i => ?_⟩
  calc
    (pi i).unitization (selfAdjoint.expUnitary s : Unitization ℂ A) (x i) =
        exp (Complex.I • T i) (x i) :=
      MathlibAnnex.Analysis.CStarAlgebra.StarAlgHom.expUnitary_apply_eq_of_eqOn_of_mapsTo
        (pi i).unitization s (T i) (E i)
        (fun z hz => by simpa only [s, unitization_inr] using haeq i z hz)
        (hTE i) (Submodule.subset_span (Set.mem_insert (x i) {y i}))
    _ = y i := hTx i

/-- One unitary in the formal unitization transports all unit pairs exactly.
Two logarithm steps account for arbitrary distances and the antipodal case. -/
theorem exists_unitary_forall_apply_eq
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i j, i ≠ j → ¬ (pi i).UnitaryEquivalent (pi j))
    (x y : ∀ i, H i) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1) :
    ∃ u : unitary (Unitization ℂ A), ∀ i,
      (pi i).unitization (u : Unitization ℂ A) (x i) = y i := by
  classical
  choose z hz hxz hzy using fun i => exists_norm_eq_one_norm_sub_lt_two (x i) (y i) (hx i) (hy i)
  obtain ⟨u, hu⟩ := exists_unitary_forall_apply_eq_of_norm_sub_lt_two pi hirr hne x z hx hz hxz
  obtain ⟨v, hv⟩ := exists_unitary_forall_apply_eq_of_norm_sub_lt_two pi hirr hne z y hz hy hzy
  refine ⟨v * u, fun i => ?_⟩
  change (pi i).unitization ((v : Unitization ℂ A) * (u : Unitization ℂ A)) (x i) = y i
  rw [map_mul]
  change (pi i).unitization (v : Unitization ℂ A)
    ((pi i).unitization (u : Unitization ℂ A) (x i)) = y i
  rw [hu i, hv i]

/-- The common contractive witness is in the original A. A separate positive
interpolant fixes every source; multiplying it by the common unitary both
preserves the prescribed action and returns to the original algebra. -/
theorem exists_norm_le_one_forall_apply_eq
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i j, i ≠ j → ¬ (pi i).UnitaryEquivalent (pi j))
    (x y : ∀ i, H i) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1) :
    ∃ a : A, ‖a‖ ≤ 1 ∧ ∀ i, pi i a (x i) = y i := by
  letI (i : I) : Nontrivial (H i) := (pi i).nontrivial_of_isNonzero (hirr i).1
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let E : ∀ i, Submodule ℂ (H i) := fun i => Submodule.span ℂ {x i}
  letI (i : I) : FiniteDimensional ℂ (E i) :=
    FiniteDimensional.span_of_finite ℂ (Set.toFinite {x i})
  obtain ⟨e, -, he, hfix⟩ := exists_nonneg_norm_le_forall_eq_on
    pi hirr hne E (fun i => (1 : H i →L[ℂ] H i)) (fun i => zero_le_one)
    1 zero_le_one (fun i => by simp)
  obtain ⟨u, hu⟩ := exists_unitary_forall_apply_eq pi hirr hne x y hx hy
  refine ⟨unitizationLeftMul (u : Unitization ℂ A) e, ?_, fun i => ?_⟩
  · rw [norm_unitizationLeftMul_unitary]
    exact he
  · rw [← unitization_inr_apply, inr_unitizationLeftMul, map_mul]
    change (pi i).unitization (u : Unitization ℂ A)
      ((pi i).unitization (e : Unitization ℂ A) (x i)) = y i
    rw [unitization_inr_apply, hfix i (x i) (Submodule.subset_span (Set.mem_singleton (x i)))]
    exact hu i

end NonUnitalCStarRepresentation
end MathlibAnnex.Analysis.CStarAlgebra
