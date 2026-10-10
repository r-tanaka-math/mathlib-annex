/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.RepresentationTransport
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.ExtremeDecomposition
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.MatrixCoefficientSeparation
import MathlibAnnex.Analysis.Normed.GeometricStructure.WeakStarMaximalFace

/-!
# Extreme unit coefficients of irreducible representations

The implication from an irreducible unit coefficient to a dual-ball extreme
point is not the previously proved converse for cyclic extreme coefficients.
Here it follows from a common extreme support of the coefficient's nonempty
value-one slice. Realize that support by the already constructed cyclic
representation. Coefficient separation forces equality of the two functionals.
Thus no extremality of the starting coefficient is assumed.

The two representations may live in different universes. Actual isometric
conjugations on lifted spaces are used only to apply the finite-family
separation theorem; coefficients and nonzero irreducibility are preserved.
-/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} {K : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Two distinct irreducible unit coefficients, allowing distinct Hilbert
universes, admit a value-one separating contraction in the original algebra. -/
theorem exists_norm_le_one_matrixCoefficient_eq_one_ne_one_of_ne
    (pi : NonUnitalCStarRepresentation A H) (rho : NonUnitalCStarRepresentation A K)
    (hpi : pi.IsIrreducible) (hrho : rho.IsIrreducible)
    (x y : H) (z w : K) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (hne : matrixCoefficient pi x y ≠ matrixCoefficient rho z w) :
    ∃ a : A, ‖a‖ ≤ 1 ∧ matrixCoefficient pi x y a = 1 ∧
      matrixCoefficient rho z w a ≠ 1 := by
  let H' := ULift.{w} H
  let K' := ULift.{v} K
  letI : InnerProductSpace ℂ H' :=
    { inner := fun x y => inner ℂ x.down y.down
      norm_sq_eq_re_inner := fun x => norm_sq_eq_re_inner x.down
      conj_inner_symm := fun x y => inner_conj_symm x.down y.down
      add_left := fun x y z => inner_add_left x.down y.down z.down
      smul_left := fun x y c => inner_smul_left x.down y.down c }
  letI : InnerProductSpace ℂ K' :=
    { inner := fun x y => inner ℂ x.down y.down
      norm_sq_eq_re_inner := fun x => norm_sq_eq_re_inner x.down
      conj_inner_symm := fun x y => inner_conj_symm x.down y.down
      add_left := fun x y z => inner_add_left x.down y.down z.down
      smul_left := fun x y c => inner_smul_left x.down y.down c }
  let U : H ≃ₗᵢ[ℂ] H' := (LinearIsometryEquiv.ulift ℂ H).symm
  let V : K ≃ₗᵢ[ℂ] K' := (LinearIsometryEquiv.ulift ℂ K).symm
  let L : Bool → Type (max v w) := fun b => match b with
    | false => H'
    | true => K'
  letI (b : Bool) : NormedAddCommGroup (L b) := match b with
    | false => inferInstance
    | true => inferInstance
  letI (b : Bool) : InnerProductSpace ℂ (L b) := match b with
    | false => inferInstance
    | true => inferInstance
  letI (b : Bool) : CompleteSpace (L b) := match b with
    | false => inferInstance
    | true => inferInstance
  let sigma : ∀ b, NonUnitalCStarRepresentation A (L b) := fun b => match b with
    | false => conj pi U
    | true => conj rho V
  let p : ∀ b, L b := fun b => match b with
    | false => U x
    | true => V z
  let q : ∀ b, L b := fun b => match b with
    | false => U y
    | true => V w
  have hs : ∀ b, (sigma b).IsIrreducible := by
    intro b
    cases b
    · exact isIrreducible_conj pi U hpi
    · exact isIrreducible_conj rho V hrho
  have hp : ∀ b, ‖p b‖ = 1 := by
    intro b
    cases b
    · exact (U.norm_map x).trans hx
    · exact (V.norm_map z).trans hz
  have hq : ∀ b, ‖q b‖ = 1 := by
    intro b
    cases b
    · exact (U.norm_map y).trans hy
    · exact (V.norm_map w).trans hw
  have hc0 : matrixCoefficient (sigma false) (p false) (q false) =
      matrixCoefficient pi x y := matrixCoefficient_conj pi U x y
  have hc1 : matrixCoefficient (sigma true) (p true) (q true) =
      matrixCoefficient rho z w := matrixCoefficient_conj rho V z w
  obtain ⟨a, ha, hf, hg⟩ := exists_norm_le_one_matrixCoefficient_eq_one_ne_one
    sigma hs p q hp hq (by rwa [hc0, hc1])
  exact ⟨a, ha, by simpa only [hc0] using hf, by simpa only [hc1] using hg⟩

/-- Paper 5.4 for a genuine nonzero irreducible representation. Extremality
is proved, not included as a premise on either vector or the representation. -/
theorem matrixCoefficient_mem_extremePoints_dual_closedBall_of_isIrreducible
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    matrixCoefficient pi x y ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ := by
  letI : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  let f : StrongDual ℂ A := matrixCoefficient pi x y
  have hn : ‖f‖ = 1 := by
    simpa only [f, hx, hy, one_mul] using norm_matrixCoefficient_of_isIrreducible pi hpi x y
  obtain ⟨a, han, ha⟩ := exists_norm_eq_one_matrixCoefficient_eq_one_of_isIrreducible
    pi hpi x y hx hy
  have ha0 : a ≠ 0 := by
    intro hz
    simpa [hz] using ha
  letI : Nontrivial A := ⟨⟨a, 0, ha0⟩⟩
  let F : Set A := NormedSpace.unitBallSupportFace ℂ f
  have hF : F.Nonempty := ⟨a, mem_closedBall_zero_iff.mpr han.le, ha⟩
  obtain ⟨tau, htau_norm, htau_ext, htau⟩ :=
    NormedSpace.exists_extreme_dual_eq_one_of_convex_subset_sphere ℂ hF
      (NormedSpace.convex_unitBallSupportFace ℂ f)
      (NormedSpace.unitBallSupportFace_subset_sphere ℂ hn.le)
  have htau0 : tau ≠ 0 := norm_ne_zero_iff.mp (by rw [htau_norm]; exact one_ne_zero)
  let rho := NonUnitalFunctional.cyclicRepresentation tau htau0
  let z := NonUnitalFunctional.cyclicSourceVector tau htau0
  let w := NonUnitalFunctional.cyclicTargetVector tau htau0
  have hrho : rho.IsIrreducible :=
    NonUnitalFunctional.isIrreducible_cyclicRepresentation tau htau0 htau_ext
  have hz : ‖z‖ = 1 := NonUnitalFunctional.norm_cyclicSourceVector tau htau0
  have hw : ‖w‖ = 1 := NonUnitalFunctional.norm_cyclicTargetVector tau htau0
  have hrecover : matrixCoefficient rho z w = tau :=
    NonUnitalFunctional.matrixCoefficient_cyclicRepresentation_of_norm_eq_one
      tau htau0 htau_norm
  have heq : f = tau := by
    by_contra hne
    obtain ⟨b, hbn, hfb, htb⟩ := exists_norm_le_one_matrixCoefficient_eq_one_ne_one_of_ne
      pi rho hpi hrho x y z w hx hy hz hw (by simpa only [hrecover] using hne)
    apply htb
    rw [hrecover]
    exact htau b ⟨mem_closedBall_zero_iff.mpr hbn, hfb⟩
  simpa only [← heq, f] using htau_ext

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
