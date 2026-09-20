import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteCentral.EscapingIsometry
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteCentral.ProbabilityOrbit
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteAveragePoint

/-!
# Finite central averages without an averaging-existence premise

C06 controller source, UNBUILT. The same compression, escaping isometry,
finite group and probability weights serve every member of a finite test
set. All gauge controls come from the received universal bilinear estimate.
The finite-index branch uses P=1 and w=1; the infinite branch uses the actual
basis-shift operator, and never assumes that a proper isometry is unitary.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexOrder CStarAlgebra
namespace MathlibAnnex.FiniteCentral
open MathlibAnnex.CStarAlgebra.TensorAveraging MathlibAnnex.CStarBilinear
open MathlibAnnex.RepresentedCentralCorner MathlibAnnex.RepresentedBidual
universe u v w t
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] {ι : Type w}
variable (b : HilbertBasis ι ℂ H)
variable (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)

/-- On a finite basis, one group already balances EVERY operator exactly. -/
theorem finite_basis_exact_average [Fintype ι] (b : HilbertBasis ι ℂ H) :
    ∃ d : FiniteIsometryAverage (H →L[ℂ] H),
      ∀ T : H →L[ℂ] H, ∀ B : ContinuousBilinearForm (H →L[ℂ] H), d.defect T B = 0 := by
  classical
  let s : Finset ι := Finset.univ
  let U := signedOperator b s
  let d := uniformOrbit U (signedOperator_star_mul b s) (1 : H →L[ℂ] H) (by simp)
  refine ⟨d, fun T B => ?_⟩
  apply uniformOrbit_defect_eq_zero U (signedOperator_star_mul b s)
    (signedOperator_mul_star b s) (signedOperator_mul b s) 1 (by simp) B T
  have h := compression_mem_group_span b s T
  simpa only [s, compression, coordinateProjection_univ, one_mul, mul_one] using h

/-- Infinite case with actual positive normal controls, one uniform budget,
and one shared finite average. The controls are discharged at the endpoint. -/
theorem infinite_basis_average [Infinite ι]
    {J : Type t} [Fintype J]
    (b : HilbertBasis ι ℂ H)
    (T : J → H →L[ℂ] H) (B : J → ContinuousBilinearForm (H →L[ℂ] H))
    (phi psi : J → StateIndex A) (C : J → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hdom : ∀ j, IsStrongStarDominated (B j)
      (cornerFunctional pi hpi (phi j).val) (cornerFunctional pi hpi (psi j).val) (C j))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ d : FiniteIsometryAverage (H →L[ℂ] H), ∀ j, ‖d.defect (T j) (B j)‖ < epsilon := by
  classical
  let Csum : ℝ := ∑ j, C j
  have hCs : 0 ≤ Csum := Finset.sum_nonneg (fun j _ => hC j)
  have hCj (j : J) : C j ≤ Csum :=
    Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ j)
  let delta : ℝ := epsilon / (16 * (1 + Csum))
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hden : (16 * (1 + Csum) : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hdelta_eq : 16 * (1 + Csum) * delta = epsilon := by
    dsimp [delta]
    field_simp [hden]
  have hbudget (j : J) : 8 * C j * delta < epsilon := by
    have hm := mul_le_mul_of_nonneg_right (hCj j) (le_of_lt hdelta)
    nlinarith
  obtain ⟨s, hs⟩ := exists_common_compression b pi hpi T
    (fun j => (phi j).val) (fun j => (psi j).val) hdelta
  let R : ℝ := 1 + ∑ j, 2 * ‖T j‖
  have hR : 0 < R := by
    have := Finset.sum_nonneg (s := Finset.univ) (fun j _ =>
      mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (norm_nonneg (T j)))
    dsimp [R]; linarith
  have hRj (j : J) : ‖T j - compression b s (T j)‖ ≤ R := by
    have hj : 2 * ‖T j‖ ≤ ∑ k, 2 * ‖T k‖ :=
      Finset.single_le_sum (s := Finset.univ) (f := fun k => (2 : ℝ) * ‖T k‖)
        (fun k _ => by positivity) (Finset.mem_univ j)
    dsimp [R]
    linarith [norm_compression_error_le b s (T j)]
  let eta : ℝ := delta ^ 2 / (R ^ 2 + 1)
  have heta : 0 < eta := by dsimp [eta]; positivity
  have heta_den : R ^ 2 + 1 ≠ 0 := ne_of_gt (by positivity)
  have heta_eq : (R ^ 2 + 1) * eta = delta ^ 2 := by
    dsimp [eta]
    field_simp [heta_den]
  obtain ⟨w, hw, hmass⟩ := exists_common_escaping_isometry pi hpi b phi psi heta
  let U := signedOperator b s
  let d := uniformOrbit U (signedOperator_star_mul b s) w hw
  refine ⟨d, fun j => lt_of_le_of_lt ?_ (hbudget j)⟩
  apply d.norm_defect_le_of_balanced_approximation (T j) (compression b s (T j)) (B j)
  · exact uniformOrbit_defect_eq_zero U (signedOperator_star_mul b s)
      (signedOperator_mul_star b s) (signedOperator_mul b s) w hw (B j) _
      (compression_mem_group_span b s (T j))
  · intro i
    have hrange : (d.point i).val * star (d.point i).val = w * star w :=
      uniformOrbit_range U (signedOperator_star_mul b s)
        (signedOperator_mul_star b s) w hw i
    have hradius : ‖T j - compression b s (T j)‖ ^ 2 ≤ R ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (le_of_lt hR)).mpr (hRj j)
    have small (p : (H →L[ℂ] H) →L[ℂ] ℂ) (hp : ‖p (w * star w)‖ < eta) :
        ‖T j - compression b s (T j)‖ ^ 2 * ‖p ((d.point i).val * star (d.point i).val)‖
          ≤ delta ^ 2 := by
      rw [hrange]
      calc
        _ ≤ R ^ 2 * eta := mul_le_mul hradius (le_of_lt hp)
          (norm_nonneg _) (sq_nonneg _)
        _ ≤ delta ^ 2 := by nlinarith [le_of_lt heta]
    exact central_error_of_escape (B j)
      (cornerFunctional pi hpi (phi j).val) (cornerFunctional pi hpi (psi j).val)
      (C j) delta (hC j) (le_of_lt hdelta) (hdom j)
      (norm_cornerFunctional_le_one pi hpi (phi j).val (phi j).property)
      (norm_cornerFunctional_le_one pi hpi (psi j).val (psi j).property)
      (cornerFunctional_positive pi hpi (phi j).val (phi j).property)
      (cornerFunctional_positive pi hpi (psi j).val (psi j).property)
      (d.point i) (T j - compression b s (T j))
      (hs j).1 (hs j).2
      (small _ (hmass j).1) (small _ (hmass j).2)

end MathlibAnnex.FiniteCentral

namespace MathlibAnnex.RepresentedCentralCorner
open MathlibAnnex.FiniteCentral MathlibAnnex.RepresentedBidual
open MathlibAnnex.CStarAlgebra.TensorAveraging MathlibAnnex.CStarBilinear
universe u v
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

/-- Actual finite central averages: no mean/Ω/feasibility input remains.
This is a written proof candidate, NOT a kernel-qualified theorem. -/
theorem hasFiniteCentralAverages
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi) :
    HasFiniteCentralAverages pi hpi := by
  classical
  obtain ⟨I, b, hb⟩ := exists_hilbertBasis ℂ H
  intro tests epsilon hepsilon
  cases fintypeOrInfinite I with
  | inl hfin =>
    letI : Fintype I := hfin
    obtain ⟨d, hd⟩ := finite_basis_exact_average b
    exact ⟨d, fun af haf => by rw [hd, norm_zero]; exact hepsilon⟩
  | inr hinf =>
    letI : Infinite I := hinf
    let J := ↥tests
    let T : J → H →L[ℂ] H := fun j => pi j.val.1
    let B : J → ContinuousBilinearForm (H →L[ℂ] H) := fun j => tensorAssignment pi hpi j.val.2
    let C : J → ℝ := fun j => 292 * ‖j.val.2‖
    have hc : ∀ j : J, ∃ phi psi : StateIndex A,
        IsStrongStarDominated (B j) (cornerFunctional pi hpi phi.val)
          (cornerFunctional pi hpi psi.val) (C j) := by
      intro j
      exact exists_tensor_state_controls pi hpi j.val.2
    choose phi psi hdom using hc
    obtain ⟨d, hd⟩ := infinite_basis_average pi hpi b T B phi psi C
      (fun j => by dsimp [C]; positivity) hdom hepsilon
    exact ⟨d, fun af haf => hd ⟨af,haf⟩⟩

end MathlibAnnex.RepresentedCentralCorner
