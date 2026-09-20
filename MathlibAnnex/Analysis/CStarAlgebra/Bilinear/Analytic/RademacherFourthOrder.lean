import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Analytic.RademacherMoments
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Analytic.QuarticImaginary

/-!
# A noncommutative fourth-moment order bound

For P = sum a_i^2 and selfadjoint a_i, the exact finite Rademacher expansion
is at most 3 ||P|| P in the C*-order.  The crossing pairing is controlled by
an explicit sum of commutator star-squares; products are never commuted.
SOURCE_UNBUILT.
-/

set_option autoImplicit false
noncomputable section
open Finset
open scoped ComplexOrder
namespace MathlibAnnex.CStarBilinear.Analytic
open MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {A : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem squareBudget_nonneg (a : ι → A) (ha : ∀ i, IsSelfAdjoint (a i)) :
    0 ≤ squareBudget a := by
  exact Finset.sum_nonneg fun i _ ↦ (ha i).sq_nonneg

theorem isSelfAdjoint_rademacherSum (a : ι → A) (ha : ∀ i, IsSelfAdjoint (a i))
    (ε : ι → Bool) : IsSelfAdjoint (rademacherSum a ε) := by
  change star (∑ i, rSign ε i • a i) = ∑ i, rSign ε i • a i
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [star_smul, (ha i).star_eq]

/-- CFC is applied to a single positive element, not to a commutative ambient algebra. -/
theorem positive_sq_le_norm_smul [Nontrivial A] (P : A) (hP : 0 ≤ P) :
    P ^ 2 ≤ ‖P‖ • P := by
  have hsa := hP.isSelfAdjoint
  have hspec : ∀ r ∈ spectrum ℝ P, r ≤ ‖P‖ :=
    (le_algebraMap_iff_spectrum_le (R := ℝ) (r := ‖P‖) hsa).mp
      hsa.le_algebraMap_norm_self
  have h : cfc (fun r : ℝ ↦ r ^ 2) P ≤ cfc (fun r : ℝ ↦ ‖P‖ * r) P := by
    apply cfc_mono
    · intro r hr
      have hr0 := spectrum_nonneg_of_nonneg hP hr
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hspec r hr) hr0
    · exact (continuous_id.pow 2).continuousOn
    · exact (continuous_const.mul continuous_id).continuousOn
  rw [cfc_pow_id P 2 hsa,
    cfc_const_mul ‖P‖ (fun r : ℝ ↦ r) P continuous_id.continuousOn,
    cfc_id' ℝ P hsa] at h
  exact h

/-- The commutator identity is an equality of ordered noncommutative words. -/
theorem commutator_star_square (a b : A) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    star (a * b - b * a) * (a * b - b * a) =
      a * b ^ 2 * a + b * a ^ 2 * b - a * b * a * b - b * a * b * a := by
  rw [star_sub, star_mul, star_mul, ha.star_eq, hb.star_eq]
  noncomm_ring

/-- A summed crossing pairing is bounded by the noncrossing sandwich pairing. -/
theorem crossing_pairing_le (a : ι → A) (ha : ∀ i, IsSelfAdjoint (a i)) :
    (∑ i, ∑ j, a i * a j * a i * a j) ≤ ∑ i, a i * squareBudget a * a i := by
  let S : A := ∑ i, ∑ j, a i * a j ^ 2 * a i
  let T : A := ∑ i, ∑ j, a i * a j * a i * a j
  have hSswap : (∑ i, ∑ j, a j * a i ^ 2 * a j) = S := by
    dsimp [S]
    rw [Finset.sum_comm]
  have hTswap : (∑ i, ∑ j, a j * a i * a j * a i) = T := by
    dsimp [T]
    rw [Finset.sum_comm]
  have hex : (∑ i, ∑ j, star (a i * a j - a j * a i) * (a i * a j - a j * a i)) =
      S + S - T - T := by
    simp_rw [commutator_star_square _ _ (ha _) (ha _)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hSswap, hTswap]
  have hdef : S - T = (1 / 2 : ℝ) •
      ∑ i, ∑ j, star (a i * a j - a j * a i) * (a i * a j - a j * a i) := by
    rw [hex]
    module
  have hnonneg : 0 ≤ S - T := by
    rw [hdef]
    apply smul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ star_mul_self_nonneg _
  have h : T ≤ S := sub_nonneg.mp hnonneg
  have he : S = ∑ i, a i * squareBudget a * a i := by
    simp only [S, squareBudget, Finset.mul_sum, Finset.sum_mul]
  simpa only [T, he] using h

/-- Every sandwich is estimated by order-preserving star conjugation. -/
theorem sandwich_pairing_le (a : ι → A) (ha : ∀ i, IsSelfAdjoint (a i)) :
    (∑ i, a i * squareBudget a * a i) ≤ ‖squareBudget a‖ • squareBudget a := by
  have hP := squareBudget_nonneg a ha
  have hbound := hP.isSelfAdjoint.le_algebraMap_norm_self
  calc
    _ ≤ ∑ i, ‖squareBudget a‖ • (a i ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have h := star_left_conjugate_le_conjugate hbound (a i)
      simpa [Algebra.algebraMap_eq_smul_one, (ha i).star_eq, mul_smul_comm,
        smul_mul_assoc, pow_two] using h
    _ = _ := by rw [← Finset.smul_sum]; rfl

/-- Dimension-free operator-order estimate.  The finite family may be empty. -/
theorem finiteMean_rademacher_fourth_le [Nontrivial A]
    (a : ι → A) (ha : ∀ i, IsSelfAdjoint (a i)) :
    finiteMean (fun ε : ι → Bool ↦ rademacherSum a ε ^ 4) ≤
      (3 * ‖squareBudget a‖) • squareBudget a := by
  let P := squareBudget a
  let S := ∑ i, a i * squareBudget a * a i
  let T := ∑ i, ∑ j, a i * a j * a i * a j
  let D := ∑ i, a i ^ 4
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ ↦ selfAdjoint_fourth_nonneg _ (ha i)
  have hT : T ≤ S := crossing_pairing_le a ha
  have hS : S ≤ ‖P‖ • P := sandwich_pairing_le a ha
  have hP : P ^ 2 ≤ ‖P‖ • P := positive_sq_le_norm_smul P (squareBudget_nonneg a ha)
  calc
    finiteMean (fun ε : ι → Bool ↦ rademacherSum a ε ^ 4) =
        P ^ 2 + S + T - (2 : ℝ) • D := finiteMean_rademacher_fourth a
    _ ≤ P ^ 2 + S + T := sub_le_self _ (smul_nonneg (by norm_num) hD)
    _ ≤ P ^ 2 + S + S := by gcongr
    _ ≤ ‖P‖ • P + ‖P‖ • P + ‖P‖ • P := add_le_add (add_le_add hP hS) hS
    _ = (3 * ‖squareBudget a‖) • squareBudget a := by dsimp [P]; module

/-- A state's real value on a selfadjoint element is bounded above by its norm. -/
theorem state_re_le_norm [Nontrivial A] (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (P : A) (hP : IsSelfAdjoint P) : (phi P).re ≤ ‖P‖ := by
  have h := state_re_mono phi hphi hP.le_algebraMap_norm_self
  have he : algebraMap ℝ A ‖P‖ = ‖P‖ • (1 : A) := by
    simp [Algebra.algebraMap_eq_smul_one]
  rw [he, state_re_real_smul, hphi.2] at h
  simpa using h

/-- Actual normalized fourth moments under any state. -/
theorem finiteMean_fourthMoment_le [Nontrivial A]
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (a : ι → A) (ha : ∀ i, IsSelfAdjoint (a i)) :
    finiteMean (fun ε : ι → Bool ↦ fourthMoment phi (rademacherSum a ε)) ≤
      3 * ‖squareBudget a‖ ^ 2 := by
  have he : finiteMean (fun ε : ι → Bool ↦ fourthMoment phi (rademacherSum a ε)) =
      (phi (finiteMean (fun ε : ι → Bool ↦ rademacherSum a ε ^ 4))).re := by
    calc
      _ = (finiteMean (fun ε : ι → Bool ↦ phi (rademacherSum a ε ^ 4))).re :=
        finiteMean_re _
      _ = _ := congrArg Complex.re (finiteMean_map (phi.restrictScalars ℝ).toLinearMap _)
  rw [he]
  have h := state_re_mono phi hphi (finiteMean_rademacher_fourth_le a ha)
  rw [state_re_real_smul] at h
  calc
    _ ≤ (3 * ‖squareBudget a‖) * (phi (squareBudget a)).re := h
    _ ≤ (3 * ‖squareBudget a‖) * ‖squareBudget a‖ :=
      mul_le_mul_of_nonneg_left
        (state_re_le_norm phi hphi _ (squareBudget_nonneg a ha).isSelfAdjoint) (by positivity)
    _ = _ := by ring

end MathlibAnnex.CStarBilinear.Analytic
