import BanachGeometry.NoC0.NoC0Closure
import BanachGeometry.AlmostIsometric.LipschitzDistance
import BanachGeometry.AlmostIsometric.OptimalLipschitz
import BanachGeometry.AlmostIsometric.Escape
import BanachGeometry.AlmostIsometric.HilbertFreeSpaceData

/-! One fixed pair built from the constructed quantitative Hilbert supplier.
The same spaces and inherited norms occur in every export before ε is chosen.
The final existence theorem requires no analytic theorem input.
Execution evidence is recorded in the external receipts. -/
noncomputable section
namespace BanachGeometry
namespace AlmostIsometricPair

def sequence : QuantitativeHilbertSequence := QuantitativeHilbertSequence.ofModels HilbertSums.exists_quantitativeHilbertData
def family : AlmostIsometricFamily := sequence.metricFamily
def xSpace : SeparableRealBanach := family.fixedXBanach
def ySpace : SeparableRealBanach := family.fixedYBanach

theorem complementedCopy_family : family.HasContractivelyComplementedCopy := sequence.hasContractivelyComplementedCopy_metricFamily
theorem splitting_family : family.HasCoordinateSplitting := sequence.hasCoordinateSplitting_metricFamily
theorem finiteExclusion_family : family.ExcludesFiniteSumCopy := sequence.excludesFiniteSumCopy_metricFamily

theorem almostIsometricAtEveryTolerance_xSpace_ySpace : AlmostIsometricAtEveryTolerance xSpace ySpace :=
  family.almostIsometricAtEveryTolerance_fixedXBanach_fixedYBanach

theorem exists_pointed_equiv (ε : ℝ) (hε : 0 < ε) :
    ∃ f : xSpace.Carrier ≃ ySpace.Carrier,
      f 0 = 0 ∧
      (∀ x x', ‖f x-f x'‖ ≤ (1+ε)*‖x-x'‖) ∧
      (∀ y y', ‖f.symm y-f.symm y'‖ ≤ (1+ε)*‖y-y'‖) :=
  almostIsometricAtEveryTolerance_xSpace_ySpace ε hε

theorem nonisomorphic : IsEmpty (xSpace.Carrier ≃L[ℝ] ySpace.Carrier) :=
  family.nonisomorphic_fixedX_fixedY_of_complemented_splitting_exclusion complementedCopy_family splitting_family finiteExclusion_family

theorem complemented_in_xSpace : ContainsComplementedCopy L1C0L2 xSpace.Carrier :=
  family.fixedX_contains_complemented complementedCopy_family

theorem not_complemented_in_ySpace : ¬ ContainsComplementedCopy L1C0L2 ySpace.Carrier :=
  family.not_complemented_fixedY_of_splitting_and_finite_exclusion splitting_family finiteExclusion_family

theorem finiteDistance_eq_one : LipschitzDistance.finiteDistance xSpace.Carrier ySpace.Carrier = 1 :=
  (family.finiteDistance_one_nonattained complementedCopy_family splitting_family finiteExclusion_family).1

theorem distortion_one_not_attained : 1 ∉ LipschitzDistance.distortions xSpace.Carrier ySpace.Carrier :=
  (family.finiteDistance_one_nonattained complementedCopy_family splitting_family finiteExclusion_family).2

theorem finiteOptimalDistance_eq_one : LipschitzDistance.finiteOptimalDistance xSpace.Carrier ySpace.Carrier = 1 :=
  LipschitzDistance.finiteOptimalDistance_eq_one xSpace ySpace almostIsometricAtEveryTolerance_xSpace_ySpace

theorem optimal_distortion_one_not_attained :
    1 ∉ LipschitzDistance.optimalDistortions xSpace.Carrier ySpace.Carrier := by
  intro h
  exact distortion_one_not_attained
    (LipschitzDistance.optimalDistortions_subset_distortions xSpace.Carrier ySpace.Carrier h)

theorem exists_separated_insertion_images :
    ∃ (z : family.ZInfty) (C : ℝ) (hC : 1 ≤ C) (hbound : ∀ i, family.bound i ≤ C),
      0 < ‖z‖/C ∧
      (∀ N M, N ≠ M → ‖z‖/C ≤
        ‖(family.nearEquiv N C hC (fun i hi => hbound i)).equiv (z,0) -
          (family.nearEquiv M C hC (fun i hi => hbound i)).equiv (z,0)‖) ∧
      ∀ s : ℕ → ℕ, StrictMono s → ¬ CauchySeq (fun n =>
        (family.nearEquiv (s n) C hC (fun i hi => hbound i)).equiv (z,0)) := by
  obtain ⟨z,hz⟩ := exists_ne (0 : family.ZInfty)
  obtain ⟨C,hC,hbound⟩ := family.exists_global_bound
  refine ⟨z,C,hC,hbound,div_pos (norm_pos_iff.mpr hz) (by linarith),?_,?_⟩
  · exact fun N M hNM => family.insertion_images_separated C hC hbound z N M hNM
  · exact fun s hs => family.insertion_images_no_cauchy_subsequence C hC hbound z hz s hs

/-- Actual B substitution, no ordinary mathematical input left. -/
theorem exists_almostIsometric_nonisomorphic_pair : ExistsAlmostIsometricNonisomorphicPair := ⟨xSpace,ySpace,nonisomorphic,almostIsometricAtEveryTolerance_xSpace_ySpace⟩

end AlmostIsometricPair
end BanachGeometry
