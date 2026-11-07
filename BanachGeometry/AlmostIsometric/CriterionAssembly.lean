import BanachGeometry.AlmostIsometric.FixedBanach
import BanachGeometry.SequenceSpaces.L1Linear
import BanachGeometry.Complemented.Factorization
import Mathlib.Analysis.Normed.Operator.Prod

/-! Complemented copy in FixedX from H2 and nonisomorphism from an explicit
complemented-copy obstruction hNoY in FixedY. HeadSplitting derives that
obstruction from coordinate splitting H3 and finite-sum exclusion H4, using
Corner for the joint-tail estimate. NoC0Closure supplies H4 for the constructed
quantitative Hilbert sequence; Existence assembles the fixed pair. -/

noncomputable section
namespace BanachGeometry
namespace AlmostIsometricFamily
variable (d : AlmostIsometricFamily)

def HasContractivelyComplementedCopy : Prop := ∀ i, ∃ (J : C0L2 →L[ℝ] (d.X i).Carrier)
    (P : (d.X i).Carrier →L[ℝ] C0L2),
    (∀ v, ‖J v‖ = ‖v‖) ∧ ‖P‖ ≤ 1 ∧ P.comp J = ContinuousLinearMap.id ℝ C0L2

def HasCoordinateSplitting : Prop := ∀ i, Nonempty ((d.X i).Carrier ≃L[ℝ] ((d.Y i).Carrier × C0L2))

/-- Arbitrary finite lists, including repetitions and the empty list. -/
def ExcludesFiniteSumCopy : Prop := ∀ n : ℕ, ∀ indices : Fin n → ℕ,
  ¬ ContainsLinearCopy C0L2 (∀ r : Fin n, (d.Y (indices r)).Carrier)

theorem fixedX_contains_complemented (h2 : d.HasContractivelyComplementedCopy) :
    ContainsComplementedCopy L1C0L2 d.FixedX := by
  choose J P hJ hP hPJ using h2
  have hJnorm : ∀ i, ‖J i‖ ≤ 1 := by
    intro i
    apply (J i).opNorm_le_bound zero_le_one
    intro v
    simp only [hJ i, one_mul]
    exact le_rfl
  let Ji : L1C0L2 →L[ℝ] d.ZInfty := L1Linear.continuousLinearMap J 1 hJnorm
  let Pi : d.ZInfty →L[ℝ] L1C0L2 := L1Linear.continuousLinearMap P 1 hP
  have hPiJi : Pi.comp Ji = ContinuousLinearMap.id ℝ L1C0L2 := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    change P i (J i (x i)) = x i
    exact congrArg (fun f : C0L2 →L[ℝ] C0L2 => f (x i)) (hPJ i)
  let Jx : L1C0L2 →L[ℝ] d.FixedX :=
    (ContinuousLinearMap.inl ℝ d.ZInfty d.FixedY).comp Ji
  let Px : d.FixedX →L[ℝ] L1C0L2 := Pi.comp (ContinuousLinearMap.fst ℝ d.ZInfty d.FixedY)
  refine ⟨Jx, Px, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  change Pi (Ji x) = x
  exact congrArg (fun f : L1C0L2 →L[ℝ] L1C0L2 => f x) hPiJi

/-- From h2 and the explicit obstruction hNoY, assemble
ExistsAlmostIsometricNonisomorphicPair with the fixed Banach bundles.
HeadSplitting.not_complemented_fixedY_of_splitting_and_finite_exclusion
supplies hNoY from H3/H4; this local theorem retains hNoY in its type. -/
theorem exists_almostIsometric_nonisomorphic_pair_of_complemented_obstruction (h2 : d.HasContractivelyComplementedCopy)
    (hNoY : ¬ ContainsComplementedCopy L1C0L2 d.FixedY) : ExistsAlmostIsometricNonisomorphicPair := by
  refine ⟨d.fixedXBanach, d.fixedYBanach, ?_, d.almostIsometricAtEveryTolerance_fixedXBanach_fixedYBanach⟩
  exact Factorization.nonisomorphic_of_complemented_distinction
    (d.fixedX_contains_complemented h2) hNoY

end AlmostIsometricFamily
end BanachGeometry
