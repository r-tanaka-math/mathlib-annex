import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.UniversalStarApproximation
import MathlibAnnex.Analysis.LocallyConvex.FiniteBallNet
import Mathlib.Order.Filter.AtTopBot.Prod

/-!
# One bounded source net, simultaneously for a family of representations

The net carries arbitrary source-dual tests as well as representation/vector
tests. Thus it really converges weak-star to the original F, in addition to
strong-star convergence in every member of the supplied representation
family. Nonunital and degenerate representations are allowed. There is no
countability hypothesis. Universes of A, the family, and the Hilbert spaces
are independent.

C02 controller proof-source candidate. No Lean execution claimed.
-/
set_option autoImplicit false
noncomputable section
open Filter Topology

namespace MathlibAnnex.RepresentedBidual
open MathlibAnnex.FiniteApproximation

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {ι : Type w} (H : ι → Type v)
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, CompleteSpace (H i)]

abbrev UniversalIndex := (Finset (Sigma H) × Finset (StrongDual ℂ A)) × ℕ

/-- Existence at every index uses both sets of tests at once. -/
theorem exists_universal_sample
    (rho : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i))
    (F : StrongDual ℂ (StrongDual ℂ A)) (d : UniversalIndex (A := A) H) :
    ∃ a : A, ‖a‖ ≤ ‖F‖ ∧
      (∀ t ∈ d.1.1,
        ‖rho t.1 a t.2 - extension (rho t.1) F t.2‖ < testTolerance d.2 ∧
        ‖rho t.1 (star a) t.2 - star (extension (rho t.1) F) t.2‖ < testTolerance d.2) ∧
      (∀ f ∈ d.1.2, ‖f a - F f‖ < testTolerance d.2) := by
  classical
  obtain ⟨a, ha, hv, hf⟩ := exists_finite_star_and_scalar_approximation
    (fun t : d.1.1 => H t.1.1)
    (fun t => rho t.1.1) (fun t => t.1.2)
    (fun f : d.1.2 => (f : StrongDual ℂ A)) F (testTolerance_pos d.2)
  exact ⟨a, ha, fun t ht => hv ⟨t, ht⟩, fun f hf' => hf ⟨f, hf'⟩⟩

/-- This is one net for all representations and all source-dual tests. -/
def universalSample
    (rho : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i))
    (F : StrongDual ℂ (StrongDual ℂ A)) (d : UniversalIndex (A := A) H) : A :=
  Classical.choose (exists_universal_sample H rho F d)

theorem universalSample_spec
    (rho : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i))
    (F : StrongDual ℂ (StrongDual ℂ A)) (d : UniversalIndex (A := A) H) :
    ‖universalSample H rho F d‖ ≤ ‖F‖ ∧
      (∀ t ∈ d.1.1,
        ‖rho t.1 (universalSample H rho F d) t.2 - extension (rho t.1) F t.2‖ < testTolerance d.2 ∧
        ‖rho t.1 (star (universalSample H rho F d)) t.2 -
          star (extension (rho t.1) F) t.2‖ < testTolerance d.2) ∧
      (∀ f ∈ d.1.2, ‖f (universalSample H rho F d) - F f‖ < testTolerance d.2) :=
  Classical.choose_spec (exists_universal_sample H rho F d)

theorem universalSample_norm_le
    (rho : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i))
    (F : StrongDual ℂ (StrongDual ℂ A)) (d : UniversalIndex (A := A) H) :
    ‖universalSample H rho F d‖ ≤ ‖F‖ := (universalSample_spec H rho F d).1

/-- Both convergences have exactly the same index and sample. -/
theorem universalSample_strongStar
    (rho : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i))
    (F : StrongDual ℂ (StrongDual ℂ A)) (i : ι) (xi : H i) :
    Tendsto (fun d => rho i (universalSample H rho F d) xi) atTop
      (𝓝 (extension (rho i) F xi)) ∧
    Tendsto (fun d => rho i (star (universalSample H rho F d)) xi) atTop
      (𝓝 (star (extension (rho i) F) xi)) := by
  classical
  constructor
  all_goals
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨n, hn⟩ := exists_testTolerance_lt hε
    filter_upwards [eventually_ge_atTop
      ((({⟨i, xi⟩} : Finset (Sigma H)), (∅ : Finset (StrongDual ℂ A))), n)] with d hd
    have hi : (⟨i, xi⟩ : Sigma H) ∈ d.1.1 := hd.1.1 (by simp)
    have he := (universalSample_spec H rho F d).2.1 ⟨i, xi⟩ hi
    have htol : testTolerance d.2 < ε := (testTolerance_antitone hd.2).trans_lt hn
  · simpa only [dist_eq_norm] using he.1.trans htol
  · simpa only [dist_eq_norm] using he.2.trans htol

/-- Every scalar dual functional is retained, including non-vector tests. -/
theorem universalSample_scalar
    (rho : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i))
    (F : StrongDual ℂ (StrongDual ℂ A)) (f : StrongDual ℂ A) :
    Tendsto (fun d => f (universalSample H rho F d)) atTop (𝓝 (F f)) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := exists_testTolerance_lt hε
  filter_upwards [eventually_ge_atTop
    (((∅ : Finset (Sigma H)), ({f} : Finset (StrongDual ℂ A))), n)] with d hd
  have hf : f ∈ d.1.2 := hd.1.2 (by simp)
  have he := (universalSample_spec H rho F d).2.2 f hf
  have htol := (testTolerance_antitone hd.2).trans_lt hn
  simpa only [dist_eq_norm] using he.trans htol

theorem universalSample_weakStar
    (rho : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i))
    (F : StrongDual ℂ (StrongDual ℂ A)) :
    Tendsto (fun d => StrongDual.toWeakDual
      (NormedSpace.inclusionInDoubleDual ℂ A (universalSample H rho F d)))
      atTop (𝓝 (StrongDual.toWeakDual F)) := by
  apply tendsto_iff_forall_eval_tendsto_topDualPairing.mpr
  intro f
  exact universalSample_scalar H rho F f

end MathlibAnnex.RepresentedBidual
