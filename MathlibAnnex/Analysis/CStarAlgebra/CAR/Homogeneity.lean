import MathlibAnnex.Analysis.CStarAlgebra.ApproximateIntertwining
import MathlibAnnex.Analysis.CStarAlgebra.CAR.FiniteAverage
import MathlibAnnex.Analysis.CStarAlgebra.CAR.NoCompacts
import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.KishimotoOzawaSakai

/-!
# The CAR homogeneity endpoint and its two-sided limit adapter

`PureStateHomogeneity` is the exact CAR-specialized endpoint (`K_CAR`).  The
second definition records the constructive output still required from the
local pure-state movement argument.  The theorem in this file closes that
output by the proved two-sided point-norm limit machinery; it does not assume
an automorphism or homogeneity as an input.
-/

set_option autoImplicit false

open Filter

namespace MathlibAnnex.CStarAlgebra.CAR

/-- Approximate-inner homogeneity for the actual completed CAR algebra.  This
is the exact `K_CAR` proposition and is deliberately distinct from the
all-simple-algebras statement `MathlibAnnex.CStarAlgebra.KishimotoOzawaSakaiProperty`. -/
def PureStateHomogeneity : Prop :=
  ∀ (phi psi : Limit →L[ℂ] ℂ), MathlibAnnex.CStarAlgebra.IsPureState Limit phi →
    MathlibAnnex.CStarAlgebra.IsPureState Limit psi →
      ∃ alpha : Limit ≃⋆ₐ[ℂ] Limit,
        (∀ a : Limit, phi (alpha a) = psi a) ∧
        ∀ (F : Finset Limit) (epsilon : ℝ), 0 < epsilon →
          ∃ v : unitary Limit, ∀ a ∈ F,
            ‖alpha a - (v : Limit) * a * star (v : Limit)‖ < epsilon

/-- Asymptotically-inner homogeneity for the completed CAR algebra.  The
implementing path is parametrized by `ℝ` and starts at one.  Negative-time
constancy is a property of the concrete path built below, not a field of this
predicate.  Both the automorphisms and their actual inverses converge
point-norm. -/
def AsymptoticallyInnerPureStateHomogeneity : Prop :=
  ∀ (phi psi : Limit →L[ℂ] ℂ), MathlibAnnex.CStarAlgebra.IsPureState Limit phi →
    MathlibAnnex.CStarAlgebra.IsPureState Limit psi →
      ∃ alpha : Limit ≃⋆ₐ[ℂ] Limit, ∃ U : ℝ → unitary Limit,
        Continuous U ∧ U 0 = 1 ∧
        (∀ a : Limit, phi (alpha a) = psi a) ∧
        (∀ a : Limit, Tendsto
          (fun t ↦ Unitary.conjStarAlgAut ℂ Limit (U t) a)
          atTop (nhds (alpha a))) ∧
        ∀ a : Limit, Tendsto
          (fun t ↦ (Unitary.conjStarAlgAut ℂ Limit (U t)).symm a)
          atTop (nhds (alpha.symm a))

set_option maxHeartbeats 800000 in
/-- Forgetting the path, asymptotically-inner homogeneity implies the
original point-norm approximately-inner endpoint. -/
theorem homogeneity_of_asymptoticallyInner
    (h : AsymptoticallyInnerPureStateHomogeneity) : PureStateHomogeneity := by
  intro phi psi hphi hpsi
  obtain ⟨alpha, U, _hU, _hU0, hstate, hforward, _hinverse⟩ :=
    h phi psi hphi hpsi
  refine ⟨alpha, hstate, ?_⟩
  intro F epsilon hepsilon
  have hfinite : ∀ᶠ t in atTop, ∀ a ∈ F,
      ‖alpha a - Unitary.conjStarAlgAut ℂ Limit (U t) a‖ < epsilon := by
    apply (F.eventually_all).2
    intro a _ha
    have ha := (hforward a) (Metric.ball_mem_nhds _ hepsilon)
    filter_upwards [ha] with t ht
    change dist (Unitary.conjStarAlgAut ℂ Limit (U t) a) (alpha a) < epsilon at ht
    rw [dist_eq_norm, norm_sub_rev] at ht
    exact ht
  obtain ⟨t, ht⟩ := hfinite.exists
  refine ⟨U t, ?_⟩
  intro a ha
  change ‖alpha a - Unitary.conjStarAlgAut ℂ Limit (U t) a‖ < epsilon
  exact ht a ha

/-- Concrete two-sided output expected from an alternating local movement
construction.  It asks for inner automorphisms, pointwise Cauchy control of
both them and their actual inverses, and convergence of the transported
state.  It contains no endpoint automorphism field. -/
def HasInnerIntertwiningSequence (phi psi : Limit →L[ℂ] ℂ) : Prop :=
  ∃ f : ℕ → StarAlgEquiv ℂ Limit Limit,
    (∀ a, CauchySeq (fun n => f n a)) ∧
    (∀ a, CauchySeq (fun n => (f n).symm a)) ∧
    (∀ n, ∃ u : unitary Limit,
      f n = Unitary.conjStarAlgAut ℂ Limit u) ∧
    ∀ a, Tendsto (fun n => phi (f n a)) atTop (nhds (psi a))

/-- The proved two-sided limit turns the exact constructive sequence contract
into the exact CAR endpoint.  In particular, surjectivity is not inferred
from a forward pointwise limit alone. -/
theorem homogeneity_of_innerIntertwiningSequences
    (hlocal : ∀ (phi psi : Limit →L[ℂ] ℂ),
      MathlibAnnex.CStarAlgebra.IsPureState Limit phi → MathlibAnnex.CStarAlgebra.IsPureState Limit psi →
        HasInnerIntertwiningSequence phi psi) :
    PureStateHomogeneity := by
  intro phi psi hphi hpsi
  obtain ⟨f, hf, hfinv, hinner, hstate⟩ := hlocal phi psi hphi hpsi
  let alpha := MathlibAnnex.CStarAlgebra.twoSidedPointwiseLimit f hf hfinv
  have hend :=
    MathlibAnnex.CStarAlgebra.twoSidedPointwiseLimit_state_and_approximatelyInner
      f hf hfinv hinner phi psi hstate
  refine ⟨alpha, hend.1, ?_⟩
  exact hend.2

end MathlibAnnex.CStarAlgebra.CAR
