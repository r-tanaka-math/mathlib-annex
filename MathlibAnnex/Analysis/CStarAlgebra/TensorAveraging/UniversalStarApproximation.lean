import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.RepresentedBidualStar
import MathlibAnnex.Analysis.Normed.Module.BidualRealification
import MathlibAnnex.Analysis.LocallyConvex.FiniteBallApproximation

/-!
# One source contraction for arbitrary finite represented strong-star tests

There is no irreducibility hypothesis. The point being approximated is one
fixed Banach bidual element, and every target operator is its actual C01
represented extension. Real convexity is essential because the adjoint
coordinate is conjugate-linear. Scalar weak-star tests may be imposed on
the very same approximant; they are not replaced by vector coefficients.

C02 proof-source candidate, unbuilt. No abstract C*-structure on A** is
installed, and this file does not assert the existence of a corner section.
-/
set_option autoImplicit false
noncomputable section
open Topology

namespace MathlibAnnex.RepresentedBidual
open MathlibAnnex.BidualRealification MathlibAnnex.FiniteApproximation

universe u v w w'
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The adjoint-vector map is real-linear, never falsely complex-linear. -/
def realStarVectorMap (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (xi : H) : A →L[ℝ] H :=
  LinearMap.mkContinuous
    { toFun := fun a => rho (star a) xi
      map_add' := by intro a b; simp
      map_smul' := by
        intro r a
        simp only [star_smul]
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
        simp only [ContinuousLinearMap.smul_apply,
          RCLike.real_smul_eq_coe_smul (K := ℂ), star_trivial,
          RingHom.id_apply] }
    ‖xi‖ (fun a => by
      calc
        ‖rho (star a) xi‖ ≤ ‖rho (star a)‖ * ‖xi‖ := (rho (star a)).le_opNorm xi
        _ ≤ ‖star a‖ * ‖xi‖ := mul_le_mul_of_nonneg_right
          (NonUnitalStarAlgHom.norm_apply_le rho (star a)) (norm_nonneg xi)
        _ = ‖xi‖ * ‖a‖ := by rw [norm_star, mul_comm])

@[simp] theorem realStarVectorMap_apply
    (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (xi : H) (a : A) :
    realStarVectorMap rho xi a = rho (star a) xi := rfl

/-- The complexification of a real adjoint coefficient is the dual
involution of the forward complex coefficient. -/
theorem complexify_star_coefficient
    (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (xi : H) (g : StrongDual ℝ H) :
    (StrongDual.extendRCLike (𝕜 := ℂ)
      (g.comp (realStarVectorMap rho xi) : StrongDual ℝ A) :
      StrongDual ℂ A) =
      dualStar (coefficient rho xi (g.extendRCLike : StrongDual ℂ H)) := by
  apply eq_of_re_eq
  intro a
  calc
    (StrongDual.extendRCLike (𝕜 := ℂ) (g.comp (realStarVectorMap rho xi)) a).re =
        (g.comp (realStarVectorMap rho xi)) a :=
      StrongDual.re_extendRCLike_apply (𝕜 := ℂ) _ _
    _ = g (rho (star a) xi) := rfl
    _ = ((g.extendRCLike : StrongDual ℂ H) (rho (star a) xi)).re :=
      (StrongDual.re_extendRCLike_apply (𝕜 := ℂ) g _).symm
    _ = (dualStar (coefficient rho xi (g.extendRCLike : StrongDual ℂ H)) a).re := by
      simp only [dualStar_apply, coefficient_apply, Complex.star_def, Complex.conj_re]

/-- Exact real bidual identity for the adjoint coordinate. -/
theorem real_star_vector_identity
    (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (F : StrongDual ℂ (StrongDual ℂ A))
    (xi : H) (g : StrongDual ℝ H) :
    toReal F (g.comp (realStarVectorMap rho xi)) =
      g (star (extension rho F) xi) := by
  rw [toReal_apply, complexify_star_coefficient]
  have hc := coefficient_extension rho (bidualStar F) xi
    (g.extendRCLike : StrongDual ℂ H)
  rw [extension_bidualStar] at hc
  calc
    (F (dualStar (coefficient rho xi g.extendRCLike))).re =
        ((bidualStar F) (coefficient rho xi g.extendRCLike)).re := by
          simp only [bidualStar_apply, Complex.star_def, Complex.conj_re]
    _ = ((g.extendRCLike : StrongDual ℂ H) (star (extension rho F) xi)).re :=
      congrArg Complex.re hc.symm
    _ = g (star (extension rho F) xi) :=
      StrongDual.re_extendRCLike_apply (𝕜 := ℂ) g _

/-- Both operator and adjoint-vector coordinates with one domain element. -/
def realStarPair (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (xi : H) :
    A →L[ℝ] (H × H) :=
  ((vectorMap rho xi).restrictScalars ℝ).prod (realStarVectorMap rho xi)

/-- Target of `realStarPair` at the fixed bidual point. -/
def starPairTarget (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (F : StrongDual ℂ (StrongDual ℂ A)) (xi : H) : H × H :=
  (extension rho F xi, star (extension rho F) xi)

theorem real_star_pair_identity
    (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (F : StrongDual ℂ (StrongDual ℂ A))
    (xi : H) (g : StrongDual ℝ (H × H)) :
    toReal F (g.comp (realStarPair rho xi)) = g (starPairTarget rho F xi) := by
  apply prod_biddual_identity
  · intro k
    exact apply_comp F (vectorMap rho xi) (extension rho F xi)
      (fun l => (coefficient_extension rho F xi l).symm) k
  · intro k
    exact real_star_vector_identity rho F xi k

/-- Complex scalar tests also give honest real bidual coefficient identities. -/
theorem real_scalar_identity (F : StrongDual ℂ (StrongDual ℂ A))
    (f : StrongDual ℂ A) (g : StrongDual ℝ ℂ) :
    toReal F (g.comp (f.restrictScalars ℝ)) = g (F f) := by
  apply apply_comp F f (F f)
  intro k
  have hk : k.comp f = k 1 • f := by
    ext a
    have h := k.map_smul (f a) (1 : ℂ)
    simpa [smul_eq_mul, mul_comm] using h
  rw [hk, map_smul]
  have h := k.map_smul (F f) (1 : ℂ)
  simpa [smul_eq_mul, mul_comm] using h.symm

/-- Arbitrary finitely many (possibly different) Hilbert representations and
vectors admit a common norm-controlled strong-star approximant. -/
theorem exists_finite_star_approximation
    {ι : Type w} [Fintype ι] (K : ι → Type v)
    [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℂ (K i)]
    [∀ i, CompleteSpace (K i)]
    (rho : ∀ i, A →⋆ₙₐ[ℂ] (K i →L[ℂ] K i)) (xi : ∀ i, K i)
    (F : StrongDual ℂ (StrongDual ℂ A)) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, ‖a‖ ≤ ‖F‖ ∧ ∀ i,
      ‖rho i a (xi i) - extension (rho i) F (xi i)‖ < ε ∧
      ‖rho i (star a) (xi i) - star (extension (rho i) F) (xi i)‖ < ε := by
  obtain ⟨a, ha, he⟩ := exists_ball_finite_image_lt
    (fun i => K i × K i) (toReal F) (fun i => realStarPair (rho i) (xi i))
    (fun i => starPairTarget (rho i) F (xi i))
    (fun i g => real_star_pair_identity (rho i) F (xi i) g) hε
  refine ⟨a, ha.trans (norm_toReal_le F), fun i => ?_⟩
  have hi := he i
  change max ‖rho i a (xi i) - extension (rho i) F (xi i)‖
    ‖rho i (star a) (xi i) - star (extension (rho i) F) (xi i)‖ < ε at hi
  exact ⟨(le_max_left _ _).trans_lt hi, (le_max_right _ _).trans_lt hi⟩


/-- Arbitrary scalar dual tests are imposed together with the strong-star
vector tests, rather than silently replaced by represented coefficients. -/
theorem exists_finite_star_and_scalar_approximation
    {ι : Type w} {κ : Type w'} [Fintype ι] [Fintype κ] (K : ι → Type v)
    [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℂ (K i)]
    [∀ i, CompleteSpace (K i)]
    (rho : ∀ i, A →⋆ₙₐ[ℂ] (K i →L[ℂ] K i)) (xi : ∀ i, K i)
    (f : κ → StrongDual ℂ A) (F : StrongDual ℂ (StrongDual ℂ A))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, ‖a‖ ≤ ‖F‖ ∧
      (∀ i, ‖rho i a (xi i) - extension (rho i) F (xi i)‖ < ε ∧
        ‖rho i (star a) (xi i) - star (extension (rho i) F) (xi i)‖ < ε) ∧
      (∀ j, ‖f j a - F (f j)‖ < ε) := by
  let T := ContinuousLinearMap.pi (fun i => realStarPair (rho i) (xi i))
  let z := fun i => starPairTarget (rho i) F (xi i)
  let S := ContinuousLinearMap.pi (fun j => (f j).restrictScalars ℝ)
  let w := fun j => F (f j)
  have hT : ∀ g : StrongDual ℝ (∀ i : ι, K i × K i),
      toReal F (g.comp T) = g z :=
    finite_pi_biddual_identity (fun i => K i × K i) (toReal F)
      (fun i => realStarPair (rho i) (xi i)) z
      (fun i g => real_star_pair_identity (rho i) F (xi i) g)
  have hS : ∀ g : StrongDual ℝ (∀ _ : κ, ℂ), toReal F (g.comp S) = g w :=
    finite_pi_biddual_identity (fun _ : κ => ℂ) (toReal F)
      (fun j => (f j).restrictScalars ℝ) w
      (fun j g => real_scalar_identity F (f j) g)
  obtain ⟨a, ha, he⟩ := exists_ball_image_lt (toReal F) (T.prod S) (z, w)
    (prod_biddual_identity (toReal F) T S z w hT hS) hε
  have heT : ‖T a - z‖ < ε := (le_max_left _ _).trans_lt he
  have heS : ‖S a - w‖ < ε := (le_max_right _ _).trans_lt he
  refine ⟨a, ha.trans (norm_toReal_le F), fun i => ?_, fun j => ?_⟩
  · have hi := (norm_le_pi_norm (T a - z) i).trans_lt heT
    change max ‖rho i a (xi i) - extension (rho i) F (xi i)‖
      ‖rho i (star a) (xi i) - star (extension (rho i) F) (xi i)‖ < ε at hi
    exact ⟨(le_max_left _ _).trans_lt hi, (le_max_right _ _).trans_lt hi⟩
  · exact (norm_le_pi_norm (S a - w) j).trans_lt heS

end MathlibAnnex.RepresentedBidual
