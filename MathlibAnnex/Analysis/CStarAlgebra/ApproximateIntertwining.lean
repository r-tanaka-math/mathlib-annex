import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Two-sided pointwise limits of C-star algebra automorphisms

The forward and inverse pointwise limits are kept together.  This is the
closure step required by an alternating approximately-inner construction:
pointwise convergence of the forward maps alone would not prove surjectivity.
-/

set_option autoImplicit false

open Filter

namespace MathlibAnnex.CStarAlgebra

variable {A : Type*} [CStarAlgebra A]

/-- Summable pointwise increments give the Cauchy input used by the
two-sided limit construction.  This records the actual norm budget rather
than requiring convergence of the implementing unitaries. -/
theorem cauchySeq_of_summable_norm_step (f : ℕ → A)
    (hf : Summable fun n => ‖f (n + 1) - f n‖) : CauchySeq f := by
  apply cauchySeq_of_summable_dist
  simpa only [Nat.succ_eq_add_one, dist_eq_norm, norm_sub_rev] using hf

/-- Point-norm approximate innerness, with one unitary serving the whole
finite set. -/
def IsPointNormApproximatelyInner (alpha : A ≃⋆ₐ[ℂ] A) : Prop :=
  ∀ (F : Finset A) (epsilon : ℝ), 0 < epsilon →
    ∃ u : unitary A, ∀ a ∈ F,
      ‖alpha a - Unitary.conjStarAlgAut ℂ A u a‖ < epsilon

/-- The chosen pointwise limit of a pointwise Cauchy automorphism sequence. -/
noncomputable def pointwiseLimit (f : ℕ → StarAlgEquiv ℂ A A)
    (hf : ∀ a, CauchySeq (fun n => f n a)) (a : A) : A :=
  Classical.choose (cauchySeq_tendsto_of_complete (hf a))

theorem tendsto_pointwiseLimit (f : ℕ → StarAlgEquiv ℂ A A)
    (hf : ∀ a, CauchySeq (fun n => f n a)) (a : A) :
    Tendsto (fun n => f n a) atTop (nhds (pointwiseLimit f hf a)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (hf a))

/-- Algebraic operations pass to the chosen pointwise limit. -/
noncomputable def pointwiseLimitHom (f : ℕ → StarAlgEquiv ℂ A A)
    (hf : ∀ a, CauchySeq (fun n => f n a)) : A →⋆ₐ[ℂ] A where
  toFun := pointwiseLimit f hf
  map_one' := by
    apply tendsto_nhds_unique (tendsto_pointwiseLimit f hf 1)
    simp
  map_mul' a b := by
    apply tendsto_nhds_unique (tendsto_pointwiseLimit f hf (a * b))
    simpa only [map_mul] using
      (tendsto_pointwiseLimit f hf a).mul (tendsto_pointwiseLimit f hf b)
  map_zero' := by
    apply tendsto_nhds_unique (tendsto_pointwiseLimit f hf 0)
    simp
  map_add' a b := by
    apply tendsto_nhds_unique (tendsto_pointwiseLimit f hf (a + b))
    simpa only [map_add] using
      (tendsto_pointwiseLimit f hf a).add (tendsto_pointwiseLimit f hf b)
  commutes' c := by
    apply tendsto_nhds_unique (tendsto_pointwiseLimit f hf ((algebraMap ℂ A) c))
    simpa only [Algebra.algebraMap_eq_smul_one, map_smul, map_one] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => c • (1 : A)) atTop (nhds (c • 1)))
  map_star' a := by
    apply tendsto_nhds_unique (tendsto_pointwiseLimit f hf (star a))
    have hstar := (continuous_star.tendsto _).comp (tendsto_pointwiseLimit f hf a)
    have hfun : (fun n => f n (star a)) = star ∘ (fun n => f n a) := by
      funext n
      exact map_star (f n) a
    rw [hfun]
    exact hstar

@[simp] theorem pointwiseLimitHom_apply (f : ℕ → StarAlgEquiv ℂ A A)
    (hf : ∀ a, CauchySeq (fun n => f n a)) (a : A) :
    pointwiseLimitHom f hf a = pointwiseLimit f hf a := rfl

/-- Isometric diagonal approximation identifies the value of the pointwise
limit at a moving input. -/
theorem pointwiseLimitHom_apply_eq_of_diagonal
    (f : ℕ → StarAlgEquiv ℂ A A) (hf : ∀ a, CauchySeq (fun n => f n a))
    (g : ℕ → A) (b c : A) (hg : Tendsto g atTop (nhds b))
    (hdiag : Tendsto (fun n => f n (g n)) atTop (nhds c)) :
    pointwiseLimitHom f hf b = c := by
  have hfixed : Tendsto (fun n => f n b) atTop
      (nhds (pointwiseLimitHom f hf b)) := tendsto_pointwiseLimit f hf b
  have hto_c : Tendsto (fun n => f n b) atTop (nhds c) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨Ng, hNg⟩ := (Metric.tendsto_atTop.mp hg) (epsilon / 2) (by positivity)
    obtain ⟨Nd, hNd⟩ := (Metric.tendsto_atTop.mp hdiag) (epsilon / 2) (by positivity)
    refine ⟨max Ng Nd, fun n hn => ?_⟩
    have hg_n := hNg n (le_trans (le_max_left Ng Nd) hn)
    have hd_n := hNd n (le_trans (le_max_right Ng Nd) hn)
    have hdist : dist (f n b) (f n (g n)) = dist b (g n) :=
      (StarAlgEquiv.isometry (f n)).dist_eq b (g n)
    calc
      dist (f n b) c ≤ dist (f n b) (f n (g n)) + dist (f n (g n)) c :=
        dist_triangle _ _ _
      _ = dist b (g n) + dist (f n (g n)) c := by rw [hdist]
      _ < epsilon / 2 + epsilon / 2 := by
        apply add_lt_add
        · simpa only [dist_comm] using hg_n
        · exact hd_n
      _ = epsilon := by ring
  exact tendsto_nhds_unique hfixed hto_c

/-- A two-sided pointwise Cauchy sequence of star-algebra equivalences has a
star-algebra equivalence as its limit.  The diagonal composition hypotheses
are the forward/inverse controls needed to prevent a merely injective limit. -/
noncomputable def pointwiseLimitEquiv
    (f g : ℕ → StarAlgEquiv ℂ A A)
    (hf : ∀ a, CauchySeq (fun n => f n a))
    (hg : ∀ a, CauchySeq (fun n => g n a))
    (hfg : ∀ a, Tendsto (fun n => f n (g n a)) atTop (nhds a))
    (hgf : ∀ a, Tendsto (fun n => g n (f n a)) atTop (nhds a)) :
    StarAlgEquiv ℂ A A := by
  let F := pointwiseLimitHom f hf
  let G := pointwiseLimitHom g hg
  have hFG (a : A) : F (G a) = a := by
    apply pointwiseLimitHom_apply_eq_of_diagonal f hf (fun n => g n a) (G a) a
    · exact tendsto_pointwiseLimit g hg a
    · exact hfg a
  have hGF (a : A) : G (F a) = a := by
    apply pointwiseLimitHom_apply_eq_of_diagonal g hg (fun n => f n a) (F a) a
    · exact tendsto_pointwiseLimit f hf a
    · exact hgf a
  exact StarAlgEquiv.ofBijective F ⟨
    fun x y hxy => by rw [← hGF x, ← hGF y, hxy],
    fun y => ⟨G y, hFG y⟩⟩

@[simp] theorem pointwiseLimitEquiv_apply
    (f g : ℕ → StarAlgEquiv ℂ A A)
    (hf : ∀ a, CauchySeq (fun n => f n a))
    (hg : ∀ a, CauchySeq (fun n => g n a))
    (hfg : ∀ a, Tendsto (fun n => f n (g n a)) atTop (nhds a))
    (hgf : ∀ a, Tendsto (fun n => g n (f n a)) atTop (nhds a)) (a : A) :
    pointwiseLimitEquiv f g hf hg hfg hgf a = pointwiseLimitHom f hf a := rfl

/-- A pointwise limit of inner automorphisms is point-norm approximately
inner on every finite set.  Surjectivity of the limit is supplied separately
by the inverse and diagonal hypotheses of `pointwiseLimitEquiv`. -/
theorem isPointNormApproximatelyInner_pointwiseLimitEquiv
    (f g : ℕ → StarAlgEquiv ℂ A A)
    (hf : ∀ a, CauchySeq (fun n => f n a))
    (hg : ∀ a, CauchySeq (fun n => g n a))
    (hfg : ∀ a, Tendsto (fun n => f n (g n a)) atTop (nhds a))
    (hgf : ∀ a, Tendsto (fun n => g n (f n a)) atTop (nhds a))
    (hinner : ∀ n, ∃ u : unitary A, f n = Unitary.conjStarAlgAut ℂ A u) :
    IsPointNormApproximatelyInner (pointwiseLimitEquiv f g hf hg hfg hgf) := by
  intro F epsilon hepsilon
  have hconv (a : A) : Tendsto (fun n => f n a) atTop
      (nhds (pointwiseLimitEquiv f g hf hg hfg hgf a)) := by
    simpa only [pointwiseLimitEquiv_apply, pointwiseLimitHom_apply] using
      tendsto_pointwiseLimit f hf a
  have hfinite : ∀ᶠ n in atTop, ∀ a ∈ F,
      ‖pointwiseLimitEquiv f g hf hg hfg hgf a - f n a‖ < epsilon := by
    apply (F.eventually_all).2
    intro a _ha
    have ha : ∀ᶠ n in atTop,
        f n a ∈ Metric.ball (pointwiseLimitEquiv f g hf hg hfg hgf a) epsilon :=
      (hconv a) (Metric.ball_mem_nhds _ hepsilon)
    filter_upwards [ha] with n hn
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hn
  obtain ⟨n, hn⟩ := hfinite.exists
  obtain ⟨u, hu⟩ := hinner n
  refine ⟨u, fun a ha => ?_⟩
  rw [← hu]
  exact hn a ha

/-- The state equation also passes to the same forward pointwise limit.
Together with the preceding theorem this is the non-circular global closure
used after a local alternating construction has produced its two sequences. -/
theorem pointwiseLimitEquiv_state_and_approximatelyInner
    (f g : ℕ → StarAlgEquiv ℂ A A)
    (hf : ∀ a, CauchySeq (fun n => f n a))
    (hg : ∀ a, CauchySeq (fun n => g n a))
    (hfg : ∀ a, Tendsto (fun n => f n (g n a)) atTop (nhds a))
    (hgf : ∀ a, Tendsto (fun n => g n (f n a)) atTop (nhds a))
    (hinner : ∀ n, ∃ u : unitary A, f n = Unitary.conjStarAlgAut ℂ A u)
    (phi psi : A →L[ℂ] ℂ)
    (hstate : ∀ a, Tendsto (fun n => phi (f n a)) atTop (nhds (psi a))) :
    (∀ a, phi (pointwiseLimitEquiv f g hf hg hfg hgf a) = psi a) ∧
      IsPointNormApproximatelyInner (pointwiseLimitEquiv f g hf hg hfg hgf) := by
  refine ⟨?_, isPointNormApproximatelyInner_pointwiseLimitEquiv
    f g hf hg hfg hgf hinner⟩
  intro a
  apply tendsto_nhds_unique
    ((phi.continuous.tendsto _).comp (show Tendsto (fun n => f n a) atTop
      (nhds (pointwiseLimitEquiv f g hf hg hfg hgf a)) by
        simpa only [pointwiseLimitEquiv_apply, pointwiseLimitHom_apply] using
          tendsto_pointwiseLimit f hf a))
  exact hstate a

/-- The two-sided pointwise limit when the inverse sequence is literally the
sequence of inverse automorphisms.  Requiring both pointwise Cauchy conditions
is essential; the diagonal composition conditions are then exact. -/
noncomputable def twoSidedPointwiseLimit
    (f : ℕ → StarAlgEquiv ℂ A A)
    (hf : ∀ a, CauchySeq (fun n => f n a))
    (hfinv : ∀ a, CauchySeq (fun n => (f n).symm a)) :
    StarAlgEquiv ℂ A A :=
  pointwiseLimitEquiv f (fun n => (f n).symm) hf hfinv
    (fun a => by simpa using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => a) atTop (nhds a)))
    (fun a => by simpa using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => a) atTop (nhds a)))

@[simp] theorem twoSidedPointwiseLimit_apply
    (f : ℕ → StarAlgEquiv ℂ A A)
    (hf : ∀ a, CauchySeq (fun n => f n a))
    (hfinv : ∀ a, CauchySeq (fun n => (f n).symm a)) (a : A) :
    twoSidedPointwiseLimit f hf hfinv a = pointwiseLimitHom f hf a :=
  rfl

/-- The inverse of the two-sided pointwise limit is the pointwise limit of
the actual inverse sequence. -/
theorem twoSidedPointwiseLimit_symm_apply
    (f : ℕ → StarAlgEquiv ℂ A A)
    (hf : ∀ a, CauchySeq (fun n ↦ f n a))
    (hfinv : ∀ a, CauchySeq (fun n ↦ (f n).symm a)) (a : A) :
    (twoSidedPointwiseLimit f hf hfinv).symm a =
      pointwiseLimitHom (fun n ↦ (f n).symm) hfinv a := by
  apply (twoSidedPointwiseLimit f hf hfinv).injective
  calc
    _ = a := (twoSidedPointwiseLimit f hf hfinv).apply_symm_apply a
    _ = _ := by
      symm
      change pointwiseLimitHom f hf
          (pointwiseLimitHom (fun n ↦ (f n).symm) hfinv a) = a
      apply pointwiseLimitHom_apply_eq_of_diagonal f hf
        (fun n ↦ (f n).symm a)
      · exact tendsto_pointwiseLimit (fun n ↦ (f n).symm) hfinv a
      · simpa using (tendsto_const_nhds :
          Tendsto (fun _ : ℕ ↦ a) atTop (nhds a))

/-- Summable forward and inverse pointwise increments are a concrete budget
for the two Cauchy hypotheses of `twoSidedPointwiseLimit`. -/
theorem twoSidedPointwiseCauchy_of_summable
    (f : ℕ → StarAlgEquiv ℂ A A)
    (hforward : ∀ a, Summable fun n => ‖f (n + 1) a - f n a‖)
    (hinverse : ∀ a, Summable fun n =>
      ‖(f (n + 1)).symm a - (f n).symm a‖) :
    (∀ a, CauchySeq (fun n => f n a)) ∧
      ∀ a, CauchySeq (fun n => (f n).symm a) :=
  ⟨fun a => cauchySeq_of_summable_norm_step _ (hforward a),
    fun a => cauchySeq_of_summable_norm_step _ (hinverse a)⟩

/-- Global approximately-inner state transport from a genuine two-sided
inner-automorphism sequence.  This is the reusable limit endpoint for the
alternating local construction; no convergence of the implementing
unitaries themselves is assumed. -/
theorem twoSidedPointwiseLimit_state_and_approximatelyInner
    (f : ℕ → StarAlgEquiv ℂ A A)
    (hf : ∀ a, CauchySeq (fun n => f n a))
    (hfinv : ∀ a, CauchySeq (fun n => (f n).symm a))
    (hinner : ∀ n, ∃ u : unitary A, f n = Unitary.conjStarAlgAut ℂ A u)
    (phi psi : A →L[ℂ] ℂ)
    (hstate : ∀ a, Tendsto (fun n => phi (f n a)) atTop (nhds (psi a))) :
    (∀ a, phi (twoSidedPointwiseLimit f hf hfinv a) = psi a) ∧
      IsPointNormApproximatelyInner (twoSidedPointwiseLimit f hf hfinv) := by
  exact pointwiseLimitEquiv_state_and_approximatelyInner
    f (fun n => (f n).symm) hf hfinv
    (fun a => by simpa using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => a) atTop (nhds a)))
    (fun a => by simpa using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => a) atTop (nhds a)))
    hinner phi psi hstate

end MathlibAnnex.CStarAlgebra
