/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.AmplifiedOrbit
import MathlibAnnex.Analysis.CStarAlgebra.FiniteInterpolation

/-!
# Self-adjoint simultaneous approximation in the original algebra

The real orthogonal complement of the self-adjoint orbit is tested against
both the original vector tuple and its orthogonal test tuple. The received
finite-vector approximation supplies a single algebra element for both.
Symmetrization then proves annihilation of the target, and real Hilbert
orthogonality upgrades this to norm-closure membership. In particular, no
continuity of star for the strong operator topology is used.

This generalizes the real-orthogonal-complement argument of the pinned
`FiniteInterpolation` module to genuinely nonunital algebras and inequivalent
families with repeated fibers. There is no norm bound on the witness yet.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter
open scoped ENNReal lp ComplexStarModule

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

open MathlibAnnex.Analysis.InnerProductSpace

/-- The real-linear orbit map on the self-adjoint part of a nonunital algebra. -/
def selfAdjointOrbitMap {A K : Type*} [NonUnitalCStarAlgebra A]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (pi : NonUnitalCStarRepresentation A K) (x : K) : selfAdjoint A →ₗ[ℝ] K where
  toFun a := pi (a : A) x
  map_add' a b := by simp
  map_smul' r a := by
    change pi ((r : ℂ) • (a : A)) x = (r : ℂ) • pi (a : A) x
    rw [map_smul]
    rfl

/-- Real symmetrization controls the adjoint term by a second vector test. -/
theorem re_inner_apply_realPart {A K : Type*} [NonUnitalCStarAlgebra A]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (pi : NonUnitalCStarRepresentation A K) (a : A) (x y : K) :
    (inner ℂ (pi (realPart a : A) x) y).re =
      (2 : ℝ)⁻¹ * ((inner ℂ (pi a x) y).re + (inner ℂ x (pi a y)).re) := by
  rw [realPart_apply_coe, RCLike.real_smul_eq_coe_smul (K := ℂ),
    map_smul, map_add, map_star]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply]
  rw [inner_smul_left, inner_add_left, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left (pi a) y x]
  simp [mul_add]

universe u v w t
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {I : Type v} [Fintype I] {J : I → Type t} [∀ i, Fintype (J i)]
variable {H : I → Type w}
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

set_option backward.isDefEq.respectTransparency false in
/-- An original-algebra self-adjoint element approximates a self-adjoint
classwise action in the Hilbert norm of a finite tuple. Empty tuples,
repeated vectors, and zero vectors are allowed. -/
theorem exists_selfAdjoint_atomic_apply_sub_diagonal_norm_lt
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i k, i ≠ k → ¬ (pi i).UnitaryEquivalent (pi k))
    (xi : ∀ i, J i → H i) (T : ∀ i, H i →L[ℂ] H i)
    (hT : ∀ i, IsSelfAdjoint (T i))
    (C : ℝ) (hC : 0 ≤ C) (hTC : ∀ i, ‖T i‖ ≤ C)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ a : A, IsSelfAdjoint a ∧
      ‖atomicRepresentation (fun q : Sigma J => (pi q.1).unitization)
          (Unitization.inr a) (⟨fun q => xi q.1 q.2, Memℓp.all _⟩ :
            HilbertSum (fun q : Sigma J => H q.1)) -
        diagonal (fun q : Sigma J => T q.1) C hC (fun q => hTC q.1)
          (⟨fun q => xi q.1 q.2, Memℓp.all _⟩ :
            HilbertSum (fun q : Sigma J => H q.1))‖ < epsilon := by
  classical
  let K := HilbertSum (fun q : Sigma J => H q.1)
  let rho := atomicRepresentation (fun q : Sigma J => (pi q.1).unitization)
  let sigma : NonUnitalCStarRepresentation A K :=
    rho.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  let x : K := ⟨fun q => xi q.1 q.2, Memℓp.all _⟩
  let D : K →L[ℂ] K := diagonal (fun q : Sigma J => T q.1) C hC (fun q => hTC q.1)
  let target : K := D x
  letI : NormedSpace ℝ K := NormedSpace.restrictScalars ℝ ℂ K
  letI : Module ℝ K := (NormedSpace.restrictScalars ℝ ℂ K).toModule
  letI : InnerProductSpace ℝ K := InnerProductSpace.rclikeToReal ℂ K
  let L : selfAdjoint A →ₗ[ℝ] K := selfAdjointOrbitMap sigma x
  let M : Submodule ℝ K := LinearMap.range L
  have htarget : target ∈ M.topologicalClosure := by
    apply (le_of_eq M.orthogonal_orthogonal_eq_closure : Mᗮᗮ ≤ M.topologicalClosure)
    rw [Submodule.mem_orthogonal]
    intro y hy
    have horbit (a : selfAdjoint A) : inner ℝ (L a) y = 0 :=
      (M.mem_orthogonal y).mp hy (L a) ⟨a, rfl⟩
    let z : ∀ i, Sum (J i) (J i) → H i := fun i =>
      Sum.elim (xi i) (fun j => y ⟨i, j⟩)
    have happrox (m : ℕ) : ∃ b : A, ∀ i j,
        ‖pi i b (z i j) - T i (z i j)‖ < (((m + 1 : ℕ) : ℝ))⁻¹ := by
      apply exists_forall_apply_sub_norm_lt_of_finite_vector_tests pi hirr hne z T
      positivity
    choose b hb using happrox
    have heps : Tendsto (fun m : ℕ => (((m + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) := by
      simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hcoord (i : I) (j : Sum (J i) (J i)) :
        Tendsto (fun m => pi i (b m) (z i j)) atTop (nhds (T i (z i j))) := by
      have hn : Tendsto (fun m => ‖pi i (b m) (z i j) - T i (z i j)‖)
          atTop (nhds 0) :=
        squeeze_zero (fun _ => norm_nonneg _) (fun m => (hb m i j).le) heps
      have hz := tendsto_zero_iff_norm_tendsto_zero.mpr hn
      convert hz.add_const (T i (z i j)) using 1 <;> simp
    have hf : Tendsto (fun m => (inner ℂ (sigma (b m) x) y).re)
        atTop (nhds (inner ℂ target y).re) := by
      have hi (q : Sigma J) : Tendsto
          (fun m => (inner ℂ (pi q.1 (b m) (xi q.1 q.2)) (y q)).re) atTop
          (nhds (inner ℂ (T q.1 (xi q.1 q.2)) (y q)).re) := by
        exact Complex.continuous_re.continuousAt.tendsto.comp
          ((hcoord q.1 (Sum.inl q.2)).inner tendsto_const_nhds)
      simpa [K, sigma, rho, x, target, D, lp.inner_eq_tsum, tsum_fintype] using
        (tendsto_finsetSum Finset.univ (fun q _ => hi q))
    have hg : Tendsto (fun m => (inner ℂ x (sigma (b m) y)).re)
        atTop (nhds (inner ℂ x (D y)).re) := by
      have hi (q : Sigma J) : Tendsto
          (fun m => (inner ℂ (xi q.1 q.2) (pi q.1 (b m) (y q))).re) atTop
          (nhds (inner ℂ (xi q.1 q.2) (T q.1 (y q))).re) := by
        exact Complex.continuous_re.continuousAt.tendsto.comp
          (tendsto_const_nhds.inner (hcoord q.1 (Sum.inr q.2)))
      simpa [K, sigma, rho, x, D, lp.inner_eq_tsum, tsum_fintype] using
        (tendsto_finsetSum Finset.univ (fun q _ => hi q))
    have hsym : (inner ℂ x (D y)).re = (inner ℂ target y).re := by
      simp only [K, x, D, target, lp.inner_eq_tsum, tsum_fintype, diagonal_apply]
      congr 1
      apply Finset.sum_congr rfl
      intro q _
      have ha : ContinuousLinearMap.adjoint (T q.1) = T q.1 := by
        rw [← ContinuousLinearMap.star_eq_adjoint, (hT q.1).star_eq]
      rw [← ContinuousLinearMap.adjoint_inner_left (T q.1) (y q) (xi q.1 q.2), ha]
    have hzero (m : ℕ) : (inner ℂ (sigma (realPart (b m) : A) x) y).re = 0 := by
      have hz := horbit (realPart (b m))
      change inner ℝ (sigma (realPart (b m) : A) x) y = 0 at hz
      rw [real_inner_eq_re_inner] at hz
      exact hz
    have hsumzero (m : ℕ) :
        (inner ℂ (sigma (b m) x) y).re + (inner ℂ x (sigma (b m) y)).re = 0 := by
      have hs := re_inner_apply_realPart sigma (b m) x y
      rw [hzero m] at hs
      linarith
    have hlim := hf.add hg
    rw [hsym] at hlim
    have hzlim : Tendsto
        (fun m => (inner ℂ (sigma (b m) x) y).re + (inner ℂ x (sigma (b m) y)).re)
        atTop (nhds 0) := by
      simpa only [hsumzero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    have hdouble := tendsto_nhds_unique hlim hzlim
    have hq : (inner ℂ target y).re = 0 := by linarith
    rw [real_inner_eq_re_inner, inner_re_symm]
    exact hq
  change target ∈ closure (M : Set K) at htarget
  obtain ⟨v, hv, hdist⟩ := Metric.mem_closure_iff.mp htarget epsilon hepsilon
  obtain ⟨a, rfl⟩ := hv
  refine ⟨(a : A), a.property, ?_⟩
  change ‖sigma (a : A) x - target‖ < epsilon
  have heval : L a = sigma (a : A) x := rfl
  rw [heval, dist_eq_norm, norm_sub_rev] at hdist
  exact hdist

/-- Simultaneous self-adjoint approximation on all finite tests. This is
still unbounded in the algebra norm; the bounded transform is a later step. -/
theorem exists_selfAdjoint_forall_apply_sub_norm_lt
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i k, i ≠ k → ¬ (pi i).UnitaryEquivalent (pi k))
    (xi : ∀ i, J i → H i) (T : ∀ i, H i →L[ℂ] H i)
    (hT : ∀ i, IsSelfAdjoint (T i))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ a : A, IsSelfAdjoint a ∧ ∀ i j, ‖pi i a (xi i j) - T i (xi i j)‖ < epsilon := by
  classical
  let C : ℝ := ∑ i : I, ‖T i‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => norm_nonneg (T i))
  have hTC (i : I) : ‖T i‖ ≤ C :=
    Finset.single_le_sum (fun k _ => norm_nonneg (T k)) (Finset.mem_univ i)
  obtain ⟨a, ha, happ⟩ := exists_selfAdjoint_atomic_apply_sub_diagonal_norm_lt
    pi hirr hne xi T hT C hC hTC hepsilon
  refine ⟨a, ha, fun i j => ?_⟩
  let x : HilbertSum (fun q : Sigma J => H q.1) :=
    ⟨fun q => xi q.1 q.2, Memℓp.all _⟩
  have hcoord := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (atomicRepresentation (fun q : Sigma J => (pi q.1).unitization)
        (Unitization.inr a) x -
      diagonal (fun q : Sigma J => T q.1) C hC (fun q => hTC q.1) x) ⟨i, j⟩
  have hbound : ‖pi i a (xi i j) - T i (xi i j)‖ ≤
      ‖atomicRepresentation (fun q : Sigma J => (pi q.1).unitization)
          (Unitization.inr a) x -
        diagonal (fun q : Sigma J => T q.1) C hC (fun q => hTC q.1) x‖ := by
    change ‖(pi i).unitization (Unitization.inr a) (xi i j) - T i (xi i j)‖ ≤ _ at hcoord
    simpa only [unitization_inr] using hcoord
  exact hbound.trans_lt happ

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
