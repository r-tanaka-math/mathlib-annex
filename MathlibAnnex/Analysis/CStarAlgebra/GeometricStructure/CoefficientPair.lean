/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.Normed.Module.DualKernelPair
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.SimultaneousCoefficient
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.CoefficientComponents

/-!
# Closed pairs from inequivalent representations

The finite-kernel argument is algebraic. The l1 norm is proved using a single
original-algebra contraction in `SimultaneousCoefficient`, not two separately
norming elements. Extremality then excludes a nontrivial two-term convex
combination. Both the closed-pair and the distinct-kernel statements are needed:
`Linked` has an equality branch as well as a nonclosed-pair branch.
-/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A] [Nontrivial A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Inequivalent irreducible representations have different nonzero coefficient
kernels. Arbitrary nonzero norms are reduced to unit vectors without changing kernels. -/
theorem matrixCoefficientKernel_ne_of_not_unitaryEquivalent
    (pi : NonUnitalCStarRepresentation A H) (sigma : NonUnitalCStarRepresentation A K)
    (hpi : pi.IsIrreducible) (hsigma : sigma.IsIrreducible) (hne : ¬ pi.UnitaryEquivalent sigma)
    (x y : H) (z w : K) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0) :
    matrixCoefficientKernel pi hpi x y hx hy ≠ matrixCoefficientKernel sigma hsigma z w hz hw := by
  obtain ⟨x', y', hx', hy', hkf⟩ := exists_unit_vectors_ker_matrixCoefficient_eq pi x y hx hy
  obtain ⟨z', w', hz', hw', hkg⟩ := exists_unit_vectors_ker_matrixCoefficient_eq sigma z w hz hw
  have hfn : ‖matrixCoefficient pi x' y'‖ = 1 := by
    rw [norm_matrixCoefficient_of_isIrreducible pi hpi, hx', hy', one_mul]
  have hneq := ContinuousLinearMap.ker_ne_of_norm_smul_add
    (matrixCoefficient pi x' y') (matrixCoefficient sigma z' w') hfn
    (norm_smul_add_matrixCoefficient_of_not_unitaryEquivalent pi sigma hpi hsigma hne
      x' y' z' w' hx' hy' hz' hw')
  intro h
  apply hneq
  rw [hkf, hkg]
  exact SetLike.coe_injective (congrArg Subtype.val h)

/-- Paper 5.8's inequivalent-pair separation, in the received closure space.
Every closure point is represented by an actual extreme functional. Its
finite-kernel factorization and l1 extremality force one endpoint kernel. -/
theorem isClosed_pair_matrixCoefficientKernel_of_not_unitaryEquivalent
    (pi : NonUnitalCStarRepresentation A H) (sigma : NonUnitalCStarRepresentation A K)
    (hpi : pi.IsIrreducible) (hsigma : sigma.IsIrreducible) (hne : ¬ pi.UnitaryEquivalent sigma)
    (x y : H) (z w : K) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0) :
    (NormedSpace.geometricStructureClosure ℂ A).IsClosed
      {matrixCoefficientKernel pi hpi x y hx hy, matrixCoefficientKernel sigma hsigma z w hz hw} := by
  obtain ⟨x', y', hx', hy', hkf⟩ := exists_unit_vectors_ker_matrixCoefficient_eq pi x y hx hy
  obtain ⟨z', w', hz', hw', hkg⟩ := exists_unit_vectors_ker_matrixCoefficient_eq sigma z w hz hw
  let f := matrixCoefficient pi x' y'
  let g := matrixCoefficient sigma z' w'
  have hf : ‖f‖ = 1 := by rw [norm_matrixCoefficient_of_isIrreducible pi hpi, hx', hy', one_mul]
  have hg : ‖g‖ = 1 := by rw [norm_matrixCoefficient_of_isIrreducible sigma hsigma, hz', hw', one_mul]
  have hf0 : f ≠ 0 := norm_ne_zero_iff.mp (by rw [hf]; exact one_ne_zero)
  have hg0 : g ≠ 0 := norm_ne_zero_iff.mp (by rw [hg]; exact one_ne_zero)
  have hl1 := norm_smul_add_matrixCoefficient_of_not_unitaryEquivalent pi sigma hpi hsigma hne
    x' y' z' w' hx' hy' hz' hw'
  apply ((NormedSpace.geometricStructureClosure ℂ A).isClosed_iff_closure_subset _).2
  intro I hI
  rw [NormedSpace.geometricStructureClosure_closure] at hI
  obtain ⟨h, hext, hkI⟩ :=
    (mem_geometricStructureFamily_iff_exists_mem_extremePoints_dual_closedBall I.val).1 I.property
  have hn : ‖h‖ = 1 := norm_eq_one_of_mem_extremePoints_dual_closedBall hext
  have h0 : h ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; exact one_ne_zero)
  have hker : f.ker ⊓ g.ker ≤ h.ker := by
    intro a ha
    have hfa : a ∈ (matrixCoefficientKernel pi hpi x y hx hy).val := by
      change a ∈ (matrixCoefficient pi x y).ker
      rw [← hkf]
      exact ha.1
    have hga : a ∈ (matrixCoefficientKernel sigma hsigma z w hz hw).val := by
      change a ∈ (matrixCoefficient sigma z w).ker
      rw [← hkg]
      exact ha.2
    have haI : a ∈ I.val := hI a (by
      intro J hJ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hJ
      rcases hJ with rfl | rfl
      · exact hfa
      · exact hga)
    rw [← hkI] at haI
    exact haI
  obtain ⟨alpha, beta, hab⟩ :=
    (ContinuousLinearMap.inf_ker_le_ker_iff_exists_smul_add_smul f g h).1 hker
  have hcases : alpha = 0 ∨ beta = 0 :=
    NormedSpace.eq_zero_or_eq_zero_of_extreme_smul_add f g hf hg hl1 alpha beta
      (hab ▸ hext) (hab ▸ hn)
  rcases hcases with halpha | hbeta
  · have hh : h = beta • g := by simpa only [halpha, _root_.zero_smul ℂ f, zero_add] using hab
    have hb0 : beta ≠ 0 := by
      intro hbeta
      apply h0
      rw [hbeta] at hh
      exact hh.trans (_root_.zero_smul ℂ g)
    have hk : g.ker = h.ker :=
      (ContinuousLinearMap.ker_eq_ker_iff_exists_ne_zero_smul hg0).2 ⟨beta, hb0, hh⟩
    have heq : I = matrixCoefficientKernel sigma hsigma z w hz hw := by
      apply Subtype.ext
      rw [← hkI, ← hk]
      exact congrArg (fun P : Submodule ℂ A => (P : Set A)) hkg
    exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr heq)
  · have hh : h = alpha • f := by simpa only [hbeta, _root_.zero_smul ℂ g, add_zero] using hab
    have ha0 : alpha ≠ 0 := by
      intro halpha
      apply h0
      rw [halpha] at hh
      exact hh.trans (_root_.zero_smul ℂ f)
    have hk : f.ker = h.ker :=
      (ContinuousLinearMap.ker_eq_ker_iff_exists_ne_zero_smul hf0).2 ⟨alpha, ha0, hh⟩
    have heq : I = matrixCoefficientKernel pi hpi x y hx hy := by
      apply Subtype.ext
      rw [← hkI, ← hk]
      exact congrArg (fun P : Submodule ℂ A => (P : Set A)) hkf
    exact Set.mem_insert_iff.mpr (Or.inl heq)

/-- A Linked step between represented kernel points forces equivalence.
The equality branch uses the separately proved kernel-distinctness theorem. -/
theorem unitaryEquivalent_of_linked_matrixCoefficientKernel
    (pi : NonUnitalCStarRepresentation A H) (sigma : NonUnitalCStarRepresentation A K)
    (hpi : pi.IsIrreducible) (hsigma : sigma.IsIrreducible)
    (x y : H) (z w : K) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0)
    (hlink : (NormedSpace.geometricStructureClosure ℂ A).Linked
      (matrixCoefficientKernel pi hpi x y hx hy) (matrixCoefficientKernel sigma hsigma z w hz hw)) :
    pi.UnitaryEquivalent sigma := by
  by_contra hne
  rcases hlink with heq | hnc
  · exact matrixCoefficientKernel_ne_of_not_unitaryEquivalent
      pi sigma hpi hsigma hne x y z w hx hy hz hw heq
  · exact hnc (isClosed_pair_matrixCoefficientKernel_of_not_unitaryEquivalent
      pi sigma hpi hsigma hne x y z w hx hy hz hw)

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
