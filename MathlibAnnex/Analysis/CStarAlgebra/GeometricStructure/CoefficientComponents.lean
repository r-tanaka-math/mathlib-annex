/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.CoefficientKernel
import MathlibAnnex.Topology.ClosureSpace.Components

/-!
# Coefficient lines and finite-chain components

A sum of two coefficients with a common source or target supplies a third
actual GSS kernel in the closure of the original pair. Distinct endpoints
ensure the summed coefficient is nonzero and that its kernel differs from
either endpoint. Hence changing one vector gives a Linked step, and changing
both vectors gives a two-step Related chain in the original closure space.

This proves the same-representation direction. It does not assert that a
pair from inequivalent representations is closed, nor does it redefine the
received relation using representation classes.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A] [Nontrivial A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem add_ne_zero_and_ker_ne
    {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] (f g : StrongDual 𝕜 V)
    (hf : f ≠ 0) (hg : g ≠ 0) (hne : f.ker ≠ g.ker) :
    f + g ≠ 0 ∧ (f + g).ker ≠ f.ker ∧ (f + g).ker ≠ g.ker := by
  have hleft (l m : StrongDual 𝕜 V) (hl : l ≠ 0) (hm : m ≠ 0)
      (hker : l.ker ≠ m.ker) : (l + m).ker ≠ l.ker := by
    intro heq
    obtain ⟨c, _, hc⟩ :=
      (ContinuousLinearMap.ker_eq_ker_iff_exists_ne_zero_smul hl).1 heq.symm
    have hm' : m = (c - 1) • l := by
      calc
        m = (l + m) - l := by abel
        _ = c • l - l := by rw [hc]
        _ = (c - 1) • l := by
          simpa only [_root_.one_smul] using (_root_.sub_smul c (1 : 𝕜) l).symm
    have hc0 : c - 1 ≠ 0 := by
      intro hz
      apply hm
      rw [hz] at hm'
      exact hm'.trans (_root_.zero_smul 𝕜 l)
    exact hker ((ContinuousLinearMap.ker_eq_ker_iff_exists_ne_zero_smul hl).2
      ⟨c - 1, hc0, hm'⟩)
  refine ⟨?_, hleft f g hf hg hne, ?_⟩
  · intro hz
    have hg' : g = (-1 : 𝕜) • f := by
      calc
        g = (f + g) - f := by abel
        _ = -f := by rw [hz, zero_sub]
        _ = (-1 : 𝕜) • f := (_root_.neg_one_smul 𝕜 f).symm
    exact hne ((ContinuousLinearMap.ker_eq_ker_iff_exists_ne_zero_smul hf).2
      ⟨-1, by norm_num, hg'⟩)
  · simpa only [add_comm] using hleft g f hg hf (Ne.symm hne)

/-- A distinct common-source pair has a third actual kernel point in its closure. -/
theorem exists_mem_closure_pair_matrixCoefficientKernel_ne_right
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y z : H) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hne : matrixCoefficientKernel pi hpi x y hx hy ≠
      matrixCoefficientKernel pi hpi x z hx hz) :
    ∃ I : NormedSpace.GeometricStructureSpace ℂ A,
      I ∈ (NormedSpace.geometricStructureClosure ℂ A).closure
        {matrixCoefficientKernel pi hpi x y hx hy, matrixCoefficientKernel pi hpi x z hx hz} ∧
      I ≠ matrixCoefficientKernel pi hpi x y hx hy ∧
      I ≠ matrixCoefficientKernel pi hpi x z hx hz := by
  let f := matrixCoefficient pi x y
  let g := matrixCoefficient pi x z
  have hf : f ≠ 0 := (matrixCoefficient_ne_zero_iff pi hpi x y).2 ⟨hx, hy⟩
  have hg : g ≠ 0 := (matrixCoefficient_ne_zero_iff pi hpi x z).2 ⟨hx, hz⟩
  have hker : f.ker ≠ g.ker := by
    intro h
    exact hne (Subtype.ext (congrArg (fun P : Submodule ℂ A => (P : Set A)) h))
  have hs := add_ne_zero_and_ker_ne f g hf hg hker
  have hyz : y + z ≠ 0 := by
    intro h
    apply hs.1
    change matrixCoefficient pi x y + matrixCoefficient pi x z = 0
    rw [← matrixCoefficient_add_right, h, matrixCoefficient_zero_right]
  let I := matrixCoefficientKernel pi hpi x (y + z) hx hyz
  refine ⟨I, ?_, ?_, ?_⟩
  · rw [NormedSpace.geometricStructureClosure_closure]
    intro a ha
    have hfa : f a = 0 := ha (matrixCoefficientKernel pi hpi x y hx hy) (by simp)
    have hga : g a = 0 := ha (matrixCoefficientKernel pi hpi x z hx hz) (by simp)
    change matrixCoefficient pi x (y + z) a = 0
    rw [matrixCoefficient_add_right, ContinuousLinearMap.add_apply, hfa, hga, add_zero]
  · intro h
    apply hs.2.1
    apply SetLike.coe_injective
    simpa only [I, coe_matrixCoefficientKernel, matrixCoefficient_add_right]
      using congrArg Subtype.val h
  · intro h
    apply hs.2.2
    apply SetLike.coe_injective
    simpa only [I, coe_matrixCoefficientKernel, matrixCoefficient_add_right]
      using congrArg Subtype.val h

/-- A distinct common-target pair has a third actual kernel point in its closure. -/
theorem exists_mem_closure_pair_matrixCoefficientKernel_ne_left
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x z y : H) (hx : x ≠ 0) (hz : z ≠ 0) (hy : y ≠ 0)
    (hne : matrixCoefficientKernel pi hpi x y hx hy ≠
      matrixCoefficientKernel pi hpi z y hz hy) :
    ∃ I : NormedSpace.GeometricStructureSpace ℂ A,
      I ∈ (NormedSpace.geometricStructureClosure ℂ A).closure
        {matrixCoefficientKernel pi hpi x y hx hy, matrixCoefficientKernel pi hpi z y hz hy} ∧
      I ≠ matrixCoefficientKernel pi hpi x y hx hy ∧
      I ≠ matrixCoefficientKernel pi hpi z y hz hy := by
  let f := matrixCoefficient pi x y
  let g := matrixCoefficient pi z y
  have hf : f ≠ 0 := (matrixCoefficient_ne_zero_iff pi hpi x y).2 ⟨hx, hy⟩
  have hg : g ≠ 0 := (matrixCoefficient_ne_zero_iff pi hpi z y).2 ⟨hz, hy⟩
  have hker : f.ker ≠ g.ker := by
    intro h
    exact hne (Subtype.ext (congrArg (fun P : Submodule ℂ A => (P : Set A)) h))
  have hs := add_ne_zero_and_ker_ne f g hf hg hker
  have hxz : x + z ≠ 0 := by
    intro h
    apply hs.1
    change matrixCoefficient pi x y + matrixCoefficient pi z y = 0
    rw [← matrixCoefficient_add_left, h, matrixCoefficient_zero_left]
  let I := matrixCoefficientKernel pi hpi (x + z) y hxz hy
  refine ⟨I, ?_, ?_, ?_⟩
  · rw [NormedSpace.geometricStructureClosure_closure]
    intro a ha
    have hfa : f a = 0 := ha (matrixCoefficientKernel pi hpi x y hx hy) (by simp)
    have hga : g a = 0 := ha (matrixCoefficientKernel pi hpi z y hz hy) (by simp)
    change matrixCoefficient pi (x + z) y a = 0
    rw [matrixCoefficient_add_left, ContinuousLinearMap.add_apply, hfa, hga, add_zero]
  · intro h
    apply hs.2.1
    apply SetLike.coe_injective
    simpa only [I, coe_matrixCoefficientKernel, matrixCoefficient_add_left]
      using congrArg Subtype.val h
  · intro h
    apply hs.2.2
    apply SetLike.coe_injective
    simpa only [I, coe_matrixCoefficientKernel, matrixCoefficient_add_left]
      using congrArg Subtype.val h

/-- Paper 5.6, common source: distinct nonzero target lines give a nonclosed pair. -/
theorem not_isClosed_pair_matrixCoefficientKernel_of_span_ne_right
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y z : H) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hline : Submodule.span ℂ {y} ≠ Submodule.span ℂ {z}) :
    ¬ (NormedSpace.geometricStructureClosure ℂ A).IsClosed
      {matrixCoefficientKernel pi hpi x y hx hy, matrixCoefficientKernel pi hpi x z hx hz} := by
  have hne := mt (matrixCoefficientKernel_eq_iff_span_eq_right pi hpi x y z hx hy hz).1 hline
  obtain ⟨I, hI, hI0, hI1⟩ :=
    exists_mem_closure_pair_matrixCoefficientKernel_ne_right pi hpi x y z hx hy hz hne
  intro hc
  have hm := ((NormedSpace.geometricStructureClosure ℂ A).isClosed_iff_closure_subset _).1 hc hI
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  exact hm.elim hI0 hI1

/-- Paper 5.6 with source and target exchanged. -/
theorem not_isClosed_pair_matrixCoefficientKernel_of_span_ne_left
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x z y : H) (hx : x ≠ 0) (hz : z ≠ 0) (hy : y ≠ 0)
    (hline : Submodule.span ℂ {x} ≠ Submodule.span ℂ {z}) :
    ¬ (NormedSpace.geometricStructureClosure ℂ A).IsClosed
      {matrixCoefficientKernel pi hpi x y hx hy, matrixCoefficientKernel pi hpi z y hz hy} := by
  have hne := mt (matrixCoefficientKernel_eq_iff_span_eq_left pi hpi x z y hx hz hy).1 hline
  obtain ⟨I, hI, hI0, hI1⟩ :=
    exists_mem_closure_pair_matrixCoefficientKernel_ne_left pi hpi x z y hx hz hy hne
  intro hc
  have hm := ((NormedSpace.geometricStructureClosure ℂ A).isClosed_iff_closure_subset _).1 hc hI
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  exact hm.elim hI0 hI1

/-- Changing only the target is a Linked step, including coincident kernels. -/
theorem linked_matrixCoefficientKernel_right
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y z : H) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    (NormedSpace.geometricStructureClosure ℂ A).Linked
      (matrixCoefficientKernel pi hpi x y hx hy) (matrixCoefficientKernel pi hpi x z hx hz) := by
  by_cases hline : Submodule.span ℂ {y} = Submodule.span ℂ {z}
  · exact Or.inl ((matrixCoefficientKernel_eq_iff_span_eq_right pi hpi x y z hx hy hz).2 hline)
  · exact Or.inr (not_isClosed_pair_matrixCoefficientKernel_of_span_ne_right
      pi hpi x y z hx hy hz hline)

/-- Changing only the source is a Linked step, including coincident kernels. -/
theorem linked_matrixCoefficientKernel_left
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x z y : H) (hx : x ≠ 0) (hz : z ≠ 0) (hy : y ≠ 0) :
    (NormedSpace.geometricStructureClosure ℂ A).Linked
      (matrixCoefficientKernel pi hpi x y hx hy) (matrixCoefficientKernel pi hpi z y hz hy) := by
  by_cases hline : Submodule.span ℂ {x} = Submodule.span ℂ {z}
  · exact Or.inl ((matrixCoefficientKernel_eq_iff_span_eq_left pi hpi x z y hx hz hy).2 hline)
  · exact Or.inr (not_isClosed_pair_matrixCoefficientKernel_of_span_ne_left
      pi hpi x z y hx hz hy hline)

/-- Two nonzero coefficients in the same representation are Related through
one target change and one source change in the original closure relation. -/
theorem related_matrixCoefficientKernel
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y z w : H) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0) :
    (NormedSpace.geometricStructureClosure ℂ A).Related
      (matrixCoefficientKernel pi hpi x y hx hy) (matrixCoefficientKernel pi hpi z w hz hw) := by
  let c := NormedSpace.geometricStructureClosure ℂ A
  exact c.related_trans
    (c.related_of_linked (linked_matrixCoefficientKernel_right pi hpi x y w hx hy hw))
    (c.related_of_linked (linked_matrixCoefficientKernel_left pi hpi x z w hx hz hw))

variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The unitary-equivalent to Related direction of Paper 5.8, using actual
intertwiners. It does not assume the converse or classify equal kernels. -/
theorem related_matrixCoefficientKernel_of_unitaryEquivalent
    (pi : NonUnitalCStarRepresentation A H) (rho : NonUnitalCStarRepresentation A K)
    (hpi : pi.IsIrreducible) (hrho : rho.IsIrreducible) (heq : pi.UnitaryEquivalent rho)
    (x y : H) (z w : K) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0) :
    (NormedSpace.geometricStructureClosure ℂ A).Related
      (matrixCoefficientKernel pi hpi x y hx hy) (matrixCoefficientKernel rho hrho z w hz hw) := by
  obtain ⟨U, hU⟩ := heq
  have hxU : U x ≠ 0 := fun h => hx (U.injective (h.trans (map_zero U).symm))
  have hyU : U y ≠ 0 := fun h => hy (U.injective (h.trans (map_zero U).symm))
  have hker := matrixCoefficientKernel_eq_of_intertwines pi rho hpi hrho U hU x y hx hy
  rw [← hker]
  exact related_matrixCoefficientKernel rho hrho (U x) (U y) z w hxU hyU hz hw

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
