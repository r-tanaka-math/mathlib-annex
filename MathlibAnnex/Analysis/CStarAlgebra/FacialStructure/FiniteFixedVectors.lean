/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.SimultaneousClipping
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Self-adjoint contractions fixing finite-dimensional subspaces

The interpolation is performed in the original nonunital algebra, using the
singleton case of sharp simultaneous interpolation. A rank-two lower bound
on the Hilbert space produces an element whose represented operator has
range dimension at least two and a nonzero diagonal coefficient. Neither
finite rank, positivity, nor idempotence of that element is asserted.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The identity on a finite-dimensional subspace is realized by a self-adjoint
contraction of the original algebra. The subspace may be zero. -/
theorem exists_selfAdjoint_norm_le_one_forall_eq_self
    (pi : NonUnitalCStarRepresentation A H) (hirr : pi.IsIrreducible)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E] :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 1 ∧ ∀ x ∈ E, pi a x = x := by
  classical
  obtain ⟨a, ha, hn, he⟩ := exists_selfAdjoint_norm_le_forall_eq_on
    (I := Unit) (H := fun _ : Unit => H) (fun _ => pi) (fun _ => hirr)
    (fun i j hij => (hij (Subsingleton.elim i j)).elim)
    (fun _ => E) (fun _ => (1 : H →L[ℂ] H))
    (fun _ => by simp only [IsSelfAdjoint, star_one])
    1 (by norm_num) (fun _ => ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun z => by simp))
  exact ⟨a, ha, hn, fun x hx => by simpa using he () x hx⟩

/-- A rank-two witness with two fixed independent vectors and a nonzero diagonal.
The rank appearing in the conclusion belongs to the actual represented operator. -/
theorem exists_selfAdjoint_norm_le_one_two_le_rank_range
    (pi : NonUnitalCStarRepresentation A H) (hirr : pi.IsIrreducible)
    (hdim : 2 ≤ Module.rank ℂ H) :
    ∃ (a : A) (x y : H), IsSelfAdjoint a ∧ ‖a‖ ≤ 1 ∧
      LinearIndependent ℂ ![x, y] ∧ pi a x = x ∧ pi a y = y ∧
      2 ≤ Module.rank ℂ (pi a).range ∧ x ≠ 0 ∧
      inner ℂ x (pi a x) ≠ 0 := by
  classical
  have hbig : 1 < Module.rank ℂ H := Cardinal.two_le_iff_one_lt.mp hdim
  obtain ⟨x, hx⟩ : ∃ x : H, x ≠ 0 := by
    by_contra h
    push_neg at h
    have hs : Module.rank ℂ H ≤ 1 := rank_le_one_iff.mpr
      ⟨0, fun z => ⟨0, by simpa only [zero_smul] using (h z).symm⟩⟩
    exact (not_le_of_gt hbig) hs
  obtain ⟨y, hy⟩ : ∃ y : H, y ∉ Submodule.span ℂ {x} := by
    by_contra h
    push_neg at h
    have hs : Module.rank ℂ H ≤ 1 := rank_le_one_iff.mpr
      ⟨x, fun z => Submodule.mem_span_singleton.mp (h z)⟩
    exact (not_le_of_gt hbig) hs
  have hxy : LinearIndependent ℂ ![x, y] := by
    apply (LinearIndependent.pair_iff' hx).mpr
    intro c hc
    apply hy
    rw [← hc]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self x)
  let E : Submodule ℂ H := Submodule.span ℂ {x, y}
  letI : FiniteDimensional ℂ E :=
    FiniteDimensional.span_of_finite ℂ (Set.toFinite {x, y})
  obtain ⟨a, ha, han, hfix⟩ := exists_selfAdjoint_norm_le_one_forall_eq_self pi hirr E
  have hax : pi a x = x := hfix x (Submodule.subset_span (by simp))
  have hay : pi a y = y := hfix y (Submodule.subset_span (by simp))
  have hrank : 2 ≤ Module.rank ℂ (pi a).range := by
    apply Cardinal.two_le_iff_one_lt.mpr
    by_contra h
    have hs : Module.rank ℂ (pi a).range ≤ 1 := le_of_not_gt h
    obtain ⟨v, hv⟩ := (rank_submodule_le_one_iff' (pi a).range).mp hs
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hv ⟨x, hax⟩)
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp (hv ⟨y, hay⟩)
    have hc0 : c ≠ 0 := by
      intro h0
      exact hx (by simpa only [h0, zero_smul] using hc.symm)
    apply hy
    have hy' : (d * c⁻¹) • x = y := by
      rw [← hc, smul_smul]
      calc
        ((d * c⁻¹) * c) • v = d • v := by rw [mul_assoc, inv_mul_cancel₀ hc0, mul_one]
        _ = y := hd
    rw [← hy']
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  exact ⟨a, x, y, ha, han, hxy, hax, hay, hrank, hx,
    by rw [hax]; exact inner_self_ne_zero.mpr hx⟩

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
