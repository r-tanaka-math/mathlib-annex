import MathlibAnnex.Analysis.CStarAlgebra.FiniteInterpolation
import Mathlib.Topology.Algebra.StarSubalgebra

/-!
# Finite amplification of a bicommutant

An operator in the bicommutant of a unital star representation can be
approximated on any finite family of vectors by one element of its range.
The proof uses the existing dependent Hilbert sum and cyclic subspace.  The
orthogonal projection onto a diagonal cyclic subspace has matrix entries in
the original commutant, so it commutes with the diagonal amplification of
every operator in the bicommutant.

For a star subalgebra that is not norm closed, the representation argument
is applied to its norm closure.  A second, operator-norm approximation
returns the approximating operator to the original star subalgebra.

## Source attribution

The first two proofs adapt the projection and approximation arguments of
`StarAlgHom.diagonal_apply_mem_cyclicSubspace_of_irreducible` and
`StarAlgHom.exists_atomic_apply_sub_norm_lt_of_irreducible` in
`MathlibAnnex/Analysis/CStarAlgebra/FiniteInterpolation.lean`, from
`r-tanaka-math/mathlib-annex` at commit
`5cbbf304e651c6c50163a59ba7f9fcf6c22eca4e` (Apache-2.0).
The irreducibility and Schur steps are replaced by the double-commutant
argument for the projection blocks. The third proof transfers approximation
from the norm closure back to the original star subalgebra.
-/

set_option autoImplicit false

open scoped BigOperators ENNReal lp

open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.Analysis.InnerProductSpace

namespace StarAlgHom

variable {A H : Type*} [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Finite diagonal amplification preserves the cyclic subspace of a
vector whenever the original operator belongs to the bicommutant of the
representation. -/
theorem diagonal_apply_mem_cyclicSubspace_of_mem_bicommutant
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (Set.range π)))
    {I : Type*} [Fintype I] [DecidableEq I] (ξ : I → H) :
    diagonal (fun _ : I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
        (finiteHilbertSum ξ) ∈
      cyclicSubspace (atomicRepresentation (fun _ : I => π))
        (finiteHilbertSum ξ) := by
  classical
  let ρ := atomicRepresentation (fun _ : I => π)
  let x : HilbertSum (fun _ : I => H) := finiteHilbertSum ξ
  let D : HilbertSum (fun _ : I => H) →L[ℂ]
      HilbertSum (fun _ : I => H) :=
    diagonal (fun _ : I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
  let M : Submodule ℂ (HilbertSum (fun _ : I => H)) := cyclicSubspace ρ x
  letI : IsClosed (M : Set (HilbertSum (fun _ : I => H))) :=
    isClosed_cyclicSubspace ρ x
  letI : M.HasOrthogonalProjection := inferInstance
  let P : HilbertSum (fun _ : I => H) →L[ℂ]
      HilbertSum (fun _ : I => H) := M.starProjection
  have hPcomm : InCommutant ρ P := by
    intro a
    change P.comp (ρ a) = (ρ a).comp P
    exact Submodule.Reduces.starProjection_commute
      (isReducing_cyclicSubspace ρ x a)
  have hblocks (i j : I) :
      atomicBlock P i j ∈ Set.centralizer (Set.range π) := by
    rintro _ ⟨a, rfl⟩
    change (π a).comp (atomicBlock P i j) =
      (atomicBlock P i j).comp (π a)
    rcases subsingleton_or_nontrivial H with h | h
    · exact Subsingleton.elim _ _
    · exact (intertwines_atomicBlock_of_inCommutant
        (fun _ : I => π) P hPcomm i j a).symm
  have hsum (y : HilbertSum (fun _ : I => H)) :
      y = ∑ i : I, coordinateEmbedding i (y i) := by
    have hyhas : HasSum (fun i : I => coordinateEmbedding i (y i)) y := by
      simpa [coordinateEmbedding_apply] using
        (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) y)
    exact hyhas.unique (hasSum_fintype _)
  have hblocksum (y : HilbertSum (fun _ : I => H)) (j : I) :
      P y j = ∑ i : I, atomicBlock P i j (y i) := by
    calc
      P y j = P (∑ i : I, coordinateEmbedding i (y i)) j :=
        congrArg (fun z => P z j) (hsum y)
      _ = ∑ i : I, atomicBlock P i j (y i) := by
        rw [map_sum]
        change coordinateProjection j
          (∑ i : I, P (coordinateEmbedding i (y i))) =
            ∑ i : I, coordinateProjection j (P (coordinateEmbedding i (y i)))
        exact map_sum (coordinateProjection j)
          (fun i : I => P (coordinateEmbedding i (y i))) Finset.univ
  have hPD (y : HilbertSum (fun _ : I => H)) : P (D y) = D (P y) := by
    apply lp.ext
    funext j
    calc
      P (D y) j = ∑ i : I, atomicBlock P i j (D y i) := hblocksum (D y) j
      _ = ∑ i : I, T (atomicBlock P i j (y i)) := by
        apply Finset.sum_congr rfl
        intro i _
        have hij := congrArg (fun Q : H →L[ℂ] H => Q (y i))
          (hT (atomicBlock P i j) (hblocks i j))
        change atomicBlock P i j (T (y i)) = T (atomicBlock P i j (y i)) at hij
        exact hij
      _ = T (∑ i : I, atomicBlock P i j (y i)) :=
        (map_sum T (fun i : I => atomicBlock P i j (y i)) Finset.univ).symm
      _ = T (P y j) := congrArg T (hblocksum y j).symm
      _ = D (P y) j := rfl
  have hxmem : x ∈ M := by
    simpa [M] using orbit_mem_cyclicSubspace ρ x (1 : A)
  have hPx : P x = x := M.starProjection_eq_self_iff.mpr hxmem
  have hDx : P (D x) = D x := by rw [hPD, hPx]
  exact M.starProjection_eq_self_iff.mp hDx

/-- A bounded operator in a represented bicommutant can be approximated
simultaneously on a finite family of vectors by a single algebra element. -/
theorem exists_forall_apply_sub_norm_lt_of_mem_bicommutant
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (Set.range π)))
    {I : Type*} [Fintype I] [DecidableEq I] (ξ : I → H)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, ∀ i, ‖π a (ξ i) - T (ξ i)‖ < ε := by
  let ρ := atomicRepresentation (fun _ : I => π)
  let x : HilbertSum (fun _ : I => H) := finiteHilbertSum ξ
  let D : HilbertSum (fun _ : I => H) →L[ℂ]
      HilbertSum (fun _ : I => H) :=
    diagonal (fun _ : I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
  have hmem : D x ∈ cyclicSubspace ρ x :=
    diagonal_apply_mem_cyclicSubspace_of_mem_bicommutant π hT ξ
  change D x ∈ closure (LinearMap.range (orbitMap ρ x)) at hmem
  obtain ⟨y, ⟨a, rfl⟩, ha⟩ := Metric.mem_closure_iff.mp hmem ε hε
  have hnorm : ‖ρ a x - D x‖ < ε := by
    rw [dist_eq_norm] at ha
    simpa [orbitMap, norm_sub_rev] using ha
  refine ⟨a, fun i => ?_⟩
  have hcoord := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (ρ a x - D x) i
  have hle : ‖π a (ξ i) - T (ξ i)‖ ≤ ‖ρ a x - D x‖ := by
    simpa [ρ, x, D] using hcoord
  exact hle.trans_lt hnorm

end StarAlgHom

namespace StarSubalgebra

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every operator in the bicommutant of a unital star subalgebra admits
simultaneous approximation on any finite family of vectors by an element
of that subalgebra.  No norm-closedness assumption is imposed on the
subalgebra. -/
theorem exists_forall_apply_sub_norm_lt_of_mem_bicommutant
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    {I : Type*} [Fintype I] [DecidableEq I] (ξ : I → H)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ S, ∀ i, ‖a (ξ i) - T (ξ i)‖ < ε := by
  classical
  let R : StarSubalgebra ℂ (H →L[ℂ] H) := S.topologicalClosure
  letI : IsClosed (R : Set (H →L[ℂ] H)) := S.isClosed_topologicalClosure
  let π : R →⋆ₐ[ℂ] (H →L[ℂ] H) := R.subtype
  have hT' : T ∈ Set.centralizer (Set.centralizer (Set.range π)) := by
    intro Q hQ
    apply hT Q
    intro b hb
    exact hQ b ⟨⟨b, S.le_topologicalClosure hb⟩, rfl⟩
  obtain ⟨a, ha⟩ := StarAlgHom.exists_forall_apply_sub_norm_lt_of_mem_bicommutant
    π hT' ξ (half_pos hε)
  let C : ℝ := ∑ i : I, ‖ξ i‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => norm_nonneg (ξ i)
  have hCpos : 0 < C + 1 := by positivity
  have hξ (i : I) : ‖ξ i‖ ≤ C :=
    Finset.single_le_sum (fun j _ => norm_nonneg (ξ j)) (Finset.mem_univ i)
  have haClosure : (a : H →L[ℂ] H) ∈ closure (S : Set (H →L[ℂ] H)) :=
    a.property
  obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.mp haClosure
    ((ε / 2) / (C + 1)) (div_pos (half_pos hε) hCpos)
  have hba : ‖b - (a : H →L[ℂ] H)‖ < (ε / 2) / (C + 1) := by
    simpa only [dist_eq_norm, norm_sub_rev] using hdist
  have hprod : ‖b - (a : H →L[ℂ] H)‖ * (C + 1) < ε / 2 :=
    (lt_div_iff₀ hCpos).mp hba
  refine ⟨b, hb, fun i => ?_⟩
  have hξ' : ‖ξ i‖ ≤ C + 1 :=
    (hξ i).trans (le_add_of_nonneg_right zero_le_one)
  have heval : ‖b (ξ i) - (a : H →L[ℂ] H) (ξ i)‖ < ε / 2 := by
    calc
      ‖b (ξ i) - (a : H →L[ℂ] H) (ξ i)‖ =
          ‖(b - (a : H →L[ℂ] H)) (ξ i)‖ := rfl
      _ ≤ ‖b - (a : H →L[ℂ] H)‖ * ‖ξ i‖ :=
        (b - (a : H →L[ℂ] H)).le_opNorm (ξ i)
      _ ≤ ‖b - (a : H →L[ℂ] H)‖ * (C + 1) :=
        mul_le_mul_of_nonneg_left hξ' (norm_nonneg _)
      _ < ε / 2 := hprod
  calc
    ‖b (ξ i) - T (ξ i)‖ ≤
        ‖b (ξ i) - (a : H →L[ℂ] H) (ξ i)‖ +
          ‖(a : H →L[ℂ] H) (ξ i) - T (ξ i)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add heval (ha i)
    _ = ε := add_halves ε

end StarSubalgebra
