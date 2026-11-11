import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.OrthogonalSum

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

universe u v

variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- This consumer has no Countable or SeparableSpace instance. It consumes
the actual internal witness and expands the partial-isometry predicate. -/
example (M : VonNeumannAlgebra H) (V : ι → M.toStarSubalgebra)
    (hV : ∀ i, (V i) * star (V i) * V i = V i)
    (hi : Pairwise (fun i j ↦ star (V i) * V j = 0))
    (hf : Pairwise (fun i j ↦ V i * star (V j) = 0)) :
    ∃ S : M.toStarSubalgebra, S * star S * S = S ∧
      (∀ x : H, Tendsto
        (fun s : Finset ι ↦ (∑ i ∈ s, (V i : H →L[ℂ] H)) x)
        atTop (𝓝 ((S : H →L[ℂ] H) x))) ∧
      ‖(S : H →L[ℂ] H)‖ ≤ 1 := by
  obtain ⟨S, hS, hlim, _, hnorm, _, _⟩ :=
    VonNeumannAlgebra.exists_orthogonal_sum_partial_isometry M V hV hi hf
  exact ⟨S, hS, hlim, hnorm⟩

/-- Initial and final projection identities are limits over the same
finite-subset net, not over a chosen enumeration of the index set. -/
example (M : VonNeumannAlgebra H) (V : ι → M.toStarSubalgebra)
    (hV : ∀ i, IsPartialIsometry (V i))
    (hi : Pairwise (fun i j ↦ star (V i) * V j = 0))
    (hf : Pairwise (fun i j ↦ V i * star (V j) = 0)) :
    ∃ S : M.toStarSubalgebra,
      ContinuousLinearMap.StronglyConverges
        (fun s : Finset ι ↦ ∑ i ∈ s, star (V i : H →L[ℂ] H) * (V i : H →L[ℂ] H))
        atTop (star (S : H →L[ℂ] H) * (S : H →L[ℂ] H)) ∧
      ContinuousLinearMap.StronglyConverges
        (fun s : Finset ι ↦ ∑ i ∈ s, (V i : H →L[ℂ] H) * star (V i : H →L[ℂ] H))
        atTop ((S : H →L[ℂ] H) * star (S : H →L[ℂ] H)) := by
  obtain ⟨S, _, _, _, _, hInitial, hFinal⟩ :=
    VonNeumannAlgebra.exists_orthogonal_sum_partial_isometry M V hV hi hf
  exact ⟨S, hInitial, hFinal⟩

/-- The geometric version starts with orthogonality of both projection
families. The two cross-product hypotheses are proved inside the same algebra. -/
example (M : VonNeumannAlgebra H) (V : ι → M.toStarSubalgebra)
    (hV : ∀ i, IsPartialIsometry (V i))
    (hi : Pairwise (fun i j ↦
      (star (V i) * V i) * (star (V j) * V j) = 0))
    (hf : Pairwise (fun i j ↦
      (V i * star (V i)) * (V j * star (V j)) = 0)) :
    ∃ S : M.toStarSubalgebra, IsPartialIsometry S ∧
      ContinuousLinearMap.StronglyConverges
        (fun s : Finset ι ↦ ∑ i ∈ s, (V i : H →L[ℂ] H))
        atTop (S : H →L[ℂ] H) := by
  have hcrossInitial : Pairwise (fun i j ↦ star (V i) * V j = 0) := by
    intro i j hij
    exact (hV i).star_mul_eq_zero_of_final_mul_final_eq_zero (hV j) (hf hij)
  have hcrossFinal : Pairwise (fun i j ↦ V i * star (V j) = 0) := by
    intro i j hij
    exact (hV i).mul_star_eq_zero_of_initial_mul_initial_eq_zero (hV j) (hi hij)
  obtain ⟨S, hS, hlim, _, _, _, _⟩ :=
    VonNeumannAlgebra.exists_orthogonal_sum_partial_isometry
      (M := M) (V := V) hV hcrossInitial hcrossFinal
  exact ⟨S, hS, hlim⟩

example (M : VonNeumannAlgebra H) :
    ∃ S : M.toStarSubalgebra, IsPartialIsometry S ∧
      ContinuousLinearMap.StronglyConverges
        (fun s : Finset Empty ↦ ∑ i ∈ s, (0 : H →L[ℂ] H)) atTop (S : H →L[ℂ] H) := by
  obtain ⟨S, hS, hlim, _, _, _, _⟩ :=
    VonNeumannAlgebra.exists_orthogonal_sum_partial_isometry M
      (fun _ : Empty ↦ 0) (fun i ↦ i.elim) (fun i ↦ i.elim) (fun i ↦ i.elim)
  exact ⟨S, hS, hlim⟩
