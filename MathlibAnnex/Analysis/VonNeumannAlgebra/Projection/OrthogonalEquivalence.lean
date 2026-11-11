/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.CentralComparison

/-!
# Equivalence of arbitrary orthogonal projection suprema

An equivalence between corresponding members of two orthogonal projection
families lifts to their projection suprema. The partial isometries are
chosen in the specified von Neumann algebra. Orthogonality of the two
endpoint families supplies both cross-product equations for the existing
strong orthogonal-sum theorem, whose net ranges over all finite subsets.
-/

set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra

namespace VonNeumannAlgebra

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Equivalence in the same von Neumann algebra is compatible with arbitrary
orthogonal projection suprema. Both endpoint families must be orthogonal.
The index universe is independent of the Hilbert-space universe, and the
index type may be empty. -/
theorem murrayVonNeumannEquivalent_iSupProjection
    (M : VonNeumannAlgebra H) {ι : Type v}
    (p q : ι → M.toStarSubalgebra)
    (hp : ∀ i, IsStarProjection (p i)) (hq : ∀ i, IsStarProjection (q i))
    (horthp : Pairwise (fun i j ↦ p i * p j = 0))
    (horthq : Pairwise (fun i j ↦ q i * q j = 0))
    (heq : ∀ i, MurrayVonNeumannEquivalent (p i) (q i)) :
    MurrayVonNeumannEquivalent (iSupProjection M p hp) (iSupProjection M q hq) := by
  classical
  let V : ι → M.toStarSubalgebra := fun i ↦ (heq i).exists_partial_isometry.choose
  have hV (i : ι) : IsPartialIsometry (V i) :=
    (heq i).exists_partial_isometry.choose_spec.1
  have hVp (i : ι) : star (V i) * V i = p i :=
    (heq i).exists_partial_isometry.choose_spec.2.1
  have hVq (i : ι) : V i * star (V i) = q i :=
    (heq i).exists_partial_isometry.choose_spec.2.2
  have hi : Pairwise (fun i j ↦ star (V i) * V j = 0) := by
    intro i j hij
    apply (hV i).star_mul_eq_zero_of_final_mul_final_eq_zero (hV j)
    rw [hVq i, hVq j]
    exact horthq hij
  have hf : Pairwise (fun i j ↦ V i * star (V j) = 0) := by
    intro i j hij
    apply (hV i).mul_star_eq_zero_of_initial_mul_initial_eq_zero (hV j)
    rw [hVp i, hVp j]
    exact horthp hij
  obtain ⟨S, hS, hSp, hSq⟩ :=
    exists_orthogonal_sum_partial_isometry_with_sup M V hV hi hf
  refine ⟨isStarProjection_iSupProjection M p hp,
    isStarProjection_iSupProjection M q hq, S, hS, ?_, ?_⟩
  · simpa only [hVp] using hSp
  · simpa only [hVq] using hSq

end VonNeumannAlgebra
