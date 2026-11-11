import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.CentralComparison

set_option autoImplicit false
noncomputable section

open VonNeumannAlgebra
open scoped CStarAlgebra

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Orthogonal strong summation gives an actual equivalence of the two
projection suprema; the index universe is arbitrary. -/
example (M : VonNeumannAlgebra H) {ι : Type v}
    (V : ι → M.toStarSubalgebra) (hV : ∀ i, IsPartialIsometry (V i))
    (hi : Pairwise (fun i j ↦ star (V i) * V j = 0))
    (hf : Pairwise (fun i j ↦ V i * star (V j) = 0)) :
    MurrayVonNeumannEquivalent
      (iSupProjection M (fun i ↦ star (V i) * V i)
        (fun i ↦ (hV i).isStarProjection_star_mul_self))
      (iSupProjection M (fun i ↦ V i * star (V i))
        (fun i ↦ (hV i).isStarProjection_mul_star_self)) := by
  obtain ⟨S, hS, hI, hF⟩ :=
    exists_orthogonal_sum_partial_isometry_with_sup M V hV hi hf
  exact ⟨isStarProjection_iSupProjection M _ _, isStarProjection_iSupProjection M _ _, S, hS, hI, hF⟩

/-- The central comparison theorem yields two witnesses inside M for the
opposite subequivalences on its two central parts. -/
example (M : VonNeumannAlgebra H) (p q : M.toStarSubalgebra)
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ∃ z v w : M.toStarSubalgebra,
      IsStarProjection z ∧ (∀ a : M.toStarSubalgebra, a * z = z * a) ∧
      v * star v * v = v ∧ w * star w * w = w ∧
      star v * v = p * z ∧ v * star v ≤ q * z ∧
      star w * w = q * (1 - z) ∧ w * star w ≤ p * (1 - z) := by
  obtain ⟨z, hz, hc, hleft, hright⟩ := exists_central_projection_comparison M hp hq
  obtain ⟨r, hpr, hr⟩ := hleft.exists_le
  obtain ⟨s, hqs, hs⟩ := hright.exists_le
  obtain ⟨v, hv, hvi, hvf⟩ := hpr.2.2
  obtain ⟨w, hw, hwi, hwf⟩ := hqs.2.2
  refine ⟨z, v, w, hz, hc, hv, hw, hvi, ?_, hwi, ?_⟩
  · rw [hvf]
    exact hr
  · rw [hwf]
    exact hs

/-- The maximal matching has centrally disjoint residual projections,
without any factor or separability hypothesis. -/
example (M : VonNeumannAlgebra H) (p q : M.toStarSubalgebra)
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ∃ S : M.toStarSubalgebra, S * star S * S = S ∧
      star S * S ≤ p ∧ S * star S ≤ q ∧
      centralSupport M (p - star S * S) * centralSupport M (q - S * star S) = 0 := by
  exact exists_partial_isometry_with_centrally_orthogonal_remainders M hp hq

/-- Zero endpoints are admitted and do not introduce a nontriviality
assumption on the algebra or its central parts. -/
example (M : VonNeumannAlgebra H) (q : M.toStarSubalgebra)
    (hq : IsStarProjection q) :
    ∃ z : M.toStarSubalgebra, IsStarProjection z ∧
      (∀ a : M.toStarSubalgebra, a * z = z * a) ∧
      MurrayVonNeumannSubequivalent 0 (q * z) ∧
      MurrayVonNeumannSubequivalent (q * (1 - z)) 0 := by
  simpa only [zero_mul] using
    exists_central_projection_comparison M (IsStarProjection.zero M.toStarSubalgebra) hq
