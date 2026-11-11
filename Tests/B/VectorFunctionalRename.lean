/-
New typed consumers; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.ExtremalExtension

set_option autoImplicit false
noncomputable section

open Set
open MathlibAnnex.Analysis.CStarAlgebra
open scoped CStarAlgebra InnerProduct

universe u v
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- The renamed image permits the zero vector. It has not silently acquired
-- a unit-vector condition in order to make every image a state.
example (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra)
    (hne : (positiveBimoduleExtensionSet D M sigma).Nonempty) :
    positiveBimoduleVectorFunctionalSet D M sigma (0 : H) = {0} := by
  ext phi
  constructor
  · rintro ⟨f, _hf, rfl⟩
    apply Set.mem_singleton_iff.mpr
    funext a
    simp only [vectorEvaluation_apply, inner_zero_left, Pi.zero_apply]
  · intro hphi
    obtain ⟨f, hf⟩ := hne
    refine ⟨f, hf, ?_⟩
    rw [Set.mem_singleton_iff] at hphi
    rw [hphi]
    funext a
    simp only [vectorEvaluation_apply, inner_zero_left, Pi.zero_apply]

example : (0 : A →L[ℂ] ℂ) ∉ stateSpace A := by
  intro h
  exact zero_ne_one (by simpa only [ContinuousLinearMap.zero_apply] using h.2)

-- Normalization is consumed only where a state is actually asserted.
example (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra) (xi : H) (hxi : ‖xi‖ = 1)
    {phi : A → ℂ} (hphi : phi ∈ positiveBimoduleVectorFunctionalSet D M sigma xi) :
    ∃ psi : A →L[ℂ] ℂ, psi ∈ stateSpace A ∧ (psi : A → ℂ) = phi := by
  exact exists_state_of_mem_positiveBimoduleVectorFunctionalSet D M sigma xi hxi hphi

example (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra) (xi : H) :
    IsCompact (positiveBimoduleVectorFunctionalSet D M sigma xi) := by
  exact isCompact_positiveBimoduleVectorFunctionalSet D M sigma xi

example (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra) (xi : H) :
    Convex ℝ (positiveBimoduleVectorFunctionalSet D M sigma xi) := by
  exact convex_positiveBimoduleVectorFunctionalSet D M sigma xi

example (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra) (xi : H)
    (hne : (positiveBimoduleExtensionSet D M sigma).Nonempty) :
    ((positiveBimoduleVectorFunctionalSet D M sigma xi).extremePoints ℝ).Nonempty := by
  exact extremePoints_positiveBimoduleVectorFunctionalSet_nonempty D M sigma xi hne
