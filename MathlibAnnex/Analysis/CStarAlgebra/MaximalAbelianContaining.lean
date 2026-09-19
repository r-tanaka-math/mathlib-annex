import MathlibAnnex.Analysis.CStarAlgebra.MaximalAbelian

/-!
# Maximal abelian subalgebras containing a prescribed normal element
-/

set_option autoImplicit false

open Set

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u

variable {A : Type u} [CStarAlgebra A]

/-- Every star-normal element of a unital C-star algebra belongs to a maximal
abelian star subalgebra. -/
theorem exists_maximalAbelian_containing (x : A) [IsStarNormal x] :
    ∃ D : StarSubalgebra ℂ A, IsMaximalAbelian D ∧ x ∈ D := by
  let E : StarSubalgebra ℂ A := StarAlgebra.elemental ℂ x
  let S : Set (StarSubalgebra ℂ A) :=
    {D | IsMulCommutative D ∧ E ≤ D}
  have hE : E ∈ S := by
    refine ⟨inferInstance, le_rfl⟩
  obtain ⟨D, _hED, hD, hmax⟩ :=
    zorn_le_nonempty₀ S (fun c hcS hc y hy => by
      letI : Nonempty c := ⟨⟨y, hy⟩⟩
      let F : c → StarSubalgebra ℂ A := fun d => d.1
      have hdir : Directed (· ≤ ·) F := by
        intro i j
        by_cases hij' : i = j
        · subst j
          exact ⟨i, le_rfl, le_rfl⟩
        have hcoe : (i.1 : StarSubalgebra ℂ A) ≠ j.1 :=
          fun h => hij' (Subtype.ext h)
        rcases hc i.2 j.2 hcoe with hij | hji
        · exact ⟨j, hij, le_rfl⟩
        · exact ⟨i, le_rfl, hji⟩
      letI (d : c) : IsMulCommutative (F d) := (hcS d.2).1
      refine ⟨⨆ d : c, F d, ?_, ?_⟩
      · refine ⟨StarSubalgebra.isMulCommutative_iSup hdir, ?_⟩
        exact (hcS hy).2.trans (le_iSup F ⟨y, hy⟩)
      · intro z hz
        exact le_iSup F ⟨z, hz⟩)
      E hE
  refine ⟨D, ?_, ?_⟩
  · refine ⟨hD.1, ?_⟩
    intro F hF hDF
    exact hmax ⟨hF, hD.2.trans hDF⟩ hDF
  · exact hD.2 (StarAlgebra.elemental.self_mem ℂ x)

/-- Self-adjoint elements satisfy the normality hypothesis of
`exists_maximalAbelian_containing`. -/
theorem exists_maximalAbelian_containing_isSelfAdjoint
    (x : A) (hx : IsSelfAdjoint x) :
    ∃ D : StarSubalgebra ℂ A, IsMaximalAbelian D ∧ x ∈ D := by
  letI : IsStarNormal x := hx.isStarNormal
  exact exists_maximalAbelian_containing x

end MathlibAnnex.Analysis.CStarAlgebra
