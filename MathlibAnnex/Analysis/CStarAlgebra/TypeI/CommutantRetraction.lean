import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.CARAverage
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.PositiveBimodule
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.PositiveRetraction
import MathlibAnnex.Analysis.VonNeumannAlgebra.Generated

/-!
# A positive bimodule retraction onto a represented CAR commutant

The finite matrix averages act on all bounded operators. Compactness of
positive unital maps in the product WOT topology supplies an actual cluster
point. Eventual commutation with each matrix stage, followed by norm density
of the CAR stages, puts its values in the full commutant. Every finite average
fixes that commutant and is bimodular over it, so the cluster point has the
same two properties.

There is no separability premise on the Hilbert space, and no normality
premise or conclusion for the retraction. The representation is arbitrary;
this construction does not assert that its commutant is type III.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped CStarAlgebra ComplexOrder
open MathlibAnnex.Analysis.CStarAlgebra

namespace MathlibAnnex.CStarAlgebra.CAR

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem mem_generated_commutant_iff
    (rho : Limit →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : H →L[ℂ] H) :
    S ∈ (VonNeumannAlgebra.generated rho.range).commutant ↔
      ∀ a : Limit, rho a * S = S * rho a := by
  rw [← SetLike.mem_coe, VonNeumannAlgebra.coe_commutant,
    VonNeumannAlgebra.coe_generated, Set.centralizer_centralizer_centralizer]
  constructor
  · intro h a
    exact h (rho a) ⟨a, rfl⟩
  · intro h T hT
    rcases hT with ⟨a, rfl⟩
    exact h a

/-- A genuine positive unital retraction from all bounded operators onto
the commutant, with the full two-sided bimodule identity. -/
theorem exists_positive_bimodule_retraction
    (rho : Limit →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    ∃ E : (H →L[ℂ] H) →P[ℂ]
        (VonNeumannAlgebra.generated rho.range).commutant.toStarSubalgebra,
      E 1 = 1 ∧
      (∀ S : (VonNeumannAlgebra.generated rho.range).commutant.toStarSubalgebra,
        E (S : H →L[ℂ] H) = S) ∧
      ∀ (S T : (VonNeumannAlgebra.generated rho.range).commutant.toStarSubalgebra)
        (b : H →L[ℂ] H),
        E ((S : H →L[ℂ] H) * b * (T : H →L[ℂ] H)) = S * E b * T := by
  obtain ⟨f, hf, hcluster⟩ := exists_mapClusterPt_positiveUnitalMapSet
    (Filter.atTop : Filter ℕ) (representedRowAverage rho) (representedRowAverage_one rho)
  have hstage (n : ℕ) (c : Stage n) (b : H →L[ℂ] H) :
      rho (ofStage n c) * (f b).toCLM = (f b).toCLM * rho (ofStage n c) := by
    have hclosed : IsClosed {g : (H →L[ℂ] H) → (H →WOT[ℂ] H) |
        ContinuousLinearMapWOT.ofCLM (rho (ofStage n c)) * g b =
          g b * ContinuousLinearMapWOT.ofCLM (rho (ofStage n c))} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    have hmem := hclosed.mem_of_mapClusterPt hcluster
      (Filter.eventually_atTop.2 ⟨n, fun m hm =>
        congrArg ContinuousLinearMapWOT.ofCLM
          (ofStage_commute_representedRowAverage_of_le rho hm c b)⟩)
    exact congrArg ContinuousLinearMapWOT.toCLM hmem
  have hcomm (b : H →L[ℂ] H) (a : Limit) :
      rho a * (f b).toCLM = (f b).toCLM * rho a := by
    have hclosed : IsClosed {c : Limit | rho c * (f b).toCLM = (f b).toCLM * rho c} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    have hsubset : (⋃ n : ℕ, Set.range (ofStage n)) ⊆
        {c : Limit | rho c * (f b).toCLM = (f b).toCLM * rho c} := by
      intro c hc
      rcases Set.mem_iUnion.mp hc with ⟨n, d, rfl⟩
      exact hstage n d b
    apply closure_minimal hsubset hclosed
    rw [dense_stageRange.closure_eq]
    exact Set.mem_univ a
  let M := (VonNeumannAlgebra.generated rho.range).commutant
  have hfix (S : M.toStarSubalgebra) :
      f (S : H →L[ℂ] H) = ContinuousLinearMapWOT.ofCLM (S : H →L[ℂ] H) := by
    have hclosed : IsClosed {g : (H →L[ℂ] H) → (H →WOT[ℂ] H) |
        g (S : H →L[ℂ] H) = ContinuousLinearMapWOT.ofCLM (S : H →L[ℂ] H)} :=
      isClosed_eq (continuous_apply _) continuous_const
    apply hclosed.mem_of_mapClusterPt hcluster
    apply Filter.Eventually.of_forall
    intro n
    exact congrArg ContinuousLinearMapWOT.ofCLM
      (representedRowAverage_eq_self rho n (S : H →L[ℂ] H)
        ((mem_generated_commutant_iff rho _).mp S.property))
  have hbi (S T : M.toStarSubalgebra) (b : H →L[ℂ] H) :
      f ((S : H →L[ℂ] H) * b * (T : H →L[ℂ] H)) =
        ContinuousLinearMapWOT.ofCLM (S : H →L[ℂ] H) * f b *
          ContinuousLinearMapWOT.ofCLM (T : H →L[ℂ] H) := by
    have hclosed : IsClosed {g : (H →L[ℂ] H) → (H →WOT[ℂ] H) |
        g ((S : H →L[ℂ] H) * b * (T : H →L[ℂ] H)) =
          ContinuousLinearMapWOT.ofCLM (S : H →L[ℂ] H) * g b *
            ContinuousLinearMapWOT.ofCLM (T : H →L[ℂ] H)} :=
      isClosed_eq (continuous_apply _) (by fun_prop)
    apply hclosed.mem_of_mapClusterPt hcluster
    apply Filter.Eventually.of_forall
    intro n
    exact congrArg ContinuousLinearMapWOT.ofCLM
      (representedRowAverage_mul_mul rho n (S : H →L[ℂ] H) (T : H →L[ℂ] H) b
        ((mem_generated_commutant_iff rho _).mp S.property)
        ((mem_generated_commutant_iff rho _).mp T.property))
  let sigma : M.toStarSubalgebra →⋆ₐ[ℂ] M.toStarSubalgebra :=
    StarAlgHom.id ℂ M.toStarSubalgebra
  have hfamily : f ∈ positiveBimoduleExtensionSet M.toStarSubalgebra M sigma :=
    ⟨hf, fun b => (mem_generated_commutant_iff rho _).mpr (hcomm b), hfix, hbi⟩
  refine ⟨positiveBimoduleExtensionOfMem M.toStarSubalgebra M sigma f hfamily, ?_, ?_, ?_⟩
  · exact positiveBimoduleExtensionOfMem_one _ _ _ _ _
  · intro S
    exact positiveBimoduleExtensionOfMem_restrict _ _ _ _ _ S
  · intro S T b
    exact positiveBimoduleExtensionOfMem_mul_mul _ _ _ _ _ S T b

/-- Choose the retraction whose existence was proved using finite matrix
averages. No extra class or witness assumption is introduced. -/
def commutantRetraction (rho : Limit →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    (H →L[ℂ] H) →P[ℂ]
      (VonNeumannAlgebra.generated rho.range).commutant.toStarSubalgebra :=
  (exists_positive_bimodule_retraction rho).choose

@[simp]
theorem commutantRetraction_one (rho : Limit →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    commutantRetraction rho 1 = 1 :=
  (exists_positive_bimodule_retraction rho).choose_spec.1

@[simp]
theorem commutantRetraction_restrict (rho : Limit →⋆ₐ[ℂ] (H →L[ℂ] H))
    (S : (VonNeumannAlgebra.generated rho.range).commutant.toStarSubalgebra) :
    commutantRetraction rho (S : H →L[ℂ] H) = S :=
  (exists_positive_bimodule_retraction rho).choose_spec.2.1 S

theorem commutantRetraction_mul_mul (rho : Limit →⋆ₐ[ℂ] (H →L[ℂ] H))
    (S T : (VonNeumannAlgebra.generated rho.range).commutant.toStarSubalgebra)
    (b : H →L[ℂ] H) :
    commutantRetraction rho ((S : H →L[ℂ] H) * b * (T : H →L[ℂ] H)) =
      S * commutantRetraction rho b * T :=
  (exists_positive_bimodule_retraction rho).choose_spec.2.2 S T b

/-- The ambient operator obtained from the retraction is fixed on applying
the retraction again. -/
@[simp]
theorem commutantRetraction_idempotent (rho : Limit →⋆ₐ[ℂ] (H →L[ℂ] H))
    (b : H →L[ℂ] H) :
    commutantRetraction rho (commutantRetraction rho b : H →L[ℂ] H) =
      commutantRetraction rho b :=
  commutantRetraction_restrict rho _

/-- The constructed retraction satisfies Schwarz; this estimate is proved,
not included in the compactness family as an extra premise. -/
theorem star_mul_commutantRetraction_le (rho : Limit →⋆ₐ[ℂ] (H →L[ℂ] H))
    (b : H →L[ℂ] H) :
    star (commutantRetraction rho b) * commutantRetraction rho b ≤
      commutantRetraction rho (star b * b) :=
  star_mul_le_of_positive_bimodule_retraction
    (VonNeumannAlgebra.generated rho.range).commutant.toStarSubalgebra
    (commutantRetraction rho) (commutantRetraction_restrict rho)
    (commutantRetraction_mul_mul rho) b

/-- The retraction is contractive in the original operator/subalgebra norms. -/
theorem norm_commutantRetraction_le (rho : Limit →⋆ₐ[ℂ] (H →L[ℂ] H))
    (b : H →L[ℂ] H) : ‖commutantRetraction rho b‖ ≤ ‖b‖ :=
  norm_le_of_positive_bimodule_retraction
    (VonNeumannAlgebra.generated rho.range).commutant.toStarSubalgebra
    (commutantRetraction rho) (commutantRetraction_restrict rho)
    (commutantRetraction_mul_mul rho) b

end MathlibAnnex.CStarAlgebra.CAR
