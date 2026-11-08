import MathlibAnnex.Analysis.VonNeumannAlgebra.Generated

/-! # Direct consumers of the generated-algebra module -/

set_option autoImplicit false

open Filter Topology

namespace VonNeumannAlgebraExamples

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem generated_carrier (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (VonNeumannAlgebra.generated S : Set (H →L[ℂ] H)) =
      Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) :=
  VonNeumannAlgebra.coe_generated S

theorem generated_is_idempotent (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    VonNeumannAlgebra.generated (VonNeumannAlgebra.generated S).toStarSubalgebra =
      VonNeumannAlgebra.generated S :=
  VonNeumannAlgebra.generated_toStarSubalgebra _

theorem generated_is_least (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (M : VonNeumannAlgebra H) (hSM : S ≤ M.toStarSubalgebra) :
    VonNeumannAlgebra.generated S ≤ M :=
  VonNeumannAlgebra.generated_le S M hSM

theorem subtype_has_cstar_algebra (M : VonNeumannAlgebra H) :
    Nonempty (CStarAlgebra M.toStarSubalgebra) :=
  ⟨inferInstance⟩

theorem subtype_is_complete (M : VonNeumannAlgebra H) :
    CompleteSpace M.toStarSubalgebra :=
  inferInstance

theorem strongly_convergent_members (M : VonNeumannAlgebra H)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → H →L[ℂ] H} {T : H →L[ℂ] H}
    (hf : ∀ i, f i ∈ M) (hT : ContinuousLinearMap.StronglyConverges f l T) :
    T ∈ M :=
  M.mem_of_stronglyConverges hf hT

theorem strongly_convergent_commuting_operators (S : Set (H →L[ℂ] H))
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → H →L[ℂ] H} {T : H →L[ℂ] H}
    (hf : ∀ i, f i ∈ Set.centralizer S)
    (hT : ContinuousLinearMap.StronglyConverges f l T) :
    T ∈ Set.centralizer S := by
  have hmem : ContinuousLinearMapWOT.ofCLM T ∈
      ContinuousLinearMapWOT.ofCLM '' Set.centralizer S :=
    (ContinuousLinearMapWOT.isClosed_image_centralizer S).mem_of_tendsto
      hT.tendsto_wot (Eventually.of_forall fun i ↦ ⟨f i, hf i, rfl⟩)
  obtain ⟨Q, hQ, hQT⟩ := hmem
  exact (ContinuousLinearMapWOT.ofCLM_injective hQT) ▸ hQ

end VonNeumannAlgebraExamples
