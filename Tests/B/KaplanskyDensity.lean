import MathlibAnnex.Analysis.VonNeumannAlgebra.KaplanskyDensity

set_option autoImplicit false

open Set

section

variable {A H I : Type*} [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype I] [DecidableEq I]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : I → H) (T : H →L[ℂ] H)
variable (hTmem : T ∈ Set.centralizer (Set.centralizer (Set.range π)))
variable (hT : IsSelfAdjoint T) {ε : ℝ} (hε : 0 < ε)

example : ∃ a : A, IsSelfAdjoint a ∧ ∀ i, ‖π a (ξ i) - T (ξ i)‖ < ε :=
  π.exists_selfAdjoint_forall_apply_sub_norm_lt_of_mem_bicommutant ξ T hTmem hT hε

example (hTnorm : ‖T‖ < 1) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 1 ∧ ∀ i, ‖π a (ξ i) - T (ξ i)‖ < ε :=
  π.exists_selfAdjoint_norm_le_one_forall_apply_sub_norm_lt_of_mem_bicommutant_of_norm_lt_one
    ξ T hTmem hT hTnorm hε

example (hTnorm : ‖T‖ ≤ 1) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 1 ∧ ∀ i, ‖π a (ξ i) - T (ξ i)‖ < ε :=
  π.exists_selfAdjoint_norm_le_one_forall_apply_sub_norm_lt_of_mem_bicommutant
    ξ T hTmem hT hTnorm hε

example : ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
    ∀ i, ‖π a (ξ i) - T (ξ i)‖ < ε :=
  π.exists_selfAdjoint_norm_le_forall_apply_sub_norm_lt_of_mem_bicommutant ξ T hTmem hT hε

example :
    ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H T ∈
      closure ((fun a : A =>
        ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (π a)) ''
          Metric.closedBall (0 : A) ‖T‖) :=
  π.mem_sotClosure_image_closedBall_of_isSelfAdjoint T hTmem hT

example : ContinuousLinearMapWOT.ofCLM T ∈
    closure ((fun a : A => ContinuousLinearMapWOT.ofCLM (π a)) ''
      Metric.closedBall (0 : A) ‖T‖) :=
  π.mem_wotClosure_image_closedBall_of_isSelfAdjoint T hTmem hT

end
