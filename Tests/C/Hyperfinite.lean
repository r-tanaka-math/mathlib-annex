import MathlibAnnex.Analysis.VonNeumannAlgebra.Hyperfinite

set_option autoImplicit false

open Set Topology

universe u v

example {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) {ι : Type v} [Nonempty ι]
    (F : ι → StarSubalgebra ℂ (H →L[ℂ] H))
    (hdir : Directed (· ≤ ·) F)
    (hsub : ∀ i, F i ≤ M.toStarSubalgebra)
    (hfin : ∀ i, FiniteDimensional ℂ (F i))
    (hdense : closure
        ((ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H) ''
          ⋃ i, (F i : Set (H →L[ℂ] H))) =
      (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H) ''
        (M : Set (H →L[ℂ] H))) :
    VonNeumannAlgebra.IsHyperfinite M :=
  VonNeumannAlgebra.isHyperfinite_of_directed M F hdir hsub hfin hdense
