import Mathlib.Topology.Algebra.Group.Basic
import MathlibAnnex.Analysis.VonNeumannAlgebra.OperatorTopology

/-!
# Closed commutants in the operator topologies

The algebraic centralizer is unchanged by passage to the standard WOT copy.
Consequently Mathlib's closed-centralizer theorem applies in WOT, and the
continuous SOT-to-WOT comparison gives strong closedness. The set being
centralized need not be closed, linear, unital, or stable under adjoints.
-/

set_option autoImplicit false

open Filter Topology

namespace ContinuousLinearMapWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Passing to the weak operator topology preserves the centralizer as a set. -/
theorem image_centralizer (S : Set (H →L[ℂ] H)) :
    ofCLM '' Set.centralizer S = Set.centralizer (ofCLM '' S) := by
  ext T
  constructor
  · rintro ⟨Q, hQ, rfl⟩ U ⟨U, hU, rfl⟩
    exact congrArg ofCLM (hQ U hU)
  · intro hT
    refine ⟨T.toCLM, ?_, by cases T; rfl⟩
    intro Q hQ
    exact congrArg toCLM (hT _ ⟨Q, hQ, rfl⟩)

/-- The commutant of an arbitrary operator set is weak-operator closed. -/
theorem isClosed_image_centralizer (S : Set (H →L[ℂ] H)) :
    IsClosed (ofCLM '' Set.centralizer S) := by
  rw [image_centralizer]
  exact Set.isClosed_centralizer _

end ContinuousLinearMapWOT

namespace PointwiseConvergenceCLM

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The commutant of an arbitrary operator set is strong-operator closed. -/
theorem isClosed_image_centralizer (S : Set (H →L[ℂ] H)) :
    IsClosed ((ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H) ''
      Set.centralizer S) := by
  have hpre :
      (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H) ''
          Set.centralizer S =
        (toWOT ℂ H H) ⁻¹' (ContinuousLinearMapWOT.ofCLM '' Set.centralizer S) := by
    ext T
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      exact ⟨Q, hQ, rfl⟩
    · rintro ⟨Q, hQ, hQT⟩
      exact ⟨Q, hQ, congrArg ContinuousLinearMapWOT.toCLM hQT⟩
  rw [hpre]
  exact (ContinuousLinearMapWOT.isClosed_image_centralizer S).preimage
    (toWOT ℂ H H).continuous

end PointwiseConvergenceCLM
