import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.NormalExtension
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.RepresentedCentralCorner

set_option autoImplicit false
noncomputable section
open Topology
open MathlibAnnex.RepresentedBidual MathlibAnnex.CStarBidual

universe u v w

section NonUnital
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

example (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (M : VonNeumannAlgebra H)
    (h : ∀ a : A, rho a ∈ M) (F : StrongDual ℂ (StrongDual ℂ A)) :
    extension rho F ∈ M := extension_mem_vonNeumannAlgebra rho M h F

example (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (sigma : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (U : H →L[ℂ] K)
    (h : ∀ a : A, (sigma a).comp U = U.comp (rho a))
    (F : StrongDual ℂ (StrongDual ℂ A)) (x : H) :
    extension sigma F (U x) = U (extension rho F x) :=
  congrArg (fun T : H →L[ℂ] K => T x) (intertwines_extension rho sigma U h F)

example (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (T : StrongDual ℂ (StrongDual ℂ A) → (H →L[ℂ] H))
    (hc : Continuous (fun F : WeakDual ℂ (StrongDual ℂ A) =>
      ContinuousLinearMapWOT.ofCLM (T (WeakDual.toStrongDual F))))
    (hi : ∀ a : A, T (NormedSpace.inclusionInDoubleDual ℂ A a) = rho a)
    (F : StrongDual ℂ (StrongDual ℂ A)) : T F = extension rho F :=
  congrFun (extension_unique rho T hc hi) F

example (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (r : ℝ) :
    IsClosed ((fun F : StrongDual ℂ (StrongDual ℂ A) =>
      ContinuousLinearMapWOT.ofCLM (extension rho F)) '' Metric.closedBall 0 r) :=
  isClosed_wot_extension_closedBall rho r
end NonUnital

section Unital
variable {A : Type u} [CStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open MathlibAnnex.Analysis.CStarAlgebra.Enveloping

example (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    (extensionToGenerated pi (Model.canonical A a) : H →L[ℂ] H) = pi a :=
  extension_canonical pi.toNonUnitalStarAlgHom a

example (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (F G : Model A) :
    extensionToGenerated pi (F * star G) =
      extensionToGenerated pi F * star (extensionToGenerated pi G) := by
  rw [map_mul, map_star]

/-- Existing central support is consumed through the literal raw carrier.
The pre-existing provider, not a new support axiom, supplies the witness. -/
example [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    ∃ p : StrongDual ℂ (StrongDual ℂ A),
      bidualStar p = p ∧ arensProduct p p = p ∧
      (∀ F, arensProduct p F = arensProduct F p) ∧
      (∀ F, extension pi.toNonUnitalStarAlgHom F = 0 ↔ arensProduct p F = 0) := by
  refine ⟨Model.toRaw A (MathlibAnnex.RepresentedCentralCorner.projection pi), ?_, ?_, ?_, ?_⟩
  · exact MathlibAnnex.RepresentedCentralCorner.projection_star pi
  · exact MathlibAnnex.RepresentedCentralCorner.projection_idem pi
  · intro F
    exact MathlibAnnex.RepresentedCentralCorner.projection_central pi ((Model.toRaw A).symm F)
  · intro F
    exact MathlibAnnex.RepresentedCentralCorner.kernel_iff pi ((Model.toRaw A).symm F)
end Unital
