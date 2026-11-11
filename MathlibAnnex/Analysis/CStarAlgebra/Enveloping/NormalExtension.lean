import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.CStarBidualTopology
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.UniversalStarNet
import MathlibAnnex.Analysis.VonNeumannAlgebra.Bicommutant

/-!
# The represented bidual map and generated von Neumann algebras

The existing coefficient-defined map `RepresentedBidual.extension` takes its
values in every concrete von Neumann algebra containing the source image.
It is the unique extension continuous from the prescribed weak-star topology
to WOT. Its bounded images are WOT-closed, and its full image has the same WOT
closure as the original representation. Intertwining operators extend as well.

The uniqueness and containment results allow nonunital, degenerate and zero
representations. For a unital representation the map is bundled with codomain
the generated von Neumann algebra. WOT continuity is used with exactly that
meaning; the statements do not replace ultraweak normality by WOT continuity.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace MathlibAnnex.RepresentedBidual

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

/-- A source intertwiner also intertwines the canonical bidual extensions.
No unit, irreducibility or nondegeneracy is needed. -/
theorem intertwines_extension
    (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (sigma : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (U : H →L[ℂ] K)
    (hU : ∀ a : A, (sigma a).comp U = U.comp (rho a))
    (F : StrongDual ℂ (StrongDual ℂ A)) :
    (extension sigma F).comp U = U.comp (extension rho F) := by
  apply ContinuousLinearMap.ext
  intro xi
  apply MathlibAnnex.HilbertBidual.eq_of_dual_eq
  intro g
  have hc : coefficient sigma (U xi) g = coefficient rho xi (g.comp U) := by
    ext a
    change g (sigma a (U xi)) = g (U (rho a xi))
    exact congrArg (fun T : H →L[ℂ] K => g (T xi)) (hU a)
  change g (extension sigma F (U xi)) = (g.comp U) (extension rho F xi)
  rw [coefficient_extension, coefficient_extension, hc]

/-- Every operator in the source commutant also commutes with each represented
bidual element. The witness remains on the same Hilbert space. -/
theorem commutes_extension
    (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : ∀ a : A, rho a * T = T * rho a)
    (F : StrongDual ℂ (StrongDual ℂ A)) :
    extension rho F * T = T * extension rho F :=
  intertwines_extension rho rho T hT F

/-- The actual extension belongs to every containing von Neumann algebra.
The proof uses the existing norm-controlled strong-star source net. -/
theorem extension_mem_vonNeumannAlgebra
    (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (M : VonNeumannAlgebra H)
    (hrho : ∀ a : A, rho a ∈ M)
    (F : StrongDual ℂ (StrongDual ℂ A)) : extension rho F ∈ M := by
  classical
  let a := universalSample (fun _ : Unit => H) (fun _ => rho) F
  apply M.mem_of_stronglyConverges (l := atTop) (f := fun d => rho (a d))
    (fun d => hrho (a d))
  intro xi
  exact (universalSample_strongStar (fun _ : Unit => H)
    (fun _ => rho) F () xi).1

/-- A represented bidual element is a WOT limit of original represented
elements, also for degenerate representations. -/
theorem extension_mem_wotClosure_range
    (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (F : StrongDual ℂ (StrongDual ℂ A)) :
    ContinuousLinearMapWOT.ofCLM (extension rho F) ∈
      closure (Set.range (fun a : A => ContinuousLinearMapWOT.ofCLM (rho a))) := by
  classical
  let a := universalSample (fun _ : Unit => H) (fun _ => rho) F
  have hlim : ContinuousLinearMap.StronglyConverges
      (fun d => rho (a d)) atTop (extension rho F) := by
    intro xi
    exact (universalSample_strongStar (fun _ : Unit => H)
      (fun _ => rho) F () xi).1
  exact isClosed_closure.mem_of_tendsto hlim.tendsto_wot
    (Filter.Eventually.of_forall (fun d => subset_closure ⟨a d, rfl⟩))

/-- Taking the represented bidual image does not enlarge the weak closure.
The equality concerns closures; it does not assert surjectivity onto them. -/
theorem wotClosure_range_extension
    (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    closure (Set.range (fun F : StrongDual ℂ (StrongDual ℂ A) =>
      ContinuousLinearMapWOT.ofCLM (extension rho F))) =
    closure (Set.range (fun a : A => ContinuousLinearMapWOT.ofCLM (rho a))) := by
  apply le_antisymm
  · apply closure_minimal _ isClosed_closure
    rintro _ ⟨F, rfl⟩
    exact extension_mem_wotClosure_range rho F
  · apply closure_mono
    rintro _ ⟨a, rfl⟩
    exact ⟨NormedSpace.inclusionInDoubleDual ℂ A a,
      congrArg ContinuousLinearMapWOT.ofCLM (extension_canonical rho a)⟩

/-- Uniqueness among weak-star-to-WOT continuous maps agreeing on the source.
Linearity of the competing map is not an additional assumption. -/
theorem extension_unique
    (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (T : StrongDual ℂ (StrongDual ℂ A) → (H →L[ℂ] H))
    (hcont : Continuous (fun F : WeakDual ℂ (StrongDual ℂ A) =>
      ContinuousLinearMapWOT.ofCLM (T (WeakDual.toStrongDual F))))
    (hsource : ∀ a : A, T (NormedSpace.inclusionInDoubleDual ℂ A a) = rho a) :
    T = extension rho := by
  classical
  funext F
  let a := universalSample (fun _ : Unit => H) (fun _ => rho) F
  have hweak := universalSample_weakStar (fun _ : Unit => H) (fun _ => rho) F
  have hT := hcont.continuousAt.tendsto.comp hweak
  have hext := (extension_weakStar_wotContinuous rho).continuousAt.tendsto.comp hweak
  have heq :
      (fun d => ContinuousLinearMapWOT.ofCLM
        (T (NormedSpace.inclusionInDoubleDual ℂ A (a d)))) =
      (fun d => ContinuousLinearMapWOT.ofCLM
        (extension rho (NormedSpace.inclusionInDoubleDual ℂ A (a d)))) := by
    funext d
    rw [hsource, extension_canonical]
  change Tendsto (fun d => ContinuousLinearMapWOT.ofCLM
    (T (NormedSpace.inclusionInDoubleDual ℂ A (a d)))) atTop
    (𝓝 (ContinuousLinearMapWOT.ofCLM (T F))) at hT
  change Tendsto (fun d => ContinuousLinearMapWOT.ofCLM
    (extension rho (NormedSpace.inclusionInDoubleDual ℂ A (a d)))) atTop
    (𝓝 (ContinuousLinearMapWOT.ofCLM (extension rho F))) at hext
  rw [heq] at hT
  exact ContinuousLinearMapWOT.ofCLM_injective (tendsto_nhds_unique hT hext)

/-- Every bounded bidual ball has a WOT-compact represented image. This uses
the original dual norm, without a renorming or a nonzero-space assumption. -/
theorem isCompact_wot_extension_closedBall
    (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (r : ℝ) :
    IsCompact ((fun F : StrongDual ℂ (StrongDual ℂ A) =>
      ContinuousLinearMapWOT.ofCLM (extension rho F)) '' Metric.closedBall 0 r) := by
  have heq : ((fun F : StrongDual ℂ (StrongDual ℂ A) =>
      ContinuousLinearMapWOT.ofCLM (extension rho F)) '' Metric.closedBall 0 r) =
      (fun F : WeakDual ℂ (StrongDual ℂ A) =>
        ContinuousLinearMapWOT.ofCLM (extension rho (WeakDual.toStrongDual F))) ''
      (WeakDual.toStrongDual ⁻¹' Metric.closedBall
        (0 : StrongDual ℂ (StrongDual ℂ A)) r) := by
    ext T
    constructor
    · rintro ⟨F, hF, rfl⟩
      exact ⟨StrongDual.toWeakDual F, hF, rfl⟩
    · rintro ⟨F, hF, rfl⟩
      exact ⟨WeakDual.toStrongDual F, hF, rfl⟩
  rw [heq]
  exact (WeakDual.isCompact_closedBall
    (0 : StrongDual ℂ (StrongDual ℂ A)) r).image (extension_weakStar_wotContinuous rho)

/-- In particular each bounded image is closed in WOT. -/
theorem isClosed_wot_extension_closedBall
    (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (r : ℝ) :
    IsClosed ((fun F : StrongDual ℂ (StrongDual ℂ A) =>
      ContinuousLinearMapWOT.ofCLM (extension rho F)) '' Metric.closedBall 0 r) :=
  (isCompact_wot_extension_closedBall rho r).isClosed

end MathlibAnnex.RepresentedBidual

namespace MathlibAnnex.Analysis.CStarAlgebra.Enveloping
open MathlibAnnex.RepresentedBidual MathlibAnnex.CStarBidual

universe u v
variable {A : Type u} [CStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A unital representation's existing bidual quotient, now with its actual
generated von Neumann algebra as codomain. -/
def extensionToGenerated (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    Model A →⋆ₐ[ℂ] (VonNeumannAlgebra.generated pi.range).toStarSubalgebra :=
  (quotient pi).codRestrict (VonNeumannAlgebra.generated pi.range).toStarSubalgebra
    (fun F => extension_mem_vonNeumannAlgebra pi.toNonUnitalStarAlgHom
      (VonNeumannAlgebra.generated pi.range)
      (fun a => VonNeumannAlgebra.subset_generated pi.range ⟨a, rfl⟩)
      (Model.toRaw A F))

@[simp]
theorem extensionToGenerated_apply (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (F : Model A) :
    (extensionToGenerated pi F : H →L[ℂ] H) =
      extension pi.toNonUnitalStarAlgHom (Model.toRaw A F) := rfl

/-- The commuting canonical-embedding equation holds in the algebra subtype. -/
@[simp]
theorem extensionToGenerated_canonical (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    extensionToGenerated pi (Model.canonical A a) =
      ⟨pi a, VonNeumannAlgebra.subset_generated pi.range ⟨a, rfl⟩⟩ := by
  apply Subtype.ext
  exact extension_canonical pi.toNonUnitalStarAlgHom a

/-- The prescribed weak-star-to-WOT continuity survives codomain restriction. -/
theorem extensionToGenerated_weakStar_wot (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    Continuous (fun F : WeakDual ℂ (StrongDual ℂ A) =>
      ContinuousLinearMapWOT.ofCLM
        (extensionToGenerated pi (weak.symm F) : H →L[ℂ] H)) :=
  quotient_weakStar_wot pi

end MathlibAnnex.Analysis.CStarAlgebra.Enveloping
