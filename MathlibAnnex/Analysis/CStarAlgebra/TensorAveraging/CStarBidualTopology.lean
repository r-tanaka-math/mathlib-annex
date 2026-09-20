import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.CStarBidualModel
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.RepresentedBidualBall

/-!
# The prescribed predual and represented quotient of the actual C*-bidual

The weak carrier remains WeakDual ℂ (StrongDual ℂ A). Both multiplication
maps, involution, compact balls, and weak-star-to-WOT quotient continuity
are proved for the Model whose original norm and Arens operations are fixed.
No claim of weak-star-to-operator-norm continuity is made. C03, unbuilt.
-/
set_option autoImplicit false
noncomputable section
open Filter Topology

namespace MathlibAnnex.CStarBidual
open MathlibAnnex.RepresentedBidual
universe u v
variable {A : Type u} [CStarAlgebra A]

/-- The actual predual carrier, not a newly chosen duality. -/
def weak : Model A ≃ WeakDual ℂ (StrongDual ℂ A) :=
  (Model.toRaw A).toEquiv.trans StrongDual.toWeakDual.toEquiv

@[simp] theorem weak_apply (F : Model A) :
    weak F = StrongDual.toWeakDual (Model.toRaw A F) := rfl
@[simp] theorem weak_symm_apply (F : WeakDual ℂ (StrongDual ℂ A)) :
    weak.symm F = (Model.toRaw A).symm (WeakDual.toStrongDual F) := rfl

theorem continuous_weak_norm : Continuous (weak (A := A)) :=
  NormedSpace.Dual.toWeakDual_continuous.comp (Model.toRaw A).continuous

/-- Left multiplication: the varying variable is the second Arens slot. -/
theorem weak_mul_left (F : Model A) :
    Continuous (fun G : WeakDual ℂ (StrongDual ℂ A) => weak (F * weak.symm G)) :=
  continuous_arensProduct_right (Model.toRaw A F)

/-- Right multiplication: the varying variable is the first Arens slot. -/
theorem weak_mul_right (F : Model A) :
    Continuous (fun G : WeakDual ℂ (StrongDual ℂ A) => weak (weak.symm G * F)) :=
  continuous_arensProduct_left (Model.toRaw A F)

theorem continuous_weak_star :
    Continuous (fun G : WeakDual ℂ (StrongDual ℂ A) => weak (star (weak.symm G))) :=
  bidualStar_weakStarContinuous

/-- Every original norm ball is compact for this predual, including an empty
negative-radius ball. -/
theorem isCompact_weak_closedBall (r : ℝ) :
    IsCompact (weak '' Metric.closedBall (0 : Model A) r) := by
  have heq : weak '' Metric.closedBall (0 : Model A) r =
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ (StrongDual ℂ A)) r := by
    ext F
    constructor
    · rintro ⟨G, hG, rfl⟩
      change dist G 0 ≤ r at hG
      change dist (Model.toRaw A G) 0 ≤ r
      have hz : Model.toRaw A (0 : Model A) = 0 := rfl
      have heq : dist (Model.toRaw A G) 0 = dist G 0 := by
        simpa only [hz] using (Model.toRaw A).isometry.dist_eq G 0
      simpa only [heq] using hG
    · intro hF
      refine ⟨weak.symm F, ?_, weak.apply_symm_apply F⟩
      change dist (WeakDual.toStrongDual F) 0 ≤ r at hF
      change dist ((Model.toRaw A).symm (WeakDual.toStrongDual F)) 0 ≤ r
      have hz : (Model.toRaw A).symm (0 : StrongDual ℂ (StrongDual ℂ A)) = 0 := rfl
      have heq : dist ((Model.toRaw A).symm (WeakDual.toStrongDual F)) 0 =
          dist (WeakDual.toStrongDual F) 0 := by
        simpa only [hz] using
          (Model.toRaw A).symm.isometry.dist_eq (WeakDual.toStrongDual F) 0
      simpa only [heq] using hF
  rw [heq]
  exact WeakDual.isCompact_closedBall (0 : StrongDual ℂ (StrongDual ℂ A)) r

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The represented extension is now an actual unital star-algebra homomorphism
from the constructed C*-bidual. Its underlying function is C01's extension. -/
def quotient (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) : Model A →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun F := extension pi.toNonUnitalStarAlgHom (Model.toRaw A F)
  map_zero' := map_zero _
  map_add' F G := map_add _ _ _
  map_mul' F G := extension_arensProduct pi.toNonUnitalStarAlgHom _ _
  map_one' := by
    change extension pi.toNonUnitalStarAlgHom (NormedSpace.inclusionInDoubleDual ℂ A 1) = 1
    rw [extension_canonical]
    exact map_one pi
  commutes' c := by
    change extension pi.toNonUnitalStarAlgHom
      (c • NormedSpace.inclusionInDoubleDual ℂ A 1) = algebraMap ℂ (H →L[ℂ] H) c
    rw [map_smul, extension_canonical,
      show pi.toNonUnitalStarAlgHom 1 = 1 from map_one pi,
      Algebra.algebraMap_eq_smul_one]
  map_star' F := extension_bidualStar pi.toNonUnitalStarAlgHom _

@[simp] theorem quotient_apply (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (F : Model A) :
    quotient pi F = extension pi.toNonUnitalStarAlgHom (Model.toRaw A F) := rfl

@[simp] theorem quotient_canonical (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    quotient pi (Model.canonical A a) = pi a :=
  extension_canonical pi.toNonUnitalStarAlgHom a

/-- A coefficientwise, globally weak-star-to-WOT continuity statement. -/
theorem quotient_weakStar_wot (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    Continuous (fun F : WeakDual ℂ (StrongDual ℂ A) =>
      ContinuousLinearMapWOT.ofCLM (quotient pi (weak.symm F))) :=
  extension_weakStar_wotContinuous pi.toNonUnitalStarAlgHom

/-- Irreducibility supplies every norm-controlled preimage. The kernel
projection and coherent section have not been assumed. -/
theorem quotient_preimage [Nontrivial H]
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    (T : H →L[ℂ] H) :
    ∃ F : Model A, quotient pi F = T ∧ ‖F‖ ≤ ‖T‖ := by
  obtain ⟨F, hnorm, hF⟩ := exists_extension_preimage_norm_le pi hpi T
  exact ⟨(Model.toRaw A).symm F, hF, hnorm⟩

end MathlibAnnex.CStarBidual
