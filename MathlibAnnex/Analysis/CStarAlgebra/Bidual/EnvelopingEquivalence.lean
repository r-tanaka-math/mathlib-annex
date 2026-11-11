import MathlibAnnex.Analysis.CStarAlgebra.Bidual.Unitization
import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.UniversalBidual

/-!
# The literal Banach bidual and the all-state enveloping algebra

The forward map is the existing represented extension on
`StrongDual ℂ (StrongDual ℂ A)`. Its original norm is preserved, and its
surjectivity is proved by recovering a bounded functional from each operator
in the universal WOT closure. Multiplication and involution are the existing
explicit Arens operations, with their compatibility proved below.

The linear isometry equivalence and the product/star equations together give
the actual isometric star-algebra identification. No competing multiplication
or norm instance is installed on StrongDual, and no replacement bidual carrier
is introduced. The weak-star homeomorphism has an explicitly WOT-topologized
subtype as target; the norm topology on the ordinary envelope subtype is not
silently used as a weak topology.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open MathlibAnnex.RepresentedBidual
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]

/-- The universal extension, restricted to the concrete envelope and bundled
with its proved isometry for the original Banach-bidual norm. -/
def bidualEnvelopingIsometry :
    StrongDual ℂ (StrongDual ℂ A) →ₗᵢ[ℂ]
      (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra where
  toFun F := ⟨extension (universalRepresentation (A := A)) F,
    extension_mem_vonNeumannAlgebra (universalRepresentation (A := A))
      (envelopingVonNeumannAlgebra (A := A))
      universalRepresentation_mem_envelopingVonNeumannAlgebra F⟩
  map_add' F G := Subtype.ext (map_add (extension (universalRepresentation (A := A))) F G)
  map_smul' c F := Subtype.ext (map_smul (extension (universalRepresentation (A := A))) c F)
  norm_map' F := norm_extension_universalRepresentation F

set_option maxHeartbeats 1600000 in
private theorem bidualEnvelopingIsometry_preimage
    (T : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) :
    ∃ F : StrongDual ℂ (StrongDual ℂ A), bidualEnvelopingIsometry (A := A) F = T := by
  have h := exists_extension_eq_of_mem_envelopingVonNeumannAlgebra (A := A) T.val T.property
  refine ⟨h.choose, ?_⟩
  apply Subtype.ext
  change extension (universalRepresentation (A := A)) h.choose = T.val
  exact h.choose_spec

private def equivOfIsometryPreimages {X Y : Type*} [NormedAddCommGroup X]
    [SeminormedAddCommGroup Y] [NormedSpace ℂ X] [NormedSpace ℂ Y]
    (f : X →ₗᵢ[ℂ] Y) (h : ∀ y : Y, ∃ x : X, f x = y) : X ≃ₗᵢ[ℂ] Y :=
  LinearIsometryEquiv.ofSurjective (F := X) (E₂ := Y) (σ₁₂ := RingHom.id ℂ) f h

set_option maxHeartbeats 1200000 in
/-- The literal Banach bidual is linearly and isometrically equivalent to the
concrete all-state envelope. Product, star, canonical inclusion and weak-star
compatibility are separate proved equations, not fields assumed of a model. -/
def bidualEnvelopingEquiv :
    StrongDual ℂ (StrongDual ℂ A) ≃ₗᵢ[ℂ]
      (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra :=
  equivOfIsometryPreimages (X := StrongDual ℂ (StrongDual ℂ A))
    (Y := ↥(envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra)
    (bidualEnvelopingIsometry (A := A)) (bidualEnvelopingIsometry_preimage (A := A))

@[simp]
theorem bidualEnvelopingEquiv_apply_coe (F : StrongDual ℂ (StrongDual ℂ A)) :
    ((bidualEnvelopingEquiv (A := A) F :
      (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) :
        UniversalHilbertSpace A →L[ℂ] UniversalHilbertSpace A) =
      extension (universalRepresentation (A := A)) F := rfl

/-- The inverse is an actual preimage under the represented extension. -/
@[simp]
theorem extension_bidualEnvelopingEquiv_symm
    (T : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) :
    extension (universalRepresentation (A := A))
      ((bidualEnvelopingEquiv (A := A)).symm T) = T.val :=
  congrArg Subtype.val ((bidualEnvelopingEquiv (A := A)).apply_symm_apply T)

/-- Both sides use the existing multiplication: first Arens on the literal
bidual, and ordinary operator multiplication on the envelope. -/
@[simp]
theorem bidualEnvelopingEquiv_arensProduct (F G : StrongDual ℂ (StrongDual ℂ A)) :
    bidualEnvelopingEquiv (A := A) (arensProduct F G) =
      bidualEnvelopingEquiv (A := A) F * bidualEnvelopingEquiv (A := A) G := by
  apply Subtype.ext
  have hF := bidualEnvelopingEquiv_apply_coe (A := A) F
  have hG := bidualEnvelopingEquiv_apply_coe (A := A) G
  exact (bidualEnvelopingEquiv_apply_coe (A := A) (arensProduct F G)).trans
    ((extension_arensProduct (universalRepresentation (A := A)) F G).trans
      (congrArg₂ (fun X Y : UniversalHilbertSpace A →L[ℂ] UniversalHilbertSpace A => X * Y)
        hF hG).symm)

/-- The explicit Banach-bidual involution corresponds to the operator adjoint. -/
@[simp]
theorem bidualEnvelopingEquiv_bidualStar (F : StrongDual ℂ (StrongDual ℂ A)) :
    bidualEnvelopingEquiv (A := A) (bidualStar F) =
      star (bidualEnvelopingEquiv (A := A) F) := by
  apply Subtype.ext
  exact (bidualEnvelopingEquiv_apply_coe (A := A) (bidualStar F)).trans
    ((extension_bidualStar (universalRepresentation (A := A)) F).trans
      (congrArg star (bidualEnvelopingEquiv_apply_coe (A := A) F)).symm)

/-- The standard evaluation embedding commutes with the original-algebra
inclusion into the concrete envelope. -/
@[simp]
theorem bidualEnvelopingEquiv_canonical (a : A) :
    bidualEnvelopingEquiv (A := A) (NormedSpace.inclusionInDoubleDual ℂ A a) =
      envelopingInclusion (A := A) a :=
  Subtype.ext (extension_canonical (universalRepresentation (A := A)) a)

@[simp]
theorem bidualEnvelopingEquiv_symm_mul
    (S T : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) :
    (bidualEnvelopingEquiv (A := A)).symm (S * T) =
      arensProduct ((bidualEnvelopingEquiv (A := A)).symm S)
        ((bidualEnvelopingEquiv (A := A)).symm T) := by
  apply (bidualEnvelopingEquiv (A := A)).injective
  let e := bidualEnvelopingEquiv (A := A)
  exact (e.apply_symm_apply (S * T)).trans
    ((congrArg₂ (· * ·) (e.apply_symm_apply S) (e.apply_symm_apply T)).symm.trans
      (bidualEnvelopingEquiv_arensProduct (e.symm S) (e.symm T)).symm)

@[simp]
theorem bidualEnvelopingEquiv_symm_star
    (T : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) :
    (bidualEnvelopingEquiv (A := A)).symm (star T) =
      bidualStar ((bidualEnvelopingEquiv (A := A)).symm T) := by
  apply (bidualEnvelopingEquiv (A := A)).injective
  let e := bidualEnvelopingEquiv (A := A)
  exact (e.apply_symm_apply (star T)).trans
    ((congrArg star (e.apply_symm_apply T)).symm.trans
      (bidualEnvelopingEquiv_bidualStar (e.symm T)).symm)

/-- Canonical evaluation can also be recovered through the inverse map. -/
@[simp]
theorem bidualEnvelopingEquiv_symm_inclusion_eval (a : A) (f : StrongDual ℂ A) :
    (bidualEnvelopingEquiv (A := A)).symm (envelopingInclusion (A := A) a) f = f a := by
  let e := bidualEnvelopingEquiv (A := A)
  exact congrArg (fun F : StrongDual ℂ (StrongDual ℂ A) => F f)
    ((congrArg e.symm (bidualEnvelopingEquiv_canonical a).symm).trans
      (e.symm_apply_apply (NormedSpace.inclusionInDoubleDual ℂ A a)))

/-- The explicit unit of the actual bidual exists even when A is nonunital.
It is not the unit of the formal unitization's extra scalar summand. -/
def bidualUnit : StrongDual ℂ (StrongDual ℂ A) :=
  (bidualEnvelopingEquiv (A := A)).symm 1

@[simp]
theorem bidualEnvelopingEquiv_bidualUnit :
    bidualEnvelopingEquiv (A := A) (bidualUnit (A := A)) = 1 :=
  (bidualEnvelopingEquiv (A := A)).apply_symm_apply 1

/-- The constructed unit is a left identity for the already defined product. -/
@[simp]
theorem arensProduct_bidualUnit_left (F : StrongDual ℂ (StrongDual ℂ A)) :
    arensProduct (bidualUnit (A := A)) F = F := by
  apply (bidualEnvelopingEquiv (A := A)).injective
  let e := bidualEnvelopingEquiv (A := A)
  exact (bidualEnvelopingEquiv_arensProduct bidualUnit F).trans
    ((congrArg (· * e F) (bidualEnvelopingEquiv_bidualUnit (A := A))).trans (one_mul _))

/-- It is also a right identity, without a unitality assumption on A. -/
@[simp]
theorem arensProduct_bidualUnit_right (F : StrongDual ℂ (StrongDual ℂ A)) :
    arensProduct F (bidualUnit (A := A)) = F := by
  apply (bidualEnvelopingEquiv (A := A)).injective
  let e := bidualEnvelopingEquiv (A := A)
  exact (bidualEnvelopingEquiv_arensProduct F bidualUnit).trans
    ((congrArg (e F * ·) (bidualEnvelopingEquiv_bidualUnit (A := A))).trans (mul_one _))

@[simp]
theorem bidualStar_bidualUnit : bidualStar (bidualUnit (A := A)) = bidualUnit (A := A) := by
  apply (bidualEnvelopingEquiv (A := A)).injective
  have h := bidualEnvelopingEquiv_bidualUnit (A := A)
  exact (bidualEnvelopingEquiv_bidualStar bidualUnit).trans
    ((congrArg star h).trans ((star_one _).trans h.symm))

/-- Exact weak-star/WOT correspondence for the universal envelope, including
unbounded parameter families. This is specific to the all-state representation. -/
def bidualEnvelopingWeakStarEquiv :
    WeakDual ℂ (StrongDual ℂ A) ≃ₜ
      {T : UniversalHilbertSpace A →WOT[ℂ] UniversalHilbertSpace A //
        T.toCLM ∈ envelopingVonNeumannAlgebra (A := A)} where
  toFun F := ⟨ContinuousLinearMapWOT.ofCLM
    (extension (universalRepresentation (A := A)) (WeakDual.toStrongDual F)),
    extension_mem_vonNeumannAlgebra (universalRepresentation (A := A))
      (envelopingVonNeumannAlgebra (A := A))
      universalRepresentation_mem_envelopingVonNeumannAlgebra (WeakDual.toStrongDual F)⟩
  invFun T := StrongDual.toWeakDual
    ((bidualEnvelopingEquiv (A := A)).symm ⟨T.val.toCLM, T.property⟩)
  left_inv F := by
    apply WeakDual.toStrongDual.injective
    change (bidualEnvelopingEquiv (A := A)).symm
      (bidualEnvelopingEquiv (A := A) (WeakDual.toStrongDual F)) = WeakDual.toStrongDual F
    exact (bidualEnvelopingEquiv (A := A)).symm_apply_apply _
  right_inv T := by
    apply Subtype.ext
    change ContinuousLinearMapWOT.ofCLM
      (extension (universalRepresentation (A := A))
        ((bidualEnvelopingEquiv (A := A)).symm ⟨T.val.toCLM, T.property⟩)) = T.val
    rw [extension_bidualEnvelopingEquiv_symm]
  continuous_toFun :=
    (extension_weakStar_wotContinuous (universalRepresentation (A := A))).subtype_mk _
  continuous_invFun := by
    apply (continuous_extension_universalRepresentation_iff _).mp
    change Continuous (fun T :
      {T : UniversalHilbertSpace A →WOT[ℂ] UniversalHilbertSpace A //
        T.toCLM ∈ envelopingVonNeumannAlgebra (A := A)} =>
      ContinuousLinearMapWOT.ofCLM
        (extension (universalRepresentation (A := A))
          ((bidualEnvelopingEquiv (A := A)).symm ⟨T.val.toCLM, T.property⟩)))
    simpa only [extension_bidualEnvelopingEquiv_symm,
      ContinuousLinearMapWOT.ofCLM_toCLM] using
        (continuous_subtype_val : Continuous (fun T :
          {T : UniversalHilbertSpace A →WOT[ℂ] UniversalHilbertSpace A //
            T.toCLM ∈ envelopingVonNeumannAlgebra (A := A)} => T.val))

/-- The topological identification is the same map as the isometric one,
with only the prescribed topologies changed. -/
@[simp]
theorem bidualEnvelopingWeakStarEquiv_apply
    (F : WeakDual ℂ (StrongDual ℂ A)) :
    (bidualEnvelopingWeakStarEquiv (A := A) F).val.toCLM =
      (bidualEnvelopingEquiv (A := A) (WeakDual.toStrongDual F)).val := rfl

/-- The weak-star inverse and the algebraic/isometric inverse coincide. -/
@[simp]
theorem bidualEnvelopingWeakStarEquiv_symm_apply
    (T : {T : UniversalHilbertSpace A →WOT[ℂ] UniversalHilbertSpace A //
      T.toCLM ∈ envelopingVonNeumannAlgebra (A := A)}) :
    WeakDual.toStrongDual ((bidualEnvelopingWeakStarEquiv (A := A)).symm T) =
      (bidualEnvelopingEquiv (A := A)).symm ⟨T.val.toCLM, T.property⟩ := rfl

end MathlibAnnex.Analysis.CStarAlgebra
