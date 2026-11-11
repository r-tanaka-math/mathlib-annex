import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.CornerEquivalence

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

open MathlibAnnex.Analysis.CStarAlgebra MathlibAnnex.RepresentedBidual

noncomputable section

variable {A H : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)

attribute [local irreducible] VonNeumannAlgebra.corner envelopingRepresentationSupportProjection

private abbrev CornerEquivCarrier {K L : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    (M : VonNeumannAlgebra K) (N : VonNeumannAlgebra L) (C : NonUnitalStarSubalgebra ℂ M.toStarSubalgebra) :=
  ↥C ≃⋆ₐ[ℂ] N.toStarSubalgebra

section
variable {K L : Type*}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (M : VonNeumannAlgebra K) (N : VonNeumannAlgebra L)
variable (C : NonUnitalStarSubalgebra ℂ M.toStarSubalgebra)

private abbrev CornerProductLaw (e : CornerEquivCarrier M N C) (x y : C) : Prop :=
  e (x * y) = e x * e y

private theorem corner_product_law (e : CornerEquivCarrier M N C) (x y : C) :
    CornerProductLaw M N C e x y := map_mul e x y

private theorem corner_star_law (e : CornerEquivCarrier M N C) (x : C) :
    e (star x) = star (e x) := map_star e x

private abbrev CornerUnitLaws (p : M.toStarSubalgebra) (hp : IsStarProjection p)
    (x : M.corner p hp) : Prop :=
  M.cornerUnit p hp * x = x ∧ x * M.cornerUnit p hp = x

private theorem corner_unit_laws (p : M.toStarSubalgebra) (hp : IsStarProjection p)
    (x : M.corner p hp) : CornerUnitLaws M p hp x :=
  ⟨M.cornerUnit_mul p hp x, M.mul_cornerUnit p hp x⟩

private abbrev HasNormLift (r : ↥C →⋆ₙₐ[ℂ] N.toStarSubalgebra) (y : N.toStarSubalgebra) : Prop :=
  ∃ x : C, r x = y ∧ ‖x‖ = ‖y‖

private theorem corner_norm_lift (r : ↥C →⋆ₙₐ[ℂ] N.toStarSubalgebra) (e : CornerEquivCarrier M N C)
    (hr : ∀ x : C, r x = e x) (he : Isometry e) (y : N.toStarSubalgebra) : HasNormLift M N C r y := by
  let x := e.invFun y
  have h : e x = y := e.toEquiv.apply_symm_apply y
  refine ⟨x, (hr x).trans h, ?_⟩
  calc
    ‖x‖ = dist x 0 := (dist_zero_right x).symm
    _ = dist (e x) (e 0) := (he.dist_eq x 0).symm
    _ = ‖y‖ := by rw [h, map_zero, dist_zero_right]
end

example : CornerEquivCarrier (envelopingVonNeumannAlgebra (A := A))
    (VonNeumannAlgebra.generated pi.unitization.range) (envelopingRepresentationCorner pi hnd) :=
  envelopingRepresentationCornerEquiv pi hnd

example (S : envelopingRepresentationCorner pi hnd) :
    (envelopingRepresentationCornerEquiv pi hnd S : H →L[ℂ] H) =
      extension pi ((bidualEnvelopingEquiv (A := A)).symm S) := rfl

example (S T : envelopingRepresentationCorner pi hnd) :
    CornerProductLaw (envelopingVonNeumannAlgebra (A := A))
    (VonNeumannAlgebra.generated pi.unitization.range) (envelopingRepresentationCorner pi hnd) (envelopingRepresentationCornerEquiv pi hnd) S T :=
  corner_product_law (envelopingVonNeumannAlgebra (A := A))
    (VonNeumannAlgebra.generated pi.unitization.range) (envelopingRepresentationCorner pi hnd) (envelopingRepresentationCornerEquiv pi hnd) S T

example (S : envelopingRepresentationCorner pi hnd) :
    envelopingRepresentationCornerEquiv pi hnd (star S) =
      star (envelopingRepresentationCornerEquiv pi hnd S) :=
  corner_star_law (envelopingVonNeumannAlgebra (A := A))
    (VonNeumannAlgebra.generated pi.unitization.range) (envelopingRepresentationCorner pi hnd) (envelopingRepresentationCornerEquiv pi hnd) S

example (S : envelopingRepresentationCorner pi hnd) :
    CornerUnitLaws (envelopingVonNeumannAlgebra (A := A)) (envelopingRepresentationSupportProjection pi hnd)
    (isStarProjection_envelopingRepresentationSupportProjection pi hnd) S :=
  corner_unit_laws (envelopingVonNeumannAlgebra (A := A)) (envelopingRepresentationSupportProjection pi hnd)
    (isStarProjection_envelopingRepresentationSupportProjection pi hnd) S

example : envelopingRepresentationCornerEquiv pi hnd
    (VonNeumannAlgebra.cornerUnit (envelopingVonNeumannAlgebra (A := A))
      (envelopingRepresentationSupportProjection pi hnd)
      (isStarProjection_envelopingRepresentationSupportProjection pi hnd)) = 1 :=
  envelopingRepresentationCornerEquiv_cornerUnit pi hnd

example : (envelopingRepresentationCornerEquiv pi hnd).invFun 1 =
    VonNeumannAlgebra.cornerUnit (envelopingVonNeumannAlgebra (A := A))
      (envelopingRepresentationSupportProjection pi hnd)
      (isStarProjection_envelopingRepresentationSupportProjection pi hnd) :=
  envelopingRepresentationCornerEquiv_symm_one pi hnd

example (S : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) :
    ((envelopingRepresentationCornerEquiv pi hnd).invFun
      (envelopingRepresentationExtension pi hnd S) :
        (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) =
      envelopingRepresentationSupportProjection pi hnd * S := by
  exact congrArg Subtype.val (envelopingRepresentationCornerEquiv_symm_extension pi hnd S)

example : Isometry (envelopingRepresentationCornerEquiv pi hnd) :=
  isometry_envelopingRepresentationCornerEquiv pi hnd

example (T : (VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra) :
    HasNormLift (envelopingVonNeumannAlgebra (A := A))
    (VonNeumannAlgebra.generated pi.unitization.range) (envelopingRepresentationCorner pi hnd) (envelopingRepresentationCornerHom pi hnd) T :=
  corner_norm_lift (envelopingVonNeumannAlgebra (A := A))
    (VonNeumannAlgebra.generated pi.unitization.range) (envelopingRepresentationCorner pi hnd) (envelopingRepresentationCornerHom pi hnd)
    (envelopingRepresentationCornerEquiv pi hnd) (fun _ => rfl)
    (isometry_envelopingRepresentationCornerEquiv pi hnd) T

end
