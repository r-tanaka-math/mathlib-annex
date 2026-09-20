import MathlibAnnex.Analysis.CStarAlgebra.Representation.FullImage
import MathlibAnnex.Analysis.CStarAlgebra.Representation.MinimalProjectionDensity

/-! # The unital Rosenberg theorem below the continuum -/

set_option autoImplicit false

open Set
open scoped Cardinal ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Representation

/-- In a simple unital algebra, a nonzero source element with compact image
forces the represented identity to be compact.  This is independent of density. -/
theorem isCompactOperator_map_one_of_isSimpleCStarAlgebra
    (pi : Representation A H) (hsimple : IsSimpleCStarAlgebra A)
    {p : A} (hp : p ≠ 0)
    (hpcompact : IsCompactOperator (pi p)) :
    IsCompactOperator (pi (1 : A)) := by
  let piNU : A →⋆ₙₐ H →L[ℂ] H := pi.toNonUnitalStarAlgHom
  let I : TwoSidedIdeal A := MathlibAnnex.CStarAlgebra.compactPreimageIdeal piNU
  have hpI : p ∈ I :=
    (MathlibAnnex.CStarAlgebra.mem_compactPreimageIdeal piNU p).2 hpcompact
  have hIne : I ≠ ⊥ := by
    intro hbot
    have hpzero : p = 0 := by
      rw [hbot] at hpI
      simpa using hpI
    exact hp hpzero
  have hItop : I = ⊤ :=
    (hsimple.2 I
      (MathlibAnnex.CStarAlgebra.isClosed_compactPreimageIdeal piNU)).resolve_left hIne
  have honeI : (1 : A) ∈ I := by
    rw [hItop]
    trivial
  exact (MathlibAnnex.CStarAlgebra.mem_compactPreimageIdeal piNU 1).1 honeI

/-- A unital singleton model of density below the continuum is finite-dimensional. -/
theorem finiteDimensional_space_of_singleton_of_dense [Nontrivial A]
    (pi : Representation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (s : Set H) (hs : Dense s) (hcard : #s < Cardinal.continuum) :
    FiniteDimensional ℂ H := by
  have hinj : Function.Injective pi := injective_of_singleton pi hsingle
  have hsimple : IsSimpleCStarAlgebra A :=
    isSimpleCStarAlgebra_of_singleton_of_injective pi hsingle hinj
  obtain ⟨p, hp, hpne, hcorner⟩ :=
    exists_nonzero_projection_scalar_corner_of_singleton_of_dense pi hsingle s hs hcard
  have hpmap : pi p ≠ 0 := by
    intro hzero
    apply hpne
    apply hinj
    simpa using hzero
  have hpcompact : IsCompactOperator (pi p) :=
    isCompactOperator_map_of_scalar_corner pi hsingle.1 hp hpmap hcorner
  have honeCompact :=
    isCompactOperator_map_one_of_isSimpleCStarAlgebra pi hsimple hpne hpcompact
  have hcompactOne : IsCompactOperator ((1 : H →L[ℂ] H) : H → H) := by
    simpa only [map_one, one_apply_eq_self] using honeCompact
  apply FiniteDimensional.of_isCompactOperator_id
  change IsCompactOperator (fun x : H => x)
  exact hcompactOne

/-- The algebra itself is finite-dimensional once its singleton model is
faithful and its representation space of density below the continuum is finite-dimensional. -/
theorem finiteDimensional_algebra_of_singleton_of_dense [Nontrivial A]
    (pi : Representation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (s : Set H) (hs : Dense s) (hcard : #s < Cardinal.continuum) :
    FiniteDimensional ℂ A := by
  letI : FiniteDimensional ℂ H :=
    finiteDimensional_space_of_singleton_of_dense pi hsingle s hs hcard
  letI : FiniteDimensional ℂ (H →L[ℂ] H) :=
    ContinuousLinearMap.finiteDimensional
  exact FiniteDimensional.of_injective
    (LinearMapClass.linearMap pi) (injective_of_singleton pi hsingle)

/-- The faithful represented range equals all compact operators.  For a
unital source the representation space is, in fact, finite-dimensional. -/
theorem isCompactOperatorModel_of_singleton_of_dense
    [Nontrivial A] (pi : Representation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (s : Set H) (hs : Dense s) (hcard : #s < Cardinal.continuum) :
    IsCompactOperatorModel pi.toNonUnitalStarAlgHom := by
  letI : Nontrivial H := nontrivial_of_isNonzero pi hsingle.1.1
  letI : FiniteDimensional ℂ H :=
    finiteDimensional_space_of_singleton_of_dense pi hsingle s hs hcard
  refine ⟨injective_of_singleton pi hsingle, ?_, ?_⟩
  · intro a
    exact isCompactOperator_of_locallyCompactSpace_rng (pi a)
  · intro T _hT
    exact surjective_of_irreducible_of_finiteDimensional pi hsingle.1 T

end Representation
end MathlibAnnex.Analysis.CStarAlgebra
