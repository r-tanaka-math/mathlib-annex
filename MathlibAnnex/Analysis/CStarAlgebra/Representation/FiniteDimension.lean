import MathlibAnnex.Analysis.CStarAlgebra.CompactPreimage
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Faithful
import MathlibAnnex.Analysis.CStarAlgebra.Representation.RankOneProjection

/-!
# Finite dimension forced by a separable singleton irreducible model
-/

set_option autoImplicit false

open Set
open scoped ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Representation

/-- The Hilbert space of a separable singleton irreducible model of a
nonzero unital C-star algebra is finite-dimensional. -/
theorem finiteDimensional_space_of_singleton [Nontrivial A]
    [TopologicalSpace.SeparableSpace H]
    (pi : Representation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi) :
    FiniteDimensional ℂ H := by
  have hinj : Function.Injective pi := injective_of_singleton pi hsingle
  have hsimple : IsSimpleCStarAlgebra A :=
    isSimpleCStarAlgebra_of_singleton_of_injective pi hsingle hinj
  obtain ⟨p, hp, hpne, hcorner⟩ :=
    exists_nonzero_projection_scalar_corner pi hsingle
  have hpmap : pi p ≠ 0 := by
    intro hzero
    apply hpne
    apply hinj
    simpa using hzero
  have hpcompact : IsCompactOperator (pi p) :=
    isCompactOperator_map_of_scalar_corner pi hsingle.1 hp hpmap hcorner
  let piNU : A →⋆ₙₐ H →L[ℂ] H := pi.toNonUnitalStarAlgHom
  let I : TwoSidedIdeal A := MathlibAnnex.CStarAlgebra.compactPreimageIdeal piNU
  have hpI : p ∈ I :=
    (MathlibAnnex.CStarAlgebra.mem_compactPreimageIdeal piNU p).2 hpcompact
  have hIne : I ≠ ⊥ := by
    intro hbot
    have hpzero : p = 0 := by
      rw [hbot] at hpI
      simpa using hpI
    exact hpne hpzero
  have hItop : I = ⊤ :=
    (hsimple.2 I
      (MathlibAnnex.CStarAlgebra.isClosed_compactPreimageIdeal piNU)).resolve_left hIne
  have honeI : (1 : A) ∈ I := by
    rw [hItop]
    trivial
  have honeCompact : IsCompactOperator (pi (1 : A)) :=
    (MathlibAnnex.CStarAlgebra.mem_compactPreimageIdeal piNU 1).1 honeI
  have hcompactOne :
      IsCompactOperator ((1 : H →L[ℂ] H) : H → H) := by
    simpa only [map_one, one_apply_eq_self] using honeCompact
  apply FiniteDimensional.of_isCompactOperator_id
  change IsCompactOperator (fun x : H => x)
  exact hcompactOne

/-- The algebra itself is finite-dimensional once its singleton model is
faithful and its separable representation space is finite-dimensional. -/
theorem finiteDimensional_algebra_of_singleton [Nontrivial A]
    [TopologicalSpace.SeparableSpace H]
    (pi : Representation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi) :
    FiniteDimensional ℂ A := by
  letI : FiniteDimensional ℂ H :=
    finiteDimensional_space_of_singleton pi hsingle
  letI : FiniteDimensional ℂ (H →L[ℂ] H) :=
    ContinuousLinearMap.finiteDimensional
  exact FiniteDimensional.of_injective
    (LinearMapClass.linearMap pi) (injective_of_singleton pi hsingle)

end Representation

end MathlibAnnex.Analysis.CStarAlgebra
