import MathlibAnnex.Analysis.CStarAlgebra.Representation.Basic

/-!
Nonunital representation interface and the unitality bridge for nonzero
irreducible representations of unital star algebras.
-/

set_option autoImplicit false

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [Semiring A] [Algebra ℂ A] [StarRing A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A possibly nonunital complex star representation. -/
abbrev NonUnitalRepresentation := A →⋆ₙₐ[ℂ] (H →L[ℂ] H)

namespace NonUnitalRepresentation

def IsNonzero (pi : NonUnitalRepresentation (A := A) (H := H)) : Prop :=
  ∃ a : A, pi a ≠ 0

def Reduces (pi : NonUnitalRepresentation (A := A) (H := H))
    (K : Submodule ℂ H) : Prop :=
  IsClosed (K : Set H) ∧
    ∀ (a : A) (x : H), x ∈ K →
      pi a x ∈ K ∧ ContinuousLinearMap.adjoint (pi a) x ∈ K

def IsIrreducible (pi : NonUnitalRepresentation (A := A) (H := H)) : Prop :=
  pi.IsNonzero ∧ ∀ K : Submodule ℂ H, pi.Reduces K → K = ⊥ ∨ K = ⊤

theorem one_idempotent (pi : NonUnitalRepresentation (A := A) (H := H)) :
    IsIdempotentElem (pi 1) := by
  rw [IsIdempotentElem, ← map_mul]
  simp

/-- The range of `pi 1` is a closed reducing subspace, even before unitality
has been established. -/
theorem reduces_range_one (pi : NonUnitalRepresentation (A := A) (H := H)) :
    pi.Reduces (pi 1).range := by
  have hp := one_idempotent pi
  refine ⟨ContinuousLinearMap.IsIdempotentElem.isClosed_range hp, ?_⟩
  intro a x hx
  have hfix : pi 1 x = x :=
    LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hp) |>.mp hx
  have hmap (b : A) : pi b x ∈ (pi 1).range := by
    apply LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hp) |>.mpr
    calc
      pi 1 (pi b x) = (pi 1 * pi b) x := rfl
      _ = pi (1 * b) x := by rw [map_mul]
      _ = pi b x := by simp
  refine ⟨hmap a, ?_⟩
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star pi]
  exact hmap (star a)

theorem map_one_ne_zero_of_isNonzero
    (pi : NonUnitalRepresentation (A := A) (H := H)) (hpi : pi.IsNonzero) :
    pi 1 ≠ 0 := by
  obtain ⟨a, ha⟩ := hpi
  intro hzero
  apply ha
  calc
    pi a = pi (1 * a) := by rw [one_mul]
    _ = pi 1 * pi a := by rw [map_mul]
    _ = 0 := by rw [hzero, zero_mul]

/-- A nonzero irreducible representation of a unital algebra sends the unit
to the identity operator.  Nontriviality of `H` alone is not substituted for
nonzeroness of the representation. -/
theorem map_one_eq_one_of_isIrreducible
    (pi : NonUnitalRepresentation (A := A) (H := H))
    (hirr : pi.IsIrreducible) : pi 1 = 1 := by
  have hp := one_idempotent pi
  have hrange_ne : (pi 1).range ≠ (⊥ : Submodule ℂ H) := by
    intro hrange
    apply map_one_ne_zero_of_isNonzero pi hirr.1
    apply ContinuousLinearMap.ext
    intro x
    have hx : pi 1 x ∈ (pi 1).range := ⟨x, rfl⟩
    rw [hrange, Submodule.mem_bot] at hx
    simpa using hx
  have hrange : (pi 1).range = (⊤ : Submodule ℂ H) :=
    (hirr.2 (pi 1).range (reduces_range_one pi)).resolve_left hrange_ne
  apply ContinuousLinearMap.ext
  intro x
  have hx : x ∈ (pi 1).range := by rw [hrange]; trivial
  have hfix := LinearMap.IsIdempotentElem.mem_range_iff
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap hp) |>.mp hx
  simpa using hfix

/-- Bundle a nonzero irreducible nonunital representation as a unital star
representation after proving the unit equation. -/
noncomputable def toUnital (pi : NonUnitalRepresentation (A := A) (H := H))
    (hirr : pi.IsIrreducible) : A →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun := pi
  map_one' := map_one_eq_one_of_isIrreducible pi hirr
  map_mul' := map_mul pi
  map_zero' := map_zero pi
  map_add' := map_add pi
  commutes' c := by
    calc
      pi (algebraMap ℂ A c) = pi (c • (1 : A)) := by rw [Algebra.smul_def, mul_one]
      _ = c • pi 1 := map_smul pi c 1
      _ = algebraMap ℂ (H →L[ℂ] H) c := by
        rw [map_one_eq_one_of_isIrreducible pi hirr, Algebra.smul_def, mul_one]
  map_star' := map_star pi

@[simp]
theorem toUnital_apply (pi : NonUnitalRepresentation (A := A) (H := H))
    (hirr : pi.IsIrreducible) (a : A) : pi.toUnital hirr a = pi a :=
  rfl

/-- Passing a nonzero irreducible possibly nonunital representation through
`toUnital` preserves irreducibility.  The represented operators, their
adjoints, and hence all reducing subspaces are definitionally unchanged. -/
theorem isIrreducible_toUnital
    (pi : NonUnitalRepresentation (A := A) (H := H))
    (hirr : pi.IsIrreducible) :
    Representation.IsIrreducible (pi.toUnital hirr) := by
  refine ⟨hirr.1, ?_⟩
  intro K hK
  exact hirr.2 K hK

end NonUnitalRepresentation

namespace Representation

universe w

/-- Exact capture predicate for the ordinary nonzero, possibly nonunital
target quantifier.  Universe `w` is left polymorphic rather than restricting
the target Hilbert dimension. -/
def IsUniqueIrreducibleModelAmongNonUnital
    (pi : Representation A H) : Prop :=
  Function.Injective pi ∧ pi.IsIrreducible ∧
    ∀ (K : Type w) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K] (rho : NonUnitalRepresentation (A := A) (H := K)),
      ∀ hrho : rho.IsIrreducible, pi.UnitaryEquivalent (rho.toUnital hrho)

/-- A universal model for unital irreducible representations is already a
universal model for ordinary possibly nonunital nonzero irreducible
representations: irreducibility forces the latter to preserve the unit. -/
theorem IsUniqueIrreducibleModel.isUniqueIrreducibleModelAmongNonUnital
    {pi : Representation A H}
    (hpi : Representation.IsUniqueIrreducibleModel.{u, v, w} pi) :
    Representation.IsUniqueIrreducibleModelAmongNonUnital.{u, v, w} pi := by
  refine ⟨hpi.1, hpi.2.1, ?_⟩
  intro K _ _ _ rho hrho
  exact hpi.2.2 K (rho.toUnital hrho)
    (NonUnitalRepresentation.isIrreducible_toUnital rho hrho)

end Representation

end MathlibAnnex.Analysis.CStarAlgebra
