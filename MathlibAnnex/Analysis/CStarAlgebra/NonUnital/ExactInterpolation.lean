import MathlibAnnex.Analysis.CStarAlgebra.ExactInterpolation
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.Representation
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Adapters

/-!
# Exact interpolation in corners of genuinely nonunital C-star algebras

The canonical unitization is used only as a proof device.  Sandwiched
witnesses have zero scalar coordinate, so the returned interpolant belongs
to the original algebra without subtracting a scalar term.
-/

set_option autoImplicit false

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace NonUnitalCStarRepresentation

/-- Sharp self-adjoint interpolation in a projection corner of a genuinely
nonunital C-star algebra.  The output-support condition is required only on
the finite subspace on which interpolation is requested. -/
theorem exists_cornerSupported_selfAdjoint_norm_le_and_eq_on_of_apply
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    {e : A} (he : IsStarProjection e)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (hE : ∀ x : H, x ∈ E → pi e x = x)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hTE : ∀ x : H, x ∈ E → pi e (T x) = T x) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      e * a = a ∧ a * e = a ∧ ∀ x : H, x ∈ E → pi a x = T x := by
  letI : Nontrivial H := pi.nontrivial_of_isNonzero hpi.1
  let eU : Unitization ℂ A := e
  have heU : IsStarProjection eU := he.inr
  have hEU : ∀ x : H, x ∈ E → pi.unitization eU x = x := by
    intro x hx
    simpa [eU] using hE x hx
  have hTEU : ∀ x : H, x ∈ E → pi.unitization eU (T x) = T x := by
    intro x hx
    simpa [eU] using hTE x hx
  obtain ⟨b, hbself, hbnorm, hbleft, hbright, hbexact⟩ :=
    MathlibAnnex.Analysis.CStarAlgebra.StarAlgHom.exists_cornerSupported_selfAdjoint_norm_le_and_eq_on_of_apply
      pi.unitization
        (Representation.isIrreducible_starAlgHom pi.unitization
          (isIrreducible_unitization pi hpi))
        heU E hEU T hT hTEU
  have hbfst : b.fst = 0 := by
    have h := congrArg (fun z : Unitization ℂ A => z.fst) hbleft
    simpa [eU] using h.symm
  let a : A := b.snd
  have hb_eq : b = (a : Unitization ℂ A) := by
    apply Unitization.ext
    · simpa [a] using hbfst
    · rfl
  have haself : IsSelfAdjoint a := by
    apply IsSelfAdjoint.of_inr (R := ℂ)
    rwa [← hb_eq]
  have hanorm : ‖a‖ ≤ ‖T‖ := by
    rw [hb_eq, Unitization.norm_inr] at hbnorm
    exact hbnorm
  have haleft : e * a = a := by
    apply Unitization.inr_injective (R := ℂ)
    simpa [hb_eq] using hbleft
  have haright : a * e = a := by
    apply Unitization.inr_injective (R := ℂ)
    simpa [hb_eq] using hbright
  refine ⟨a, haself, hanorm, haleft, haright, ?_⟩
  intro x hx
  simpa [hb_eq] using hbexact x hx

/-- Sharp positive interpolation in a projection corner of a genuinely
nonunital C-star algebra. -/
theorem exists_cornerSupported_nonneg_norm_le_and_eq_on_of_apply
    [PartialOrder A] [StarOrderedRing A]
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    {e : A} (he : IsStarProjection e)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (hE : ∀ x : H, x ∈ E → pi e x = x)
    (T : H →L[ℂ] H) (hT : 0 ≤ T)
    (hTE : ∀ x : H, x ∈ E → pi e (T x) = T x) :
    ∃ a : A, 0 ≤ a ∧ ‖a‖ ≤ ‖T‖ ∧
      e * a = a ∧ a * e = a ∧ ∀ x : H, x ∈ E → pi a x = T x := by
  letI : Nontrivial H := pi.nontrivial_of_isNonzero hpi.1
  let eU : Unitization ℂ A := e
  have heU : IsStarProjection eU := he.inr
  have hEU : ∀ x : H, x ∈ E → pi.unitization eU x = x := by
    intro x hx
    simpa [eU] using hE x hx
  have hTEU : ∀ x : H, x ∈ E → pi.unitization eU (T x) = T x := by
    intro x hx
    simpa [eU] using hTE x hx
  obtain ⟨b, hbnonneg, hbnorm, hbleft, hbright, hbexact⟩ :=
    MathlibAnnex.Analysis.CStarAlgebra.StarAlgHom.exists_cornerSupported_nonneg_norm_le_and_eq_on_of_apply
      pi.unitization
        (Representation.isIrreducible_starAlgHom pi.unitization
          (isIrreducible_unitization pi hpi))
        heU E hEU T hT hTEU
  have hbfst : b.fst = 0 := by
    have h := congrArg (fun z : Unitization ℂ A => z.fst) hbleft
    simpa [eU] using h.symm
  let a : A := b.snd
  have hb_eq : b = (a : Unitization ℂ A) := by
    apply Unitization.ext
    · simpa [a] using hbfst
    · rfl
  have hanonneg : 0 ≤ a := by
    apply Unitization.inr_nonneg_iff.mp
    rwa [← hb_eq]
  have hanorm : ‖a‖ ≤ ‖T‖ := by
    rw [hb_eq, Unitization.norm_inr] at hbnorm
    exact hbnorm
  have haleft : e * a = a := by
    apply Unitization.inr_injective (R := ℂ)
    simpa [hb_eq] using hbleft
  have haright : a * e = a := by
    apply Unitization.inr_injective (R := ℂ)
    simpa [hb_eq] using hbright
  refine ⟨a, hanonneg, hanorm, haleft, haright, ?_⟩
  intro x hx
  simpa [hb_eq] using hbexact x hx

/-- Positive-contraction specialization of genuinely nonunital sharp corner
interpolation. -/
theorem exists_cornerSupported_positive_contraction_eq_on_of_apply
    [PartialOrder A] [StarOrderedRing A]
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    {e : A} (he : IsStarProjection e)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (hE : ∀ x : H, x ∈ E → pi e x = x)
    (T : H →L[ℂ] H) (hT : 0 ≤ T) (hTnorm : ‖T‖ ≤ 1)
    (hTE : ∀ x : H, x ∈ E → pi e (T x) = T x) :
    ∃ a : A, 0 ≤ a ∧ ‖a‖ ≤ 1 ∧
      e * a = a ∧ a * e = a ∧ ∀ x : H, x ∈ E → pi a x = T x := by
  obtain ⟨a, ha, hanorm, haleft, haright, haexact⟩ :=
    exists_cornerSupported_nonneg_norm_le_and_eq_on_of_apply
      pi hpi he E hE T hT hTE
  exact ⟨a, ha, hanorm.trans hTnorm, haleft, haright, haexact⟩

end NonUnitalCStarRepresentation

end MathlibAnnex.Analysis.CStarAlgebra
