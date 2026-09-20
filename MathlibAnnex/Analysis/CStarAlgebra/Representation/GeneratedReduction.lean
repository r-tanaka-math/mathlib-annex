import MathlibAnnex.Analysis.CStarAlgebra.Representation.Basic

/-!
# Generic adjoint intertwining

The target-specific norm-closed generation lemmas live under
`MathlibAnnex.CStarAlgebra.AtomicConstruction.GeneratedReduction`; this generic module has no reverse dependency
on `MathlibAnnex.CStarAlgebra` or the KOS boundary.
-/

set_option autoImplicit false

noncomputable section

open scoped InnerProduct

namespace LinearIsometryEquiv

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A unitary intertwining relation automatically intertwines the adjoints. -/
theorem intertwines_adjoint (e : E ≃ₗᵢ[ℂ] F)
    {A : E →L[ℂ] E} {B : F →L[ℂ] F}
    (h : (e : E →L[ℂ] F).comp A = B.comp (e : E →L[ℂ] F)) :
    (e : E →L[ℂ] F).comp (A†) = (B†).comp (e : E →L[ℂ] F) := by
  have h' := congrArg ContinuousLinearMap.adjoint h
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    e.adjoint_eq_symm] at h'
  apply ContinuousLinearMap.ext
  intro x
  apply e.symm.injective
  have hx := congrArg (fun T : F →L[ℂ] E ↦ T (e x)) h'
  simpa [ContinuousLinearMap.comp_apply] using hx

end LinearIsometryEquiv
