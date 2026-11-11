/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.CARConstruction
import Mathlib.Analysis.CStarAlgebra.Hom

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

open Set
open MathlibAnnex.Analysis.CStarAlgebra MathlibAnnex.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [Nontrivial A]

example (hA : IsAntiliminal A) :
    ∃ (D : NonUnitalStarSubalgebra ℂ A) (_hD : IsClosed (D : Set A)),
      ∃ q : D →⋆ₙₐ[ℂ] CAR.Limit, Function.Surjective q :=
  hA.exists_car_subquotient

example (hA : IsAntiliminal A) :
    ∃ (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosed (D : Set A)),
      letI : IsClosed (D : Set A) := hD
      ∃ (J : TwoSidedIdeal D) (hJ : IsClosed (J : Set D)), J ≠ ⊤ ∧
        Nonempty (ClosedIdealQuotient.Quotient J hJ ≃⋆ₐ[ℂ] CAR.Limit) :=
  hA.exists_car_quotient_equiv

-- Surjectivity is used on an arbitrary element of the fixed existing CAR model.
example (hA : IsAntiliminal A) (y : CAR.Limit) :
    ∃ (D : NonUnitalStarSubalgebra ℂ A) (_hD : IsClosed (D : Set A)),
      ∃ (q : D →⋆ₙₐ[ℂ] CAR.Limit) (x : D), q x = y := by
  obtain ⟨D, hD, q, hq⟩ := hA.exists_car_subquotient
  obtain ⟨x, hx⟩ := hq y
  exact ⟨D, hD, q, x, hx⟩

section
attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

private theorem quotient_equiv_preserves_norm {Q : Type*} [NonUnitalCStarAlgebra Q]
    (J : TwoSidedIdeal Q) (hJ : IsClosed (J : Set Q))
    (e : ClosedIdealQuotient.Quotient J hJ ≃⋆ₐ[ℂ] CAR.Limit) : ∀ z, ‖e z‖ = ‖z‖ := by
  letI : NonUnitalCStarAlgebra (ClosedIdealQuotient.Quotient J hJ) :=
    HomKernelQuotient.instNonUnitalCStarAlgebra (ClosedIdealQuotient.representation J hJ)
  exact NonUnitalStarAlgHom.norm_map e.toNonUnitalStarAlgHom e.toEquiv.injective
end

-- The quotient equivalence retains the original C-star quotient norm.
example (hA : IsAntiliminal A) :
    ∃ (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosed (D : Set A)),
      letI : IsClosed (D : Set A) := hD
      ∃ (J : TwoSidedIdeal D) (hJ : IsClosed (J : Set D))
        (e : ClosedIdealQuotient.Quotient J hJ ≃⋆ₐ[ℂ] CAR.Limit),
        ∀ z, ‖e z‖ = ‖z‖ := by
  obtain ⟨D, hD, hrest⟩ := hA.exists_car_quotient_equiv
  letI : IsClosed (D : Set A) := hD
  obtain ⟨J, hJ, _hproper, ⟨e⟩⟩ := hrest
  exact ⟨D, hD, J, hJ, e, quotient_equiv_preserves_norm (Q := ↥D) J hJ e⟩
