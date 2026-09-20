import MathlibAnnex.Analysis.CStarAlgebra.SmallUnitary
import MathlibAnnex.Analysis.CStarAlgebra.State.CompactPhase

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open NormedSpace
open scoped CStarAlgebra ComplexOrder ComplexStarModule InnerProduct
namespace MathlibAnnex.Analysis.CStarAlgebra
variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

theorem StarAlgHom.exists_unitary_path_apply_eq_of_norm_sub_lt_two
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (xi eta : H) (hxi : ‖xi‖ = 1) (heta : ‖eta‖ = 1)
    (hdist : ‖xi - eta‖ < 2) :
    ∃ v : unitary A, ∃ p : Path 1 v, pi (v : A) xi = eta := by
  let E : Submodule ℂ H := Submodule.span ℂ {xi, eta}
  letI : FiniteDimensional ℂ E :=
    FiniteDimensional.span_of_finite ℂ (Set.toFinite {xi, eta})
  letI : E.HasOrthogonalProjection := inferInstance
  have hxiE : xi ∈ E := Submodule.subset_span (Set.mem_insert xi {eta})
  have hetaE : eta ∈ E :=
    Submodule.subset_span (Set.mem_insert_of_mem xi (Set.mem_singleton eta))
  let xiE : E := ⟨xi, hxiE⟩
  let etaE : E := ⟨eta, hetaE⟩
  have hxiEne : xiE ≠ 0 := by
    intro hzero
    have : xi = 0 := congrArg Subtype.val hzero
    rw [this, norm_zero] at hxi
    norm_num at hxi
  letI : Nontrivial E := ⟨⟨xiE, 0, hxiEne⟩⟩
  letI : NormedRing (E →L[ℂ] E) := ContinuousLinearMap.toNormedRing
  obtain ⟨u, huxi, hunorm⟩ :=
    MathlibAnnex.Analysis.InnerProductSpace.exists_unitary_apply_eq_and_norm_sub_one_eq
      xiE etaE (by simpa [xiE] using hxi) (by simpa [etaE] using heta)
  have huTwo : ‖(u : E →L[ℂ] E) - 1‖ < 2 := by
    rw [hunorm]
    exact hdist
  let t : selfAdjoint (E →L[ℂ] E) := Unitary.argSelfAdjoint u
  let T : H →L[ℂ] H := zeroExtension E (t : E →L[ℂ] E)
  have hTself : IsSelfAdjoint T :=
    isSelfAdjoint_zeroExtension E (t : E →L[ℂ] E) t.property
  have hTmap : Set.MapsTo T E E :=
    mapsTo_zeroExtension E (t : E →L[ℂ] E)
  obtain ⟨h, hhself, _hhnorm, hheq⟩ :=
    exists_selfAdjoint_norm_le_two_mul_and_eq_on pi hpi E T hTself
  let hs : selfAdjoint A := ⟨h, hhself⟩
  let v : unitary A := selfAdjoint.expUnitary hs
  let p : Path 1 v := selfAdjoint.expUnitaryPathToOne hs
  refine ⟨v, p, ?_⟩
  calc
    pi (v : A) xi = exp (Complex.I • T) xi :=
      MathlibAnnex.Analysis.CStarAlgebra.StarAlgHom.expUnitary_apply_eq_of_eqOn_of_mapsTo
        pi hs T E hheq hTmap hxiE
    _ = (exp (Complex.I • (t : E →L[ℂ] E)) xiE : E) := by
      have hsmul : Complex.I • T =
          zeroExtension E (Complex.I • (t : E →L[ℂ] E)) := by
        ext z
        simp [T, zeroExtension, ContinuousLinearMap.comp_apply]
      rw [hsmul, exp_zeroExtension_apply E (Complex.I • (t : E →L[ℂ] E)) xiE]
    _ = eta := by
      have hlog : selfAdjoint.expUnitary t = u := expUnitary_argSelfAdjoint huTwo
      have happ := congrArg (fun q : unitary (E →L[ℂ] E) =>
        (q : E →L[ℂ] E) xiE) hlog
      rw [selfAdjoint.expUnitary_coe] at happ
      exact congrArg Subtype.val (happ.trans huxi)
end MathlibAnnex.Analysis.CStarAlgebra
