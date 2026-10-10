/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.SmallUnitary
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Adapters

/-!
# Exact unitary transport of two unit vectors

The finite-dimensional unitary below is a target for Kadison interpolation,
not an element assumed to belong to the represented algebra. A self-adjoint
logarithm on the two-vector span is extended by zero and lifted by the existing
exact interpolation theorem. Its exponential transports the vectors exactly.
The antipodal case is handled separately, so no global logarithm is assumed.

The algebra in this file is unital. The nonunital applications use its actual
canonical unitization and return their eventual witnesses to the original algebra.
-/

set_option autoImplicit false

noncomputable section

open NormedSpace
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra
namespace Representation

variable {A H : Type*} [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 800000 in
private theorem exists_unitary_apply_eq_of_norm_sub_lt_two [Nontrivial H]
    (pi : Representation A H) (hpi : pi.IsIrreducible)
    (xi eta : H) (hxi : ‖xi‖ = 1) (heta : ‖eta‖ = 1)
    (hdist : ‖xi - eta‖ < 2) :
    ∃ u : unitary A, pi (u : A) xi = eta := by
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
    intro hz
    have hzero : xi = 0 := congrArg Subtype.val hz
    simpa [hzero] using hxi
  letI : Nontrivial E := ⟨⟨xiE, 0, hxiEne⟩⟩
  letI : NormedRing (E →L[ℂ] E) := ContinuousLinearMap.toNormedRing
  obtain ⟨v, hv, hvnorm⟩ :=
    MathlibAnnex.Analysis.InnerProductSpace.exists_unitary_apply_eq_and_norm_sub_one_eq
      xiE etaE (by simpa [xiE] using hxi) (by simpa [etaE] using heta)
  have hvTwo : ‖(v : E →L[ℂ] E) - 1‖ < 2 := by
    rw [hvnorm]
    simpa [xiE, etaE] using hdist
  let t : selfAdjoint (E →L[ℂ] E) := Unitary.argSelfAdjoint v
  let T : H →L[ℂ] H := zeroExtension E (t : E →L[ℂ] E)
  have hTself : IsSelfAdjoint T :=
    isSelfAdjoint_zeroExtension E (t : E →L[ℂ] E) t.property
  have hTmap : Set.MapsTo T E E := mapsTo_zeroExtension E (t : E →L[ℂ] E)
  obtain ⟨a, ha, -, haeq⟩ := exists_selfAdjoint_norm_le_and_eq_on
    pi (isIrreducible_starAlgHom pi hpi) E T hTself
  let s : selfAdjoint A := ⟨a, ha⟩
  refine ⟨selfAdjoint.expUnitary s, ?_⟩
  calc
    pi (selfAdjoint.expUnitary s : A) xi = exp (Complex.I • T) xi :=
      MathlibAnnex.Analysis.CStarAlgebra.StarAlgHom.expUnitary_apply_eq_of_eqOn_of_mapsTo
        pi s T E haeq hTmap hxiE
    _ = (exp (Complex.I • (t : E →L[ℂ] E)) xiE : E) := by
      have hsmul : Complex.I • T =
          zeroExtension E (Complex.I • (t : E →L[ℂ] E)) := by
        ext z
        simp [T, zeroExtension, ContinuousLinearMap.comp_apply]
      rw [hsmul, exp_zeroExtension_apply E (Complex.I • (t : E →L[ℂ] E)) xiE]
    _ = eta := by
      have hlog : selfAdjoint.expUnitary t = v := expUnitary_argSelfAdjoint hvTwo
      have happ := congrArg (fun w : unitary (E →L[ℂ] E) =>
        (w : E →L[ℂ] E) xiE) hlog
      rw [selfAdjoint.expUnitary_coe] at happ
      exact congrArg Subtype.val (happ.trans hv)

/-- Exact two-vector unitary transitivity in a nonzero irreducible representation.
No faithfulness, separability, dimension, or closed-range hypothesis is used. -/
theorem exists_unitary_apply_eq_of_isIrreducible
    (pi : Representation A H) (hpi : pi.IsIrreducible)
    (xi eta : H) (hxi : ‖xi‖ = 1) (heta : ‖eta‖ = 1) :
    ∃ u : unitary A, pi (u : A) xi = eta := by
  letI : Nontrivial H := nontrivial_of_isNonzero pi hpi.1
  by_cases hdist : ‖xi - eta‖ < 2
  · exact exists_unitary_apply_eq_of_norm_sub_lt_two pi hpi xi eta hxi heta hdist
  have hdist' : ‖xi - (-eta)‖ < 2 := by
    have hadd := norm_add_sq (𝕜 := ℂ) xi eta
    have hsub := norm_sub_sq (𝕜 := ℂ) xi eta
    rw [hxi, heta] at hadd hsub
    have hlarge : 2 ≤ ‖xi - eta‖ := le_of_not_gt hdist
    have hlarge_sq : (2 : ℝ) ^ 2 ≤ ‖xi - eta‖ ^ 2 :=
      (sq_le_sq₀ (by norm_num) (norm_nonneg _)).2 hlarge
    have hsum_sq : ‖xi + eta‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖xi + eta‖]
    have hsmall : ‖xi + eta‖ < 2 := by
      rw [sq_eq_zero_iff.mp hsum_sq]
      norm_num
    simpa only [sub_neg_eq_add] using hsmall
  obtain ⟨u, hu⟩ := exists_unitary_apply_eq_of_norm_sub_lt_two
    pi hpi xi (-eta) hxi (by simpa using heta) hdist'
  let v : unitary A := ⟨-(u : A), by
    simpa only [Unitary.mem_iff, star_neg, neg_mul_neg] using u.property⟩
  refine ⟨v, ?_⟩
  change pi (-(u : A)) xi = eta
  rw [map_neg, ContinuousLinearMap.neg_apply, hu, neg_neg]

end Representation
end MathlibAnnex.Analysis.CStarAlgebra
