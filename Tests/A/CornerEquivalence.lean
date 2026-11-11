/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.Hereditary.CornerEquivalence

set_option autoImplicit false
noncomputable section

open MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]

-- No unit, separability, norm bound, or partial-isometry hypothesis on v.
example {c v : A} (hc : IsSelfAdjoint c) (hv : star v * v * c = c) :
    hereditarySubalgebra c ≃⋆ₐ[ℂ] hereditarySubalgebra (v * c * star v) :=
  hereditaryConjugateEquiv (c := c) (v := v) hc hv

-- The map is the stated ambient conjugation on arbitrary closed-corner elements.
example {c v : A} (hc : IsSelfAdjoint c) (hv : star v * v * c = c)
    (z : hereditarySubalgebra c) :
    (hereditaryConjugateEquiv hc hv z : A) = v * (z : A) * star v :=
  coe_hereditaryConjugateEquiv hc hv z

-- The inverse has the opposite ambient formula, not an ambient inverse of v.
example {c v : A} (hc : IsSelfAdjoint c) (hv : star v * v * c = c)
    (w : hereditarySubalgebra (v * c * star v)) :
    ((hereditaryConjugateEquiv hc hv).symm w : A) = star v * (w : A) * v :=
  coe_hereditaryConjugateEquiv_symm hc hv w

-- Surjectivity is onto the full hereditary target, including closure elements.
example {c v : A} (hc : IsSelfAdjoint c) (hv : star v * v * c = c)
    (w : hereditarySubalgebra (v * c * star v)) :
    ∃ z : hereditarySubalgebra c, hereditaryConjugateHom hc hv z = w := by
  exact (hereditaryConjugateEquiv hc hv).surjective w

-- Norm equality uses the inherited norm of the original nonunital C-star algebra.
example {c v z : A} (hc : IsSelfAdjoint c) (hv : star v * v * c = c)
    (hz : z ∈ hereditarySubalgebra c) : ‖v * z * star v‖ = ‖z‖ :=
  norm_conjugate_of_mem_hereditarySubalgebra hc hv hz

-- A generator annihilation identity controls the entire hereditary algebra.
example {c v z : A} (hc : IsSelfAdjoint c) (hcv : c * v = 0)
    (hz : z ∈ hereditarySubalgebra c) : z * v = 0 := by
  apply mul_eq_zero_of_mem_hereditarySubalgebra_right (a := c) (e := v) _ hz
  simpa only [hc.star_eq] using hcv

-- The exact product law transports sibling products with the same link.
example {c v z w : A} (hv : star v * v * c = c)
    (hw : w ∈ hereditarySubalgebra c) (hzw : z * w = 0) :
    (v * z * star v) * (v * w * star v) = 0 := by
  rw [conjugate_mul_conjugate_of_mem_hereditarySubalgebra hv hw, hzw, mul_zero, zero_mul]

-- The isometry assertion is a typed consumer of the proved bijective homomorphism.
example {c v : A} (hc : IsSelfAdjoint c) (hv : star v * v * c = c) :
    Isometry (hereditaryConjugateEquiv (c := c) (v := v) hc hv) :=
  isometry_hereditaryConjugateEquiv hc hv
