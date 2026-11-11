import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeDecomposition
import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeII1

set_option autoImplicit false

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A consumer of the three typed central components, including their
actual orthogonality equations and sum, with no factor or countability input. -/
example (M : VonNeumannAlgebra H) :
    ∃ p q r : M.toStarSubalgebra,
      VonNeumannAlgebra.IsTypeIProjection M p ∧
      VonNeumannAlgebra.IsTypeIIProjection M q ∧
      VonNeumannAlgebra.IsTypeIIIProjection M r ∧
      (∀ a : M.toStarSubalgebra, a * p = p * a ∧ a * q = q * a ∧ a * r = r * a) ∧
      p * q = 0 ∧ p * r = 0 ∧ q * r = 0 ∧ p + q + r = 1 := by
  obtain ⟨p, q, r, hp, hq, hr, hc, hpq, hpr, hqr, hsum, _, _, _, _⟩ :=
    VonNeumannAlgebra.exists_type_decomposition M
  exact ⟨p, q, r, hp, hq, hr, hc, hpq, hpr, hqr, hsum⟩

/-- Any triple with the three actual type conditions and sum one is the
canonical triple. No centrality or orthogonality premise is silently supplied. -/
example (M : VonNeumannAlgebra H) (p q r : M.toStarSubalgebra)
    (hp : VonNeumannAlgebra.IsTypeIProjection M p)
    (hq : VonNeumannAlgebra.IsTypeIIProjection M q)
    (hr : VonNeumannAlgebra.IsTypeIIIProjection M r)
    (hsum : p + q + r = 1) :
    p = VonNeumannAlgebra.abelianCentralSupport M ∧
      q = VonNeumannAlgebra.typeIIProjection M ∧
      r = VonNeumannAlgebra.typeIIIProjection M :=
  VonNeumannAlgebra.type_decomposition_unique
    (M := M) (p := p) (q := q) (r := r) (hp := hp) (hq := hq) (hr := hr) (hsum := hsum)

/-- The equivalence has the literal three corner carriers and inverse addition. -/
example (M : VonNeumannAlgebra H) (a : M.toStarSubalgebra) :
    (((VonNeumannAlgebra.typeDecompositionEquiv M) a).1 : M.toStarSubalgebra) +
    (((VonNeumannAlgebra.typeDecompositionEquiv M) a).2.1 : M.toStarSubalgebra) +
    (((VonNeumannAlgebra.typeDecompositionEquiv M) a).2.2 : M.toStarSubalgebra) = a := by
  exact (VonNeumannAlgebra.typeDecompositionEquiv M).symm_apply_apply a

example (M : VonNeumannAlgebra H) :
    Isometry (VonNeumannAlgebra.typeDecompositionEquiv M) :=
  VonNeumannAlgebra.isometry_typeDecompositionEquiv M

/-- This consumes the type III definition itself: the witness is an
internal finite subprojection, so it must be zero. -/
example (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra)
    (hp : IsFiniteProjection p)
    (hsub : p * VonNeumannAlgebra.typeIIIProjection M = p) : p = 0 :=
  (VonNeumannAlgebra.isTypeIIIProjection_typeIIIProjection M).2 p hp hsub

example (M : VonNeumannAlgebra H) (hcomm : ∀ a b : M.toStarSubalgebra, a * b = b * a) :
    VonNeumannAlgebra.abelianCentralSupport M = 1 ∧
    VonNeumannAlgebra.typeIIProjection M = 0 ∧
    VonNeumannAlgebra.typeIIIProjection M = 0 := by
  have hI := VonNeumannAlgebra.isTypeI_of_commutative M hcomm
  exact ⟨hI.abelianCentralSupport_eq_one, hI.typeIIProjection_eq_zero,
    hI.isSemifinite.typeIIIProjection_eq_zero⟩

/-- The accepted II₁-factor input implies semifiniteness. No unproved
identification with the general type II predicate is used. -/
example (M : VonNeumannAlgebra H) (hM : M.IsTypeII1) :
    VonNeumannAlgebra.typeIIIProjection M = 0 :=
  hM.2.1.isSemifinite.typeIIIProjection_eq_zero

/-- Empty central components are legitimate, including on a zero space. -/
example (M : VonNeumannAlgebra H) [Subsingleton M.toStarSubalgebra] :
    VonNeumannAlgebra.abelianCentralSupport M = 0 ∧
    VonNeumannAlgebra.typeIIProjection M = 0 ∧
    VonNeumannAlgebra.typeIIIProjection M = 0 :=
  ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
