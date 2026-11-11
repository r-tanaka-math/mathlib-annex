/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.Corner
import MathlibAnnex.Algebra.Star.ProjectionEquivalence

/-!
# Abelian projections and type I von Neumann algebras

All corner variables, subprojections, and equivalence witnesses belong to
the specified algebra. A projection is abelian when its algebraic corner
is commutative; the zero projection is allowed. Type I means that every
nonzero projection dominates a nonzero abelian projection.

The algebraic equation `q * p = q` records the order on projections. The
standard order interpretation is supplied by the projection-order API.
No factor, separability, or finite-dimensionality hypothesis is used here.
-/

set_option autoImplicit false

namespace VonNeumannAlgebra

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A projection whose internal corner is commutative. Zero is permitted. -/
def IsAbelianProjection (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra) : Prop :=
  IsStarProjection p ∧
    ∀ a b : M.toStarSubalgebra,
      p * a = a → a * p = a → p * b = b → b * p = b → a * b = b * a

/-- Every nonzero projection in the algebra dominates a nonzero abelian
projection in the same algebra. -/
def IsTypeI (M : VonNeumannAlgebra H) : Prop :=
  ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q : M.toStarSubalgebra, IsAbelianProjection M q ∧ q ≠ 0 ∧ q * p = q

/-- The type I condition restricted to subprojections of a specified
projection. This is the projection formulation for the corner with unit `p`. -/
def IsTypeIProjection (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra) : Prop :=
  IsStarProjection p ∧
    ∀ q : M.toStarSubalgebra, IsStarProjection q → q ≠ 0 → q * p = q →
      ∃ r : M.toStarSubalgebra, IsAbelianProjection M r ∧ r ≠ 0 ∧ r * q = r

namespace IsAbelianProjection

variable {M : VonNeumannAlgebra H} {p q : M.toStarSubalgebra}

theorem isStarProjection (hp : IsAbelianProjection M p) : IsStarProjection p := hp.1

theorem mul_comm (hp : IsAbelianProjection M p) {a b : M.toStarSubalgebra}
    (hpa : p * a = a) (hap : a * p = a) (hpb : p * b = b) (hbp : b * p = b) :
    a * b = b * a := hp.2 a b hpa hap hpb hbp

/-- A subprojection of an abelian projection is abelian in the same algebra. -/
theorem of_mul_eq_self (hp : IsAbelianProjection M p)
    (hq : IsStarProjection q) (hqp : q * p = q) : IsAbelianProjection M q := by
  have hpq : p * q = q := by
    simpa only [star_mul, hp.1.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
      using congrArg star hqp
  refine ⟨hq, ?_⟩
  intro a b hqa haq hqb hbq
  have lift_left (x : M.toStarSubalgebra) (hqx : q * x = x) : p * x = x := by
    calc
      p * x = p * (q * x) := by rw [hqx]
      _ = (p * q) * x := (mul_assoc _ _ _).symm
      _ = x := by rw [hpq, hqx]
  have lift_right (x : M.toStarSubalgebra) (hxq : x * q = x) : x * p = x := by
    calc
      x * p = (x * q) * p := by rw [hxq]
      _ = x * (q * p) := mul_assoc _ _ _
      _ = x := by rw [hqp, hxq]
  exact hp.mul_comm (lift_left a hqa) (lift_right a haq)
    (lift_left b hqb) (lift_right b hbq)

/-- Equivalence transports the corner by `a ↦ v*a*v⁎`; in particular,
abelianness is invariant under an internal partial isometry. -/
theorem of_equivalent (hp : IsAbelianProjection M p)
    (hpq : MurrayVonNeumannEquivalent p q) : IsAbelianProjection M q := by
  obtain ⟨e⟩ := nonempty_cornerEquiv_of_equivalent M hpq
  refine ⟨hpq.2.1, ?_⟩
  intro a b hqa haq hqb hbq
  let aQ : corner M q hpq.2.1 := ⟨a, hqa, haq⟩
  let bQ : corner M q hpq.2.1 := ⟨b, hqb, hbq⟩
  have hcomm : e.symm aQ * e.symm bQ = e.symm bQ * e.symm aQ := by
    apply Subtype.ext
    exact hp.mul_comm (e.symm aQ).property.1 (e.symm aQ).property.2
      (e.symm bQ).property.1 (e.symm bQ).property.2
  have h : aQ * bQ = bQ * aQ := by
    simpa only [map_mul, e.apply_symm_apply] using congrArg e hcomm
  exact congrArg Subtype.val h

/-- Abelian corners satisfy the local type I condition. -/
theorem isTypeIProjection (hp : IsAbelianProjection M p) : IsTypeIProjection M p := by
  refine ⟨hp.1, ?_⟩
  intro q hq hq0 hqp
  exact ⟨q, hp.of_mul_eq_self hq hqp, hq0, hq.isIdempotentElem.eq⟩

end IsAbelianProjection

@[simp]
theorem isAbelianProjection_zero (M : VonNeumannAlgebra H) :
    IsAbelianProjection M 0 := by
  refine ⟨IsStarProjection.zero _, ?_⟩
  intro a b hzeroa _ _ _
  have ha : a = 0 := by simpa only [zero_mul] using hzeroa.symm
  simp only [ha, zero_mul, mul_zero]

/-- The absorption definition is exactly commutativity of the canonical
nonunital corner; its distinguished identity is `p`. -/
theorem isAbelianProjection_iff_corner_commutative (M : VonNeumannAlgebra H)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p) :
    IsAbelianProjection M p ↔
      ∀ a b : corner M p hp, a * b = b * a := by
  constructor
  · intro h a b
    apply Subtype.ext
    exact h.mul_comm a.property.1 a.property.2 b.property.1 b.property.2
  · intro h
    refine ⟨hp, ?_⟩
    intro a b hpa hap hpb hbp
    exact congrArg Subtype.val (h ⟨a, hpa, hap⟩ ⟨b, hpb, hbp⟩)

theorem isAbelianProjection_of_commutative (M : VonNeumannAlgebra H)
    (hcomm : ∀ a b : M.toStarSubalgebra, a * b = b * a)
    {p : M.toStarSubalgebra} (hp : IsStarProjection p) : IsAbelianProjection M p :=
  ⟨hp, fun a b _ _ _ _ ↦ hcomm a b⟩

/-- Every commutative concrete von Neumann algebra is type I, including
the algebra acting on the zero Hilbert space. -/
theorem isTypeI_of_commutative (M : VonNeumannAlgebra H)
    (hcomm : ∀ a b : M.toStarSubalgebra, a * b = b * a) : IsTypeI M := by
  intro p hp hp0
  exact ⟨p, isAbelianProjection_of_commutative M hcomm hp, hp0,
    hp.isIdempotentElem.eq⟩

theorem isTypeI_of_subsingleton (M : VonNeumannAlgebra H)
    [Subsingleton M.toStarSubalgebra] : IsTypeI M := by
  intro p _ hp0
  exact (hp0 (Subsingleton.elim p 0)).elim

@[simp]
theorem isTypeIProjection_zero (M : VonNeumannAlgebra H) :
    IsTypeIProjection M 0 := (isAbelianProjection_zero M).isTypeIProjection

theorem IsTypeI.isTypeIProjection {M : VonNeumannAlgebra H} (hM : IsTypeI M)
    {p : M.toStarSubalgebra} (hp : IsStarProjection p) : IsTypeIProjection M p :=
  ⟨hp, fun q hq hq0 _ ↦ hM q hq hq0⟩

theorem IsTypeIProjection.of_mul_eq_self {M : VonNeumannAlgebra H}
    {p q : M.toStarSubalgebra} (hp : IsTypeIProjection M p)
    (hq : IsStarProjection q) (hqp : q * p = q) : IsTypeIProjection M q := by
  refine ⟨hq, ?_⟩
  intro r hr hr0 hrq
  apply hp.2 r hr hr0
  calc
    r * p = (r * q) * p := by rw [hrq]
    _ = r * (q * p) := mul_assoc _ _ _
    _ = r := by rw [hqp, hrq]

theorem isTypeI_iff_one (M : VonNeumannAlgebra H) :
    IsTypeI M ↔ IsTypeIProjection M 1 := by
  constructor
  · intro h
    exact h.isTypeIProjection (IsStarProjection.one _)
  · intro h p hp hp0
    exact h.2 p hp hp0 (mul_one p)

/-- An internal isomorphism transports the abelian-corner predicate. -/
theorem isAbelianProjection_map_iff
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra) (p : M.toStarSubalgebra) :
    IsAbelianProjection N (e p) ↔ IsAbelianProjection M p := by
  have inj : Function.Injective (fun a : M.toStarSubalgebra => e a) := e.injective
  have forward : ∀ (p : M.toStarSubalgebra), IsAbelianProjection M p →
      IsAbelianProjection N (e p) := by
    intro p hp
    refine ⟨hp.1.map e, ?_⟩
    intro a b hpa hap hpb hbp
    have pull (x : N.toStarSubalgebra) (hleft : e p * x = x)
        (hright : x * e p = x) :
        p * e.symm x = e.symm x ∧ e.symm x * p = e.symm x := by
      constructor
      · apply inj
        simpa only [map_mul, e.apply_symm_apply] using hleft
      · apply inj
        simpa only [map_mul, e.apply_symm_apply] using hright
    have ha := pull a hpa hap
    have hb := pull b hpb hbp
    have h := congrArg e (hp.mul_comm ha.1 ha.2 hb.1 hb.2)
    simpa only [map_mul, e.apply_symm_apply] using h
  constructor
  · intro hp
    refine ⟨?_, ?_⟩
    · have h : IsStarProjection (e.symm (e p)) := hp.1.map e.symm.toNonUnitalStarAlgHom
      simpa only [e.symm_apply_apply] using h
    · intro a b hpa hap hpb hbp
      apply inj
      simp only [map_mul]
      apply hp.mul_comm
      · simpa only [map_mul] using congrArg e hpa
      · simpa only [map_mul] using congrArg e hap
      · simpa only [map_mul] using congrArg e hpb
      · simpa only [map_mul] using congrArg e hbp
  · exact forward p

/-- Type I is invariant under actual star-algebra equivalence of the
underlying von Neumann algebras. No existence theorem is assumed here. -/
theorem IsTypeI.map
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K} (hM : IsTypeI M)
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra) : IsTypeI N := by
  intro p hp hp0
  have hp' : IsStarProjection (e.symm p) := hp.map e.symm
  have hp0' : e.symm p ≠ 0 := by
    intro h
    apply hp0
    simpa only [e.apply_symm_apply, map_zero] using congrArg e h
  obtain ⟨q, hq, hq0, hqp⟩ := hM (e.symm p) hp' hp0'
  refine ⟨e q, (isAbelianProjection_map_iff M N e q).mpr hq, ?_, ?_⟩
  · intro h
    apply hq0
    exact e.injective (h.trans (map_zero e).symm)
  · simpa only [map_mul, e.apply_symm_apply] using congrArg e hqp

end VonNeumannAlgebra
