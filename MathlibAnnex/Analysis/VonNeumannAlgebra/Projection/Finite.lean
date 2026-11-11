/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Algebra.Star.ProjectionEquivalence
import MathlibAnnex.Analysis.VonNeumannAlgebra.Finite
import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.Corner

/-!
# Finite projections and the finite unit

Finiteness is expressed using equivalence in the specified star ring.  The
order on projections is written algebraically as `q * p = q`; no ambient
operator witness is admitted by this definition.

The existing `VonNeumannAlgebra.IsFinite` is preserved and identified with
finiteness of the unit of the algebra subtype. Finiteness is reflected by
injective multiplicative star maps and preserved by bijective such maps.
Internal projection equivalence preserves finiteness via the actual corner
equivalence, whose units are the endpoint projections.
-/

set_option autoImplicit false

universe u v

section NonUnitalRing

variable {R : Type u} [NonUnitalRing R] [StarRing R]

/-- A finite projection has no proper subprojection equivalent to it in `R`. -/
def IsFiniteProjection (p : R) : Prop :=
  IsStarProjection p ∧
    ∀ q : R, MurrayVonNeumannEquivalent p q → q * p = q → q = p

/-- A nonzero properly infinite projection contains two orthogonal
subprojections, each equivalent to it inside the same ring. -/
def IsProperlyInfiniteProjection (p : R) : Prop :=
  IsStarProjection p ∧ p ≠ 0 ∧
    ∃ r s : R, MurrayVonNeumannEquivalent p r ∧
      MurrayVonNeumannEquivalent p s ∧ r * p = r ∧ s * p = s ∧ r * s = 0

namespace IsFiniteProjection

variable {p q : R}

theorem isStarProjection (hp : IsFiniteProjection p) : IsStarProjection p := hp.1

theorem eq_of_equivalent_of_mul_eq (hp : IsFiniteProjection p)
    (hpq : MurrayVonNeumannEquivalent p q) (hqp : q * p = q) : q = p :=
  hp.2 q hpq hqp

@[simp]
theorem zero : IsFiniteProjection (0 : R) := by
  refine ⟨IsStarProjection.zero R, ?_⟩
  intro q _ hq
  simpa only [mul_zero] using hq.symm

/-- A subprojection of a finite projection is finite.  The proof adjoins
the same orthogonal complement to both sides of the equivalence. -/
theorem of_mul_eq_left (hp : IsFiniteProjection p) (hq : IsStarProjection q)
    (hqp : q * p = q) : IsFiniteProjection q := by
  refine ⟨hq, ?_⟩
  intro r hqr hrq
  have hrp : r * p = r := by
    calc
      r * p = (r * q) * p := by rw [hrq]
      _ = r * (q * p) := mul_assoc _ _ _
      _ = r := by rw [hqp, hrq]
  have hd : IsStarProjection (p - q) := hq.sub_of_mul_eq_left hp.1 hqp
  have hqd : q * (p - q) = 0 := by
    rw [mul_sub, hqp, hq.isIdempotentElem.eq, sub_self]
  have hrd : r * (p - q) = 0 := by rw [mul_sub, hrp, hrq, sub_self]
  have hqplus : q + (p - q) = p := by rw [add_comm, sub_add_cancel]
  have hsum : MurrayVonNeumannEquivalent p (r + (p - q)) := by
    simpa only [hqplus] using
      hqr.add (MurrayVonNeumannEquivalent.refl hd) hqd hrd
  have hsumle : (r + (p - q)) * p = r + (p - q) := by
    rw [add_mul, sub_mul, hrp, hp.1.isIdempotentElem.eq, hqp]
  have heq : r + (p - q) = p := hp.2 _ hsum hsumle
  exact add_right_cancel (heq.trans hqplus.symm)

/-- The algebraic corner commutativity condition already forces its unit
projection to be finite.  All the elements used below belong to `R`. -/
theorem of_commutative_corner (hp : IsStarProjection p)
    (hcomm : ∀ a b : R, p * a = a → a * p = a →
      p * b = b → b * p = b → a * b = b * a) :
    IsFiniteProjection p := by
  refine ⟨hp, ?_⟩
  intro q hpq hqp
  rcases hpq with ⟨_, hq, v, hv, hvi, hvf⟩
  have hvpi : v * p = v := by
    rw [← hvi, ← mul_assoc]
    exact hv
  have hqv : q * v = v := by
    rw [← hvf]
    exact hv
  have hpq : p * q = q := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq,
      hq.isSelfAdjoint.star_eq] using congrArg star hqp
  have hpv : p * v = v := by
    calc
      p * v = p * (q * v) := by rw [hqv]
      _ = (p * q) * v := (mul_assoc _ _ _).symm
      _ = v := by rw [hpq, hqv]
  have hpvs : p * star v = star v := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hvpi
  have hvsp : star v * p = star v := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hpv
  calc
    q = v * star v := hvf.symm
    _ = star v * v := hcomm v (star v) hpv hvpi hpvs hvsp
    _ = p := hvi

/-- In a commutative ring every star projection is finite. -/
theorem of_commutative (hp : IsStarProjection p)
    (hcomm : ∀ a b : R, a * b = b * a) : IsFiniteProjection p :=
  of_commutative_corner hp (fun a b _ _ _ _ ↦ hcomm a b)

theorem not_isProperlyInfiniteProjection (hp : IsFiniteProjection p) :
    ¬ IsProperlyInfiniteProjection p := by
  rintro ⟨_, hp0, r, s, hr, hs, hrp, hsp, hrs⟩
  have hr' : r = p := hp.2 r hr hrp
  have hs' : s = p := hp.2 s hs hsp
  rw [hr', hs', hp.1.isIdempotentElem.eq] at hrs
  exact hp0 hrs

end IsFiniteProjection

namespace IsProperlyInfiniteProjection

variable {p : R}

theorem isStarProjection (hp : IsProperlyInfiniteProjection p) :
    IsStarProjection p := hp.1

theorem ne_zero (hp : IsProperlyInfiniteProjection p) : p ≠ 0 := hp.2.1

theorem not_isFiniteProjection (hp : IsProperlyInfiniteProjection p) :
    ¬ IsFiniteProjection p := fun hfin ↦ hfin.not_isProperlyInfiniteProjection hp

end IsProperlyInfiniteProjection

end NonUnitalRing

namespace IsFiniteProjection

section Maps

variable {R : Type u} {S : Type v} [NonUnitalRing R] [StarRing R]
  [NonUnitalRing S] [StarRing S] {F : Type*} [FunLike F R S]
  [MulHomClass F R S] [StarHomClass F R S] {p : R}

/-- Finiteness is reflected by an injective multiplicative star map: every
source witness maps to a target witness, and equality reflects back. -/
theorem of_map (f : F) (hf : Function.Injective f)
    (hp : IsFiniteProjection (f p)) : IsFiniteProjection p := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change p * p = p
    apply hf
    simpa only [map_mul] using hp.1.isIdempotentElem.eq
  · change star p = p
    apply hf
    simpa only [map_star] using hp.1.isSelfAdjoint.star_eq
  · intro q hpq hqp
    apply hf
    exact hp.2 (f q) (hpq.map f) (by
      simpa only [map_mul] using congrArg f hqp)

/-- A bijective multiplicative star map preserves finiteness. Surjectivity
is used both for the target subprojection and for its equivalence witness. -/
protected theorem map (hp : IsFiniteProjection p) (f : F)
    (hf : Function.Bijective f) : IsFiniteProjection (f p) := by
  refine ⟨hp.1.map f, ?_⟩
  intro s hps hsp
  obtain ⟨q, rfl⟩ := hf.2 s
  have hpq : MurrayVonNeumannEquivalent p q :=
    MurrayVonNeumannEquivalent.of_map f hf hps
  have hqp : q * p = q := hf.1 (by simpa only [map_mul] using hsp)
  exact congrArg f (hp.2 q hpq hqp)

theorem map_iff (f : F) (hf : Function.Bijective f) :
    IsFiniteProjection (f p) ↔ IsFiniteProjection p :=
  ⟨of_map f hf.1, fun hp ↦ hp.map f hf⟩

end Maps

end IsFiniteProjection

section Ring

variable {R : Type u} [Ring R] [StarRing R]

/-- Finiteness of the unit is exactly the isometry-to-unitary property.
No proper-star assumption is required for this algebraic equivalence. -/
theorem isFiniteProjection_one_iff :
    IsFiniteProjection (1 : R) ↔
      ∀ v : R, star v * v = 1 → v * star v = 1 := by
  constructor
  · intro hfin v hv
    have hpi : IsPartialIsometry v := IsPartialIsometry.of_star_mul_self_eq_one hv
    have hproj : IsStarProjection (v * star v) := hpi.isStarProjection_mul_star_self
    exact hfin.2 (v * star v)
      ⟨IsStarProjection.one R, hproj, v, hpi, hv, rfl⟩ (mul_one _)
  · intro h
    refine ⟨IsStarProjection.one R, ?_⟩
    rintro q ⟨_, _, v, _, hi, hf⟩ _
    exact hf.symm.trans (h v hi)

end Ring

namespace LinearMap

variable {R : Type u} [Ring R] [Algebra ℂ R] [StarRing R]

/-- A faithful tracial linear functional makes every projection finite.
The defect proof extends the unit argument in
`MathlibAnnex.Analysis.VonNeumannAlgebra.Finite`. -/
theorem isFiniteProjection_of_faithful_tracial
    (φ : R →ₗ[ℂ] ℂ)
    (htrace : ∀ a b : R, φ (a * b) = φ (b * a))
    (hfaithful : ∀ a : R, φ (star a * a) = 0 → a = 0)
    {p : R} (hp : IsStarProjection p) : IsFiniteProjection p := by
  refine ⟨hp, ?_⟩
  rintro q ⟨_, hq, v, _, hvi, hvf⟩ hqp
  have hdefect : IsStarProjection (p - q) := hq.sub_of_mul_eq_left hp hqp
  have htrace_eq : φ q = φ p := by
    rw [← hvf, ← hvi]
    exact htrace v (star v)
  have hzero : φ (p - q) = 0 := by rw [map_sub, htrace_eq, sub_self]
  have hdefect_zero : p - q = 0 := hfaithful (p - q) (by
    rw [hdefect.isSelfAdjoint.star_eq, hdefect.isIdempotentElem.eq]
    exact hzero)
  exact (sub_eq_zero.mp hdefect_zero).symm

end LinearMap

namespace VonNeumannAlgebra

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The accepted algebra finiteness predicate agrees with finiteness of the
unit projection in the algebra subtype, with exactly the same witnesses. -/
theorem isFinite_iff_isFiniteProjection_one (M : VonNeumannAlgebra H) :
    M.IsFinite ↔ IsFiniteProjection (1 : M.toStarSubalgebra) := by
  rw [isFiniteProjection_one_iff]
  constructor
  · intro hM v hv
    apply Subtype.ext
    exact hM v v.property
      (congrArg (fun a : M.toStarSubalgebra ↦ (a : H →L[ℂ] H)) hv)
  · intro h v hv hi
    let w : M.toStarSubalgebra := ⟨v, hv⟩
    have hw : star w * w = 1 := Subtype.ext hi
    exact congrArg (fun a : M.toStarSubalgebra ↦ (a : H →L[ℂ] H)) (h w hw)

/-- Finiteness of the algebra makes every internal projection finite. -/
theorem IsFinite.isFiniteProjection {M : VonNeumannAlgebra H} (hM : M.IsFinite)
    {p : M.toStarSubalgebra} (hp : IsStarProjection p) : IsFiniteProjection p :=
  ((isFinite_iff_isFiniteProjection_one M).1 hM).of_mul_eq_left hp (mul_one p)

/-- Finiteness of a projection in `M` is exactly finiteness of the actual
unit of its corner. To infer finiteness in `M`, the internal witness between
two subprojections of `p` is placed in that corner by endpoint absorption. -/
theorem isFiniteProjection_cornerUnit_iff (M : VonNeumannAlgebra H)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p) :
    IsFiniteProjection (cornerUnit M p hp) ↔ IsFiniteProjection p := by
  constructor
  · intro hcorner
    refine ⟨hp, ?_⟩
    intro q hpq hqp
    have hq : IsStarProjection q := hpq.isStarProjection_right
    have hpq' : p * q = q := by
      simpa only [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
        using congrArg star hqp
    let q' : corner M p hp := ⟨q, hpq', hqp⟩
    have heq : MurrayVonNeumannEquivalent (cornerUnit M p hp) q' :=
      (murrayVonNeumannEquivalent_corner_iff M p hp (cornerUnit M p hp) q').2 hpq
    have hqp' : q' = cornerUnit M p hp :=
      hcorner.2 q' heq (mul_cornerUnit M p hp q')
    exact congrArg (fun x : corner M p hp ↦ (x : M.toStarSubalgebra)) hqp'
  · intro hfin
    exact IsFiniteProjection.of_map
      (NonUnitalStarSubalgebraClass.subtype (R := ℂ) (corner M p hp))
      (fun _ _ h ↦ Subtype.ext h) hfin

/-- An internal equivalence of projections preserves finiteness. The
proof transports finite corner units along conjugation by its witness. -/
theorem isFiniteProjection_of_equivalent (M : VonNeumannAlgebra H)
    {p q : M.toStarSubalgebra} (hp : IsFiniteProjection p)
    (hpq : MurrayVonNeumannEquivalent p q) : IsFiniteProjection q := by
  obtain ⟨v, hv, hinitial, hfinal⟩ := hpq.exists_partial_isometry
  let e := cornerEquiv M hp.1 hpq.isStarProjection_right v hv hinitial hfinal
  have hunit : IsFiniteProjection (cornerUnit M p hp.1) :=
    (isFiniteProjection_cornerUnit_iff M p hp.1).2 hp
  have hmap : IsFiniteProjection (e (cornerUnit M p hp.1)) :=
    IsFiniteProjection.map (R := ↥(corner M p hp.1))
      (S := ↥(corner M q hpq.isStarProjection_right)) hunit
      e.toNonUnitalStarAlgHom e.toEquiv.bijective
  have heq : e (cornerUnit M p hp.1) =
      cornerUnit M q hpq.isStarProjection_right :=
    cornerEquiv_unit M hp.1 hpq.isStarProjection_right v hv hinitial hfinal
  rw [heq] at hmap
  exact (isFiniteProjection_cornerUnit_iff M q hpq.isStarProjection_right).1 hmap

end VonNeumannAlgebra
