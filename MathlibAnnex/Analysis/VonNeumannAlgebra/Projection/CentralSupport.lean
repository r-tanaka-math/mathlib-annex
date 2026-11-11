/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.Basic
import MathlibAnnex.Algebra.Star.ProjectionEquivalence
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Central support in a concrete von Neumann algebra

For a set `S` of elements of `M`, the closed span of the vectors `a (p ξ)`,
with `a ∈ M` and `p ∈ S`, is invariant under both `M` and its commutant.
Its orthogonal projection is therefore a central element of `M`. This gives
the least central projection which fixes every member of `S`.

Taking a singleton gives `centralSupport`. The construction works on an
arbitrary Hilbert space, including the zero space, and does not assume the
existence of a least central projection or of a projection lattice.
-/

set_option autoImplicit false
noncomputable section

open Set

namespace VonNeumannAlgebra

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private def centralOrbitSpan (M : VonNeumannAlgebra H)
    (S : Set M.toStarSubalgebra) : Submodule ℂ H :=
  ⨆ p : S, ⨆ a : M.toStarSubalgebra,
    ((a : H →L[ℂ] H) * (p.1 : H →L[ℂ] H)).range

private def centralOrbitClosure (M : VonNeumannAlgebra H)
    (S : Set M.toStarSubalgebra) : Submodule ℂ H :=
  (centralOrbitSpan M S).topologicalClosure

local instance (M : VonNeumannAlgebra H) (S : Set M.toStarSubalgebra) :
    CompleteSpace (centralOrbitClosure M S) :=
  (centralOrbitSpan M S).isClosed_topologicalClosure.completeSpace_coe

private theorem apply_mem_centralOrbitSpan (M : VonNeumannAlgebra H)
    (S : Set M.toStarSubalgebra) {p : M.toStarSubalgebra} (hp : p ∈ S)
    (a : M.toStarSubalgebra) (ξ : H) :
    (a : H →L[ℂ] H) ((p : H →L[ℂ] H) ξ) ∈ centralOrbitSpan M S := by
  have h : ((a : H →L[ℂ] H) * (p : H →L[ℂ] H)).range ≤ centralOrbitSpan M S :=
    le_iSup_of_le (⟨p, hp⟩ : S) (le_iSup_of_le a (by rfl))
  exact h ⟨ξ, rfl⟩

private theorem centralOrbitSpan_invariant (M : VonNeumannAlgebra H)
    (S : Set M.toStarSubalgebra) {b : H →L[ℂ] H} (hb : b ∈ M) :
    Set.MapsTo b (centralOrbitSpan M S) (centralOrbitSpan M S) := by
  have h : centralOrbitSpan M S ≤ (centralOrbitSpan M S).comap b.toLinearMap := by
    refine iSup_le fun p ↦ iSup_le fun a ↦ ?_
    rintro ξ ⟨η, rfl⟩
    exact apply_mem_centralOrbitSpan M S p.2 ((⟨b, hb⟩ : M.toStarSubalgebra) * a) η
  exact fun _ hξ ↦ h hξ

private theorem centralOrbitSpan_commutant_invariant (M : VonNeumannAlgebra H)
    (S : Set M.toStarSubalgebra) {b : H →L[ℂ] H} (hb : b ∈ M.commutant) :
    Set.MapsTo b (centralOrbitSpan M S) (centralOrbitSpan M S) := by
  have hbcomm := mem_commutant_iff.mp hb
  have h : centralOrbitSpan M S ≤ (centralOrbitSpan M S).comap b.toLinearMap := by
    refine iSup_le fun p ↦ iSup_le fun a ↦ ?_
    rintro ξ ⟨η, rfl⟩
    change b (((a : H →L[ℂ] H) * (p.1 : H →L[ℂ] H)) η) ∈ centralOrbitSpan M S
    have hmul : b * ((a : H →L[ℂ] H) * (p.1 : H →L[ℂ] H)) =
        ((a : H →L[ℂ] H) * (p.1 : H →L[ℂ] H)) * b := by
      rw [← mul_assoc, ← hbcomm a a.property, mul_assoc,
        ← hbcomm p.1 p.1.property, ← mul_assoc]
    have happ := congrArg (fun T : H →L[ℂ] H ↦ T η) hmul
    rw [show b (((a : H →L[ℂ] H) * (p.1 : H →L[ℂ] H)) η) =
      (a : H →L[ℂ] H) ((p.1 : H →L[ℂ] H) (b η)) from happ]
    exact apply_mem_centralOrbitSpan M S p.2 a (b η)
  exact fun _ hξ ↦ h hξ

private theorem centralOrbitClosure_invariant (M : VonNeumannAlgebra H)
    (S : Set M.toStarSubalgebra) {b : H →L[ℂ] H} (hb : b ∈ M) :
    centralOrbitClosure M S ∈ Module.End.invtSubmodule b.toLinearMap := by
  exact (centralOrbitSpan_invariant M S hb).closure b.continuous

private theorem centralOrbitClosure_commutant_invariant (M : VonNeumannAlgebra H)
    (S : Set M.toStarSubalgebra) {b : H →L[ℂ] H} (hb : b ∈ M.commutant) :
    centralOrbitClosure M S ∈ Module.End.invtSubmodule b.toLinearMap := by
  exact (centralOrbitSpan_commutant_invariant M S hb).closure b.continuous

/-- The least central projection fixing every element of a specified set.
The elements and the projection belong to the same algebra `M`. -/
def centralHull (M : VonNeumannAlgebra H) (S : Set M.toStarSubalgebra) :
    M.toStarSubalgebra :=
  ⟨(centralOrbitClosure M S).starProjection,
    starProjection_mem M (centralOrbitClosure M S)
      (fun _ hb ↦ centralOrbitClosure_commutant_invariant M S hb)⟩

theorem isStarProjection_centralHull (M : VonNeumannAlgebra H)
    (S : Set M.toStarSubalgebra) : IsStarProjection (centralHull M S) := by
  have h : IsStarProjection (centralOrbitClosure M S).starProjection :=
    isStarProjection_starProjection
  exact ⟨Subtype.ext h.isIdempotentElem.eq, Subtype.ext h.isSelfAdjoint.star_eq⟩

theorem centralHull_mem_commutant (M : VonNeumannAlgebra H)
    (S : Set M.toStarSubalgebra) :
    (centralHull M S : H →L[ℂ] H) ∈ M.commutant := by
  apply starProjection_mem M.commutant (centralOrbitClosure M S)
  intro b hb
  rw [commutant_commutant] at hb
  exact centralOrbitClosure_invariant M S hb

theorem centralHull_commute (M : VonNeumannAlgebra H)
    (S : Set M.toStarSubalgebra) (a : M.toStarSubalgebra) :
    a * centralHull M S = centralHull M S * a := by
  apply Subtype.ext
  exact (mem_commutant_iff.mp (centralHull_mem_commutant M S)) a a.property

/-- Every member of `S` has range in the range of its central hull. -/
theorem centralHull_mul_eq (M : VonNeumannAlgebra H)
    (S : Set M.toStarSubalgebra) {p : M.toStarSubalgebra} (hp : p ∈ S) :
    centralHull M S * p = p := by
  apply Subtype.ext
  ext ξ
  change (centralOrbitClosure M S).starProjection ((p : H →L[ℂ] H) ξ) =
    (p : H →L[ℂ] H) ξ
  apply Submodule.starProjection_eq_self_iff.mpr
  exact (centralOrbitSpan M S).le_topologicalClosure
    (by simpa using apply_mem_centralOrbitSpan M S hp (1 : M.toStarSubalgebra) ξ)

theorem mul_centralHull_eq (M : VonNeumannAlgebra H)
    (S : Set M.toStarSubalgebra) {p : M.toStarSubalgebra} (hp : p ∈ S) :
    p * centralHull M S = p :=
  (centralHull_commute M S p).trans (centralHull_mul_eq M S hp)

/-- Leastness is stated by the algebraic projection-order equation. No
existence or minimality assumption is hidden in the construction. -/
theorem centralHull_le (M : VonNeumannAlgebra H) (S : Set M.toStarSubalgebra)
    {q : M.toStarSubalgebra} (hq : IsStarProjection q)
    (hqcentral : ∀ a : M.toStarSubalgebra, a * q = q * a)
    (hfix : ∀ p ∈ S, q * p = p) : centralHull M S * q = centralHull M S := by
  have hq' : IsStarProjection (q : H →L[ℂ] H) := hq.map M.toStarSubalgebra.subtype
  have hspan : centralOrbitSpan M S ≤ (q : H →L[ℂ] H).range := by
    refine iSup_le fun p ↦ iSup_le fun a ↦ ?_
    rintro ξ ⟨η, rfl⟩
    refine ⟨(a : H →L[ℂ] H) ((p.1 : H →L[ℂ] H) η), ?_⟩
    have heq : q * (a * p.1) = a * p.1 := by
      rw [← mul_assoc, ← hqcentral a, mul_assoc, hfix p.1 p.2]
    exact congrArg (fun T : M.toStarSubalgebra ↦ (T : H →L[ℂ] H) η) heq
  have hclosure : centralOrbitClosure M S ≤ (q : H →L[ℂ] H).range :=
    (centralOrbitSpan M S).topologicalClosure_minimal hspan
      (ContinuousLinearMap.IsIdempotentElem.isClosed_range hq'.isIdempotentElem)
  have hleft : q * centralHull M S = centralHull M S := by
    apply Subtype.ext
    ext ξ
    have hξ : (centralOrbitClosure M S).starProjection ξ ∈ centralOrbitClosure M S :=
      Submodule.coe_mem ((centralOrbitClosure M S).orthogonalProjectionOnto ξ)
    obtain ⟨η, hη⟩ := hclosure hξ
    change (q : H →L[ℂ] H) ((centralOrbitClosure M S).starProjection ξ) =
      (centralOrbitClosure M S).starProjection ξ
    rw [← hη]
    exact congrArg (fun T : H →L[ℂ] H ↦ T η) hq'.isIdempotentElem.eq
  exact (hqcentral (centralHull M S)).trans hleft

/-- An operator annihilates the central hull exactly when it annihilates
every algebraic orbit `a * p`. This is the density step used to extract a
nonzero corner overlap from a nonzero central part. -/
theorem mul_centralHull_eq_zero_iff (M : VonNeumannAlgebra H)
    (S : Set M.toStarSubalgebra) (r : M.toStarSubalgebra) :
    r * centralHull M S = 0 ↔
      ∀ p ∈ S, ∀ a : M.toStarSubalgebra, r * a * p = 0 := by
  constructor
  · intro h p hp a
    have hfix : centralHull M S * (a * p) = a * p := by
      rw [← mul_assoc, ← centralHull_commute M S a, mul_assoc,
        centralHull_mul_eq M S hp]
    calc
      r * a * p = r * (centralHull M S * (a * p)) := by rw [hfix, mul_assoc]
      _ = (r * centralHull M S) * (a * p) := (mul_assoc _ _ _).symm
      _ = 0 := by rw [h, zero_mul]
  · intro h
    have hspan : centralOrbitSpan M S ≤ (r : H →L[ℂ] H).ker := by
      refine iSup_le fun p ↦ iSup_le fun a ↦ ?_
      rintro ξ ⟨η, rfl⟩
      exact congrArg (fun T : M.toStarSubalgebra ↦ (T : H →L[ℂ] H) η)
        (h p.1 p.2 a)
    have hclosed : IsClosed ((r : H →L[ℂ] H).ker : Set H) :=
      isClosed_eq (r : H →L[ℂ] H).continuous continuous_const
    have hclosure : centralOrbitClosure M S ≤ (r : H →L[ℂ] H).ker :=
      (centralOrbitSpan M S).topologicalClosure_minimal hspan hclosed
    apply Subtype.ext
    ext ξ
    exact hclosure
      (Submodule.coe_mem ((centralOrbitClosure M S).orthogonalProjectionOnto ξ))

theorem exists_mul_mul_ne_zero_of_mul_centralHull_ne_zero
    (M : VonNeumannAlgebra H) (S : Set M.toStarSubalgebra) (r : M.toStarSubalgebra)
    (hr : r * centralHull M S ≠ 0) :
    ∃ p ∈ S, ∃ a : M.toStarSubalgebra, r * a * p ≠ 0 := by
  classical
  by_contra hnone
  apply hr
  apply (mul_centralHull_eq_zero_iff M S r).mpr
  intro p hp a
  by_contra h
  exact hnone ⟨p, hp, a, h⟩

/-- The central support of an element is the central hull of its singleton.
For a projection this is precisely its least central majorant. -/
def centralSupport (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra) :
    M.toStarSubalgebra := centralHull M {p}

theorem isStarProjection_centralSupport (M : VonNeumannAlgebra H)
    (p : M.toStarSubalgebra) : IsStarProjection (centralSupport M p) :=
  isStarProjection_centralHull M {p}

theorem centralSupport_commute (M : VonNeumannAlgebra H)
    (p a : M.toStarSubalgebra) : a * centralSupport M p = centralSupport M p * a :=
  centralHull_commute M {p} a

@[simp]
theorem centralSupport_mul_self (M : VonNeumannAlgebra H)
    (p : M.toStarSubalgebra) : centralSupport M p * p = p :=
  centralHull_mul_eq M {p} (Set.mem_singleton p)

@[simp]
theorem self_mul_centralSupport (M : VonNeumannAlgebra H)
    (p : M.toStarSubalgebra) : p * centralSupport M p = p :=
  mul_centralHull_eq M {p} (Set.mem_singleton p)

theorem centralSupport_le (M : VonNeumannAlgebra H)
    {p q : M.toStarSubalgebra} (hq : IsStarProjection q)
    (hqcentral : ∀ a : M.toStarSubalgebra, a * q = q * a)
    (hqp : q * p = p) : centralSupport M p * q = centralSupport M p := by
  apply centralHull_le M {p} hq hqcentral
  intro r hr
  have hrp : r = p := Set.mem_singleton_iff.mp hr
  simpa only [hrp] using hqp

theorem centralSupport_eq_of_central (M : VonNeumannAlgebra H)
    {p : M.toStarSubalgebra} (hp : IsStarProjection p)
    (hpcentral : ∀ a : M.toStarSubalgebra, a * p = p * a) :
    centralSupport M p = p := by
  have hle := centralSupport_le M hp hpcentral hp.isIdempotentElem.eq
  exact hle.symm.trans (centralSupport_mul_self M p)

@[simp]
theorem centralSupport_zero (M : VonNeumannAlgebra H) :
    centralSupport M 0 = 0 :=
  centralSupport_eq_of_central M (IsStarProjection.zero _) (by intros; simp)

@[simp]
theorem centralSupport_one (M : VonNeumannAlgebra H) :
    centralSupport M 1 = 1 :=
  centralSupport_eq_of_central M (IsStarProjection.one _) (by intros; simp)

@[simp]
theorem centralSupport_eq_zero_iff (M : VonNeumannAlgebra H)
    (p : M.toStarSubalgebra) : centralSupport M p = 0 ↔ p = 0 := by
  constructor
  · intro h
    have hp := centralSupport_mul_self M p
    simpa only [h, zero_mul] using hp.symm
  · rintro rfl
    exact centralSupport_zero M

@[simp]
theorem centralSupport_idempotent (M : VonNeumannAlgebra H)
    (p : M.toStarSubalgebra) : centralSupport M (centralSupport M p) = centralSupport M p :=
  centralSupport_eq_of_central M (isStarProjection_centralSupport M p)
    (centralSupport_commute M p)

/-- The central-support construction is monotone under range absorption. -/
theorem centralSupport_mono (M : VonNeumannAlgebra H)
    {p q : M.toStarSubalgebra} (hqp : q * p = p) :
    centralSupport M p * centralSupport M q = centralSupport M p := by
  apply centralSupport_le M (isStarProjection_centralSupport M q)
    (centralSupport_commute M q)
  calc
    centralSupport M q * p = centralSupport M q * (q * p) := by rw [hqp]
    _ = (centralSupport M q * q) * p := (mul_assoc _ _ _).symm
    _ = q * p := by rw [centralSupport_mul_self]
    _ = p := hqp

/-- Internal Murray--von Neumann equivalence preserves central support. -/
theorem centralSupport_eq_of_equivalent (M : VonNeumannAlgebra H)
    {p q : M.toStarSubalgebra} (h : MurrayVonNeumannEquivalent p q) :
    centralSupport M p = centralSupport M q := by
  have step : ∀ {p q : M.toStarSubalgebra}, MurrayVonNeumannEquivalent p q →
      centralSupport M p * centralSupport M q = centralSupport M p := by
    intro p q hpq
    obtain ⟨hp, hq, v, hv, hvp, hvq⟩ := hpq
    have hqv : q * v = v := by
      rw [← hvq]
      exact hv
    have hcv : centralSupport M q * v = v := by
      calc
        centralSupport M q * v = centralSupport M q * (q * v) := by rw [hqv]
        _ = (centralSupport M q * q) * v := (mul_assoc _ _ _).symm
        _ = q * v := by rw [centralSupport_mul_self]
        _ = v := hqv
    apply centralSupport_le M (isStarProjection_centralSupport M q)
      (centralSupport_commute M q)
    rw [← hvp, ← mul_assoc, ← centralSupport_commute M q (star v), mul_assoc, hcv]
  have hpq := step h
  have hqp := step h.symm
  calc
    centralSupport M p = centralSupport M p * centralSupport M q := hpq.symm
    _ = centralSupport M q * centralSupport M p := centralSupport_commute M q _
    _ = centralSupport M q := hqp

end VonNeumannAlgebra
