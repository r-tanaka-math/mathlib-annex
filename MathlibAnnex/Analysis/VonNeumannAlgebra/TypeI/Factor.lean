/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeI.CentralPart
import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.Comparison
import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeI.MinimalCorner
import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeI.Representation
import MathlibAnnex.Analysis.VonNeumannAlgebra.Factor
import MathlibAnnex.Analysis.CStarAlgebra.Ideal.MinimalCompactCorner
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Order.Bounds.OrderIso

/-!
# Full operator algebras and central support in factors

A projection whose represented range is contained in a one-dimensional
subspace has a commutative internal corner. This proves the type I condition
for the full bounded-operator algebra on every complex Hilbert space.

For an arbitrary factor, central projections are zero or one. Consequently
every nonzero element has central support one. The accepted factor predicate
is reused, including its nonzero identity condition. A minimal abelian
projection yields a faithful irreducible cyclic restriction. The existing
represented-bidual ball theorem and the bicommutant property make this
restriction onto `B(K)`, giving the actual type I factor model.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra

namespace VonNeumannAlgebra

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A represented range of dimension at most one gives an abelian
projection. Membership in the specified algebra is retained by the subtype. -/
theorem isAbelianProjection_of_range_le_span_singleton
    (M : VonNeumannAlgebra H) {p : M.toStarSubalgebra} (hp : IsStarProjection p)
    (ξ : H) (hrange : (p : H →L[ℂ] H).range ≤ ℂ ∙ ξ) : IsAbelianProjection M p := by
  refine ⟨hp, ?_⟩
  intro a b hpa hap hpb hbp
  have hax : (a : H →L[ℂ] H) ξ ∈ ℂ ∙ ξ := by
    apply hrange
    refine ⟨(a : H →L[ℂ] H) ξ, ?_⟩
    exact congrArg (fun T : M.toStarSubalgebra ↦ (T : H →L[ℂ] H) ξ) hpa
  have hbx : (b : H →L[ℂ] H) ξ ∈ ℂ ∙ ξ := by
    apply hrange
    refine ⟨(b : H →L[ℂ] H) ξ, ?_⟩
    exact congrArg (fun T : M.toStarSubalgebra ↦ (T : H →L[ℂ] H) ξ) hpb
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hax
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hbx
  apply Subtype.ext
  ext η
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
    (hrange (show (p : H →L[ℂ] H) η ∈ (p : H →L[ℂ] H).range from ⟨η, rfl⟩))
  have haη : (a : H →L[ℂ] H) η = t • (c • ξ) := by
    calc
      (a : H →L[ℂ] H) η = (a : H →L[ℂ] H) ((p : H →L[ℂ] H) η) :=
        (congrArg (fun T : M.toStarSubalgebra ↦ (T : H →L[ℂ] H) η) hap).symm
      _ = (a : H →L[ℂ] H) (t • ξ) := by rw [← ht]
      _ = t • (c • ξ) := by rw [map_smul, ← hc]
  have hbη : (b : H →L[ℂ] H) η = t • (d • ξ) := by
    calc
      (b : H →L[ℂ] H) η = (b : H →L[ℂ] H) ((p : H →L[ℂ] H) η) :=
        (congrArg (fun T : M.toStarSubalgebra ↦ (T : H →L[ℂ] H) η) hbp).symm
      _ = (b : H →L[ℂ] H) (t • ξ) := by rw [← ht]
      _ = t • (d • ξ) := by rw [map_smul, ← hd]
  change (a : H →L[ℂ] H) ((b : H →L[ℂ] H) η) =
    (b : H →L[ℂ] H) ((a : H →L[ℂ] H) η)
  rw [hbη, haη]
  simp only [map_smul, ← hc, ← hd, smul_smul, mul_assoc, mul_comm, mul_left_comm]

/-- The full bounded-operator algebra is type I. A nonzero projection is
cut down to the orthogonal projection onto the span of a nonzero range vector.
There is no separability or finite-dimensionality hypothesis. -/
theorem isTypeI_of_all_operators_mem (M : VonNeumannAlgebra H)
    (hfull : ∀ T : H →L[ℂ] H, T ∈ M) : IsTypeI M := by
  classical
  intro p hp hp0
  have hsome : ¬ ∀ ξ : H, (p : H →L[ℂ] H) ξ = 0 := by
    intro h
    apply hp0
    apply Subtype.ext
    ext ξ
    exact h ξ
  obtain ⟨ξ, hξ⟩ := not_forall.mp hsome
  let η : H := (p : H →L[ℂ] H) ξ
  let q : M.toStarSubalgebra := ⟨(ℂ ∙ η).starProjection, hfull _⟩
  have hq : IsStarProjection q := by
    have h : IsStarProjection (ℂ ∙ η).starProjection := isStarProjection_starProjection
    exact ⟨Subtype.ext h.isIdempotentElem.eq, Subtype.ext h.isSelfAdjoint.star_eq⟩
  have hqrange : (q : H →L[ℂ] H).range = ℂ ∙ η :=
    Submodule.range_starProjection _
  have hq0 : q ≠ 0 := by
    intro hzero
    have hfix : (q : H →L[ℂ] H) η = η :=
      Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_span_singleton_self η)
    have hzeroη : (q : H →L[ℂ] H) η = 0 := by
      rw [hzero]
      rfl
    exact hξ (hfix.symm.trans hzeroη)
  have hrange : (q : H →L[ℂ] H).range ≤ (p : H →L[ℂ] H).range := by
    rw [hqrange]
    apply Submodule.span_le.mpr
    intro x hx
    have hxη : x = η := Set.mem_singleton_iff.mp hx
    rw [hxη]
    exact ⟨ξ, rfl⟩
  have hle : q ≤ p := (projection_le_iff_range_le M hq hp).mpr hrange
  exact ⟨q, isAbelianProjection_of_range_le_span_singleton M hq η hqrange.le,
    hq0, (hq.le_iff_mul_eq_left hp).mp hle⟩

/-- The canonical algebra generated by all bounded operators is type I.
This formulation does not introduce a competing top-instance for concrete
von Neumann algebras. -/
theorem isTypeI_generated_top :
    IsTypeI (generated (⊤ : StarSubalgebra ℂ (H →L[ℂ] H))) := by
  apply isTypeI_of_all_operators_mem
  intro T
  exact subset_generated (⊤ : StarSubalgebra ℂ (H →L[ℂ] H)) (by trivial)

/-- The only central projections in a factor are zero and one. -/
theorem IsFactor.eq_zero_or_eq_one_of_central_projection
    {M : VonNeumannAlgebra H} (hM : IsFactor M)
    {z : M.toStarSubalgebra} (hz : IsStarProjection z)
    (hcentral : ∀ a : M.toStarSubalgebra, a * z = z * a) : z = 0 ∨ z = 1 := by
  obtain ⟨c, hc⟩ := hM.2 z z.property (by
    intro a ha
    exact congrArg Subtype.val (hcentral ⟨a, ha⟩))
  have hz' : IsStarProjection (z : H →L[ℂ] H) := hz.map M.toStarSubalgebra.subtype
  have hscalar : (c * c - c) • (1 : H →L[ℂ] H) = 0 := by
    calc
      (c * c - c) • (1 : H →L[ℂ] H) =
          (z : H →L[ℂ] H) * (z : H →L[ℂ] H) - (z : H →L[ℂ] H) := by
        rw [hc]
        simp only [sub_smul, smul_mul_assoc, mul_smul_comm, one_mul, smul_smul]
      _ = 0 := by rw [hz'.isIdempotentElem.eq, sub_self]
  have hcoeff : c * c - c = 0 := (smul_eq_zero.mp hscalar).resolve_right hM.1
  have hprod : c * (c - 1) = 0 := by simpa only [mul_sub, mul_one] using hcoeff
  rcases mul_eq_zero.mp hprod with hc0 | hc1
  · left
    apply Subtype.ext
    change (z : H →L[ℂ] H) = 0
    simpa only [hc0, zero_smul] using hc
  · right
    have hc1' : c = 1 := sub_eq_zero.mp hc1
    apply Subtype.ext
    change (z : H →L[ℂ] H) = 1
    simpa only [hc1', one_smul] using hc

/-- A nonzero internal element of a factor has full central support. -/
theorem IsFactor.centralSupport_eq_one {M : VonNeumannAlgebra H}
    (hM : IsFactor M) {p : M.toStarSubalgebra} (hp : p ≠ 0) :
    centralSupport M p = 1 := by
  rcases hM.eq_zero_or_eq_one_of_central_projection
    (isStarProjection_centralSupport M p) (centralSupport_commute M p) with h | h
  · exact (hp ((centralSupport_eq_zero_iff M p).mp h)).elim
  · exact h

/-- In a factor, a nonzero abelian projection is minimal in the existing
projection-order sense. The proof uses central support, not a claim that an
arbitrary projection-minimal C-star corner is scalar. -/
theorem IsAbelianProjection.isMinimalStarProjection_of_isFactor {M : VonNeumannAlgebra H}
    {p : M.toStarSubalgebra} (hp : IsAbelianProjection M p) (hp0 : p ≠ 0)
    (hM : IsFactor M) :
    MathlibAnnex.Analysis.CStarAlgebra.IsMinimalStarProjection p := by
  refine ⟨hp.1, hp0, ?_⟩
  intro q hq hq0 hqp
  have hqp' : q * p = q := (hq.le_iff_mul_eq_left hp.1).mp hqp
  have hpq : p * q = q := (hq.le_iff_mul_eq_right hp.1).mp hqp
  let r : M.toStarSubalgebra := p - q
  have hrp : r * p = r := by
    change (p - q) * p = p - q
    rw [sub_mul, hp.1.isIdempotentElem.eq, hqp']
  have hrq : r * q = 0 := by
    change (p - q) * q = 0
    rw [sub_mul, hpq, hq.isIdempotentElem.eq, sub_self]
  have hvanish (a : M.toStarSubalgebra) : r * a * q = 0 := by
    have hpx : p * (p * a * p) = p * a * p := by
      calc
        p * (p * a * p) = (p * p) * a * p := by simp only [mul_assoc]
        _ = p * a * p := by rw [hp.1.isIdempotentElem.eq]
    have hxp : (p * a * p) * p = p * a * p := by
      rw [mul_assoc, hp.1.isIdempotentElem.eq]
    have hcomm : q * (p * a * p) = (p * a * p) * q :=
      hp.mul_comm hpq hqp' hpx hxp
    calc
      r * a * q = (r * p) * a * (p * q) := by rw [hrp, hpq]
      _ = r * ((p * a * p) * q) := by simp only [mul_assoc]
      _ = r * (q * (p * a * p)) := by rw [← hcomm]
      _ = (r * q) * (p * a * p) := (mul_assoc _ _ _).symm
      _ = 0 := by rw [hrq, zero_mul]
  have hrc : r * centralSupport M q = 0 := by
    apply (mul_centralHull_eq_zero_iff M {q} r).mpr
    intro q' hq' a
    have heq : q' = q := Set.mem_singleton_iff.mp hq'
    simpa only [heq] using hvanish a
  have hrzero : r = 0 := by
    simpa only [hM.centralSupport_eq_one hq0, mul_one] using hrc
  exact (sub_eq_zero.mp hrzero).symm

/-- The type I condition supplies an actual nonzero abelian projection in
a factor; the nonzero identity is taken from the accepted factor definition. -/
theorem IsFactor.exists_nonzero_abelian_projection {M : VonNeumannAlgebra H}
    (hM : IsFactor M) (hI : IsTypeI M) :
    ∃ p : M.toStarSubalgebra, IsAbelianProjection M p ∧ p ≠ 0 ∧
      centralSupport M p = 1 := by
  have hone : (1 : M.toStarSubalgebra) ≠ 0 := by
    intro h
    exact hM.1 (congrArg Subtype.val h)
  obtain ⟨p, hp, hp0, _⟩ := hI 1 (IsStarProjection.one _) hone
  exact ⟨p, hp, hp0, hM.centralSupport_eq_one hp0⟩

/-- A type I factor contains an actual nonzero minimal abelian projection,
using the canonical pre-existing minimal-projection predicate. -/
theorem IsFactor.exists_minimal_abelian_projection {M : VonNeumannAlgebra H}
    (hM : IsFactor M) (hI : IsTypeI M) :
    ∃ p : M.toStarSubalgebra, IsAbelianProjection M p ∧
      MathlibAnnex.Analysis.CStarAlgebra.IsMinimalStarProjection p ∧
      centralSupport M p = 1 := by
  obtain ⟨p, hp, hp0, hc⟩ := hM.exists_nonzero_abelian_projection hI
  exact ⟨p, hp, hp.isMinimalStarProjection_of_isFactor hp0 hM, hc⟩

/-- The corner of a nonzero abelian projection in a factor is scalar.
The equality is internal and its scalar multiple uses the corner unit `p`. -/
theorem IsAbelianProjection.exists_scalar_corner_of_isFactor
    {M : VonNeumannAlgebra H} {p : M.toStarSubalgebra}
    (hp : IsAbelianProjection M p) (hp0 : p ≠ 0) (hM : IsFactor M)
    (a : M.toStarSubalgebra) : ∃ c : ℂ, p * a * p = c • p :=
  exists_scalar_corner_of_minimal_projection M (hp.isMinimalStarProjection_of_isFactor hp0 hM) a

/-- Every nonzero projection in a factor dominates a projection equivalent
to any fixed minimal projection. The equivalence is internal to `M`. -/
theorem IsFactor.exists_equivalent_subprojection_of_minimal_projection
    {M : VonNeumannAlgebra H} (hM : IsFactor M)
    {p r : M.toStarSubalgebra}
    (hp : MathlibAnnex.Analysis.CStarAlgebra.IsMinimalStarProjection p)
    (hr : IsStarProjection r) (hr0 : r ≠ 0) :
    ∃ q : M.toStarSubalgebra, MurrayVonNeumannEquivalent p q ∧ q ≠ 0 ∧ q ≤ r := by
  have hone : (1 : M.toStarSubalgebra) ≠ 0 := by
    intro h
    exact hM.1 (congrArg Subtype.val h)
  have hc : centralSupport M p * centralSupport M r ≠ 0 := by
    rw [hM.centralSupport_eq_one hp.2.1, hM.centralSupport_eq_one hr0, one_mul]
    exact hone
  obtain ⟨p', q, heq, hp'0, hq0, hp'p, hqr⟩ :=
    exists_nonzero_equivalent_subprojections_of_centralSupport_mul_ne_zero M hp.1 hr hc
  have hp'p_eq : p' = p := hp.2.2 p' heq.1 hp'0 hp'p
  rw [hp'p_eq] at heq
  exact ⟨q, heq, hq0, hqr⟩

/-- Nonzero abelian projections in a factor are internally equivalent. -/
theorem IsFactor.equivalent_of_nonzero_abelian_projections
    {M : VonNeumannAlgebra H} (hM : IsFactor M)
    {p q : M.toStarSubalgebra} (hp : IsAbelianProjection M p) (hp0 : p ≠ 0)
    (hq : IsAbelianProjection M q) (hq0 : q ≠ 0) :
    MurrayVonNeumannEquivalent p q := by
  obtain ⟨r, heq, hr0, hrq⟩ :=
    hM.exists_equivalent_subprojection_of_minimal_projection
      (hp.isMinimalStarProjection_of_isFactor hp0 hM) hq.1 hq0
  have hrq_eq : r = q := (hq.isMinimalStarProjection_of_isFactor hq0 hM).2.2 r heq.2.1 hr0 hrq
  simpa only [hrq_eq] using heq

/-- A factor is type I precisely when it has a nonzero abelian projection.
The reverse implication uses central support and internal polar comparison,
so it applies without any assumption on the dimension of the ambient space. -/
theorem IsFactor.isTypeI_iff_exists_nonzero_abelian_projection
    {M : VonNeumannAlgebra H} (hM : IsFactor M) :
    IsTypeI M ↔ ∃ p : M.toStarSubalgebra, IsAbelianProjection M p ∧ p ≠ 0 := by
  constructor
  · intro hI
    obtain ⟨p, hp, hp0, _⟩ := hM.exists_nonzero_abelian_projection hI
    exact ⟨p, hp, hp0⟩
  · rintro ⟨p, hp, hp0⟩ r hr hr0
    obtain ⟨q, heq, hq0, hqr⟩ :=
      hM.exists_equivalent_subprojection_of_minimal_projection
        (hp.isMinimalStarProjection_of_isFactor hp0 hM) hr hr0
    exact ⟨q, hp.of_equivalent heq, hq0, (heq.2.1.le_iff_mul_eq_left hr).mp hqr⟩

/-- Every type I factor is actually star-isomorphic to the full operator
algebra on a nontrivial Hilbert space. The equivalence is isometric and
preserves every existing least upper bound in both directions; in particular
it preserves bounded increasing positive suprema, the order formulation of
normality. The Hilbert space is constructed as a closed cyclic subspace and
is not identified with the original ambient representation space. -/
theorem exists_starAlgEquiv_continuousLinearMap_of_isFactor_of_isTypeI
    (M : VonNeumannAlgebra H) (hM : IsFactor M) (hI : IsTypeI M) :
    ∃ (K : Type u) (instN : NormedAddCommGroup K),
      letI := instN
      ∃ instI : InnerProductSpace ℂ K,
        letI := instI
        ∃ instC : CompleteSpace K,
          letI := instC
          ∃ instNT : Nontrivial K,
            letI := instNT
            ∃ e : M.toStarSubalgebra ≃⋆ₐ[ℂ] (K →L[ℂ] K),
              Isometry e ∧
              (∀ (S : Set M.toStarSubalgebra) (a : M.toStarSubalgebra),
                IsLUB S a ↔ IsLUB (e '' S) (e a)) ∧
              (∀ (S : Set (K →L[ℂ] K)) (a : K →L[ℂ] K),
                IsLUB S a ↔ IsLUB (e.symm '' S) (e.symm a)) := by
  classical
  obtain ⟨p, _, hp, hcentral⟩ := hM.exists_minimal_abelian_projection hI
  obtain ⟨K, hKclosed, hdata⟩ :=
    exists_faithful_irreducible_restriction_of_minimal_projection M hp hcentral
  letI : CompleteSpace K := hKclosed.completeSpace_coe
  obtain ⟨hK, hnontrivial, hfaith, hirr⟩ := hdata
  letI : Nontrivial K := hnontrivial
  let rho := MathlibAnnex.Analysis.CStarAlgebra.Representation.restrictToReducing
    M.toStarSubalgebra.subtype K hK
  have hsurj : Function.Surjective rho :=
    surjective_restrict_to_reducing_of_irreducible M K hK hirr
  let e : M.toStarSubalgebra ≃⋆ₐ[ℂ] (K →L[ℂ] K) :=
    { toFun := rho
      invFun := fun T ↦ (hsurj T).choose
      left_inv := fun a ↦ hfaith (hsurj (rho a)).choose_spec
      right_inv := fun T ↦ (hsurj T).choose_spec
      map_add' := map_add rho
      map_mul' := map_mul rho
      map_star' := map_star rho
      map_smul' := map_smul rho }
  let eo : M.toStarSubalgebra ≃o (K →L[ℂ] K) :=
    { toEquiv := e.toEquiv
      map_rel_iff' := by intro a b; exact map_le_map_iff e }
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance,
    e, StarAlgEquiv.isometry e, ?_, ?_⟩
  · intro S a
    exact eo.isLUB_image'.symm
  · intro S a
    exact eo.symm.isLUB_image'.symm

end VonNeumannAlgebra
