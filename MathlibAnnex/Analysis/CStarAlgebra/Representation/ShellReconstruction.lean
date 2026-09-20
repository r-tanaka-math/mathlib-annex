import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Basic
import MathlibAnnex.Analysis.InnerProductSpace.ProjectionLimit
import MathlibAnnex.Analysis.InnerProductSpace.ProjectionShell
import MathlibAnnex.Analysis.InnerProductSpace.UnitaryCompletion

/-!
# Rebuilding shell strong sums in an arbitrary representation

Only algebraic source identities are transported through the representation.
The strong limits are then reconstructed in the target Hilbert space by the
orthogonal-shell theorem; no representation is claimed to preserve a strong
operator limit formed elsewhere.
-/

set_option autoImplicit false

open Filter Topology
open scoped InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Star projections remain star projections under a unital star-algebra
homomorphism. -/
theorem IsStarProjection.map_representation
    (pi : Representation A H) {p : A} (hp : IsStarProjection p) :
    IsStarProjection (pi p) := by
  constructor
  · rw [isIdempotentElem_iff, ← map_mul, hp.isIdempotentElem.eq]
  · rw [isSelfAdjoint_iff, ← map_star, hp.isSelfAdjoint.star_eq]

/-- Algebraic decreasing projection flags and exact shell supports rebuild
both strong shell sums and their limiting products in every represented
Hilbert space. -/
theorem exists_represented_strongSums_of_sourceShells
    (pi : Representation A H)
    (p q w : ℕ → A)
    (hp : ∀ n, IsStarProjection (p n))
    (hq : ∀ n, IsStarProjection (q n))
    (hp0 : p 0 = 1) (hq0 : q 0 = 1)
    (hp_le : ∀ ⦃m n : ℕ⦄, m ≤ n → p m * p n = p n)
    (hq_le : ∀ ⦃m n : ℕ⦄, m ≤ n → q m * q n = q n)
    (hInitial : ∀ n, star (w n) * w n = p n - p (n + 1))
    (hFinal : ∀ n, w n * star (w n) = q n - q (n + 1)) :
    let U : ℕ → Submodule ℂ H := fun n ↦ (pi (p n)).range
    let V : ℕ → Submodule ℂ H := fun n ↦ (pi (q n)).range
    ∃ S T PU PV : H →L[ℂ] H,
      ContinuousLinearMap.StronglyConverges
        (ContinuousLinearMap.partialSum (fun n ↦ pi (w n))) atTop S ∧
      ContinuousLinearMap.StronglyConverges
        (ContinuousLinearMap.partialSum (fun n ↦ (pi (w n))†)) atTop T ∧
      T = S† ∧
      IsStarProjection PU ∧ PU.range = ⨅ n, U n ∧
      IsStarProjection PV ∧ PV.range = ⨅ n, V n ∧
      (S†).comp S = 1 - PU ∧
      S.comp (S†) = 1 - PV := by
  dsimp only
  let U : ℕ → Submodule ℂ H := fun n ↦ (pi (p n)).range
  let V : ℕ → Submodule ℂ H := fun n ↦ (pi (q n)).range
  have hpPi (n : ℕ) : IsStarProjection (pi (p n)) :=
    IsStarProjection.map_representation pi (hp n)
  have hqPi (n : ℕ) : IsStarProjection (pi (q n)) :=
    IsStarProjection.map_representation pi (hq n)
  have hUdata (n : ℕ) : ∃ (_ : (U n).HasOrthogonalProjection),
      pi (p n) = (U n).starProjection := by
    simpa [U] using
      (isStarProjection_iff_eq_starProjection_range.mp (hpPi n))
  have hVdata (n : ℕ) : ∃ (_ : (V n).HasOrthogonalProjection),
      pi (q n) = (V n).starProjection := by
    simpa [V] using
      (isStarProjection_iff_eq_starProjection_range.mp (hqPi n))
  letI hUprojection (n : ℕ) : (U n).HasOrthogonalProjection := (hUdata n).choose
  letI hVprojection (n : ℕ) : (V n).HasOrthogonalProjection := (hVdata n).choose
  have hUproj (n : ℕ) : pi (p n) = (U n).starProjection := (hUdata n).choose_spec
  have hVproj (n : ℕ) : pi (q n) = (V n).starProjection := (hVdata n).choose_spec
  have hUclosed (n : ℕ) : IsClosed (U n : Set H) := by
    exact ContinuousLinearMap.IsIdempotentElem.isClosed_range (hpPi n).isIdempotentElem
  have hVclosed (n : ℕ) : IsClosed (V n : Set H) := by
    exact ContinuousLinearMap.IsIdempotentElem.isClosed_range (hqPi n).isIdempotentElem
  letI : IsClosed ((⨅ n, U n : Submodule ℂ H) : Set H) := by
    simpa only [Submodule.coe_iInf] using isClosed_iInter hUclosed
  letI : IsClosed ((⨅ n, V n : Submodule ℂ H) : Set H) := by
    simpa only [Submodule.coe_iInf] using isClosed_iInter hVclosed
  letI : CompleteSpace (⨅ n, U n : Submodule ℂ H) := inferInstance
  letI : CompleteSpace (⨅ n, V n : Submodule ℂ H) := inferInstance
  letI : (⨅ n, U n).HasOrthogonalProjection := inferInstance
  letI : (⨅ n, V n).HasOrthogonalProjection := inferInstance
  have hUanti : Antitone U := by
    intro m n hmn
    rintro x ⟨y, rfl⟩
    refine ⟨pi (p n) y, ?_⟩
    have heq : pi (p m) * pi (p n) = pi (p n) := by
      rw [← map_mul, hp_le hmn]
    exact congrArg (fun T : H →L[ℂ] H ↦ T y) heq
  have hVanti : Antitone V := by
    intro m n hmn
    rintro x ⟨y, rfl⟩
    refine ⟨pi (q n) y, ?_⟩
    have heq : pi (q m) * pi (q n) = pi (q n) := by
      rw [← map_mul, hq_le hmn]
    exact congrArg (fun T : H →L[ℂ] H ↦ T y) heq
  have hU0 : U 0 = ⊤ := by
    rw [← Submodule.range_starProjection (U 0), ← hUproj, hp0, map_one]
    exact LinearMap.range_eq_top.mpr fun x ↦ ⟨x, rfl⟩
  have hV0 : V 0 = ⊤ := by
    rw [← Submodule.range_starProjection (V 0), ← hVproj, hq0, map_one]
    exact LinearMap.range_eq_top.mpr fun x ↦ ⟨x, rfl⟩
  have hInitialPi (n : ℕ) :
      ((pi (w n))†).comp (pi (w n)) = Submodule.projectionShell U n := by
    change star (pi (w n)) * pi (w n) = _
    rw [← map_star, ← map_mul, hInitial, map_sub, hUproj, hUproj]
    rfl
  have hFinalPi (n : ℕ) :
      (pi (w n)).comp ((pi (w n))†) = Submodule.projectionShell V n := by
    change pi (w n) * star (pi (w n)) = _
    rw [← map_star, ← map_mul, hFinal, map_sub, hVproj, hVproj]
    rfl
  obtain ⟨S, T, hS, hT, _, _, hAdj, hProdU, hProdV⟩ :=
    ContinuousLinearMap.exists_strongSums_of_projectionShells
      (fun n ↦ pi (w n)) U V hUanti hVanti hU0 hV0 hInitialPi hFinalPi
  exact ⟨S, T, (⨅ n, U n).starProjection, (⨅ n, V n).starProjection,
    hS, hT, hAdj, isStarProjection_starProjection, Submodule.range_starProjection _,
    isStarProjection_starProjection, Submodule.range_starProjection _, hProdU, hProdV⟩

/-- A represented unitary satisfying the finite algebraic shell relations is
reconstructed from strong sums formed afresh on the target Hilbert space.
The complementary operator is supported exactly between the two represented
limiting fixed spaces.  In particular, this theorem never maps a strong limit
through `pi`; only the finite source identities are mapped. -/
theorem exists_represented_unitaryCompletion_of_sourceShells
    (pi : Representation A H) (e : H ≃ₗᵢ[ℂ] H)
    (p q w : ℕ → A)
    (hp : ∀ n, IsStarProjection (p n))
    (hq : ∀ n, IsStarProjection (q n))
    (hp0 : p 0 = 1) (hq0 : q 0 = 1)
    (hp_le : ∀ ⦃m n : ℕ⦄, m ≤ n → p m * p n = p n)
    (hq_le : ∀ ⦃m n : ℕ⦄, m ≤ n → q m * q n = q n)
    (hInitial : ∀ n, star (w n) * w n = p n - p (n + 1))
    (hFinal : ∀ n, w n * star (w n) = q n - q (n + 1))
    (hUnitary : ∀ n, (e : H →L[ℂ] H).comp
      (pi (p n - p (n + 1))) = pi (w n)) :
    let U : ℕ → Submodule ℂ H := fun n ↦ (pi (p n)).range
    let V : ℕ → Submodule ℂ H := fun n ↦ (pi (q n)).range
    ∃ S T P Q R : H →L[ℂ] H,
      ContinuousLinearMap.StronglyConverges
        (ContinuousLinearMap.partialSum (fun n ↦ pi (w n))) atTop S ∧
      ContinuousLinearMap.StronglyConverges
        (ContinuousLinearMap.partialSum (fun n ↦ (pi (w n))†)) atTop T ∧
      ‖S‖ ≤ 1 ∧ ‖T‖ ≤ 1 ∧ T = S† ∧
      IsStarProjection P ∧ P.range = ⨅ n, U n ∧
      IsStarProjection Q ∧ Q.range = ⨅ n, V n ∧
      (S†).comp S = 1 - P ∧ S.comp (S†) = 1 - Q ∧
      (e : H →L[ℂ] H) = S + R ∧
      R = (e : H →L[ℂ] H).comp P ∧
      (R†).comp R = P ∧ R.comp (R†) = Q ∧
      R = (Q.comp R).comp P ∧
      (∀ x, x ∈ ⨅ n, U n ↔ e x ∈ ⨅ n, V n) := by
  dsimp only
  let U : ℕ → Submodule ℂ H := fun n ↦ (pi (p n)).range
  let V : ℕ → Submodule ℂ H := fun n ↦ (pi (q n)).range
  have hpPi (n : ℕ) : IsStarProjection (pi (p n)) :=
    IsStarProjection.map_representation pi (hp n)
  have hqPi (n : ℕ) : IsStarProjection (pi (q n)) :=
    IsStarProjection.map_representation pi (hq n)
  have hUdata (n : ℕ) : ∃ (_ : (U n).HasOrthogonalProjection),
      pi (p n) = (U n).starProjection := by
    simpa [U] using
      (isStarProjection_iff_eq_starProjection_range.mp (hpPi n))
  have hVdata (n : ℕ) : ∃ (_ : (V n).HasOrthogonalProjection),
      pi (q n) = (V n).starProjection := by
    simpa [V] using
      (isStarProjection_iff_eq_starProjection_range.mp (hqPi n))
  letI hUprojection (n : ℕ) : (U n).HasOrthogonalProjection :=
    (hUdata n).choose
  letI hVprojection (n : ℕ) : (V n).HasOrthogonalProjection :=
    (hVdata n).choose
  have hUproj (n : ℕ) : pi (p n) = (U n).starProjection :=
    (hUdata n).choose_spec
  have hVproj (n : ℕ) : pi (q n) = (V n).starProjection :=
    (hVdata n).choose_spec
  have hUclosed (n : ℕ) : IsClosed (U n : Set H) :=
    ContinuousLinearMap.IsIdempotentElem.isClosed_range
      (hpPi n).isIdempotentElem
  have hVclosed (n : ℕ) : IsClosed (V n : Set H) :=
    ContinuousLinearMap.IsIdempotentElem.isClosed_range
      (hqPi n).isIdempotentElem
  letI : IsClosed ((⨅ n, U n : Submodule ℂ H) : Set H) := by
    simpa only [Submodule.coe_iInf] using isClosed_iInter hUclosed
  letI : IsClosed ((⨅ n, V n : Submodule ℂ H) : Set H) := by
    simpa only [Submodule.coe_iInf] using isClosed_iInter hVclosed
  letI : CompleteSpace (⨅ n, U n : Submodule ℂ H) := inferInstance
  letI : CompleteSpace (⨅ n, V n : Submodule ℂ H) := inferInstance
  letI : (⨅ n, U n).HasOrthogonalProjection := inferInstance
  letI : (⨅ n, V n).HasOrthogonalProjection := inferInstance
  have hUanti : Antitone U := by
    intro m n hmn
    rintro x ⟨y, rfl⟩
    refine ⟨pi (p n) y, ?_⟩
    have heq : pi (p m) * pi (p n) = pi (p n) := by
      rw [← map_mul, hp_le hmn]
    exact congrArg (fun T : H →L[ℂ] H ↦ T y) heq
  have hVanti : Antitone V := by
    intro m n hmn
    rintro x ⟨y, rfl⟩
    refine ⟨pi (q n) y, ?_⟩
    have heq : pi (q m) * pi (q n) = pi (q n) := by
      rw [← map_mul, hq_le hmn]
    exact congrArg (fun T : H →L[ℂ] H ↦ T y) heq
  have hU0 : U 0 = ⊤ := by
    rw [← Submodule.range_starProjection (U 0), ← hUproj, hp0, map_one]
    exact LinearMap.range_eq_top.mpr fun x ↦ ⟨x, rfl⟩
  have hV0 : V 0 = ⊤ := by
    rw [← Submodule.range_starProjection (V 0), ← hVproj, hq0, map_one]
    exact LinearMap.range_eq_top.mpr fun x ↦ ⟨x, rfl⟩
  have hInitialPi (n : ℕ) :
      ((pi (w n))†).comp (pi (w n)) = Submodule.projectionShell U n := by
    change star (pi (w n)) * pi (w n) = _
    rw [← map_star, ← map_mul, hInitial, map_sub, hUproj, hUproj]
    rfl
  have hFinalPi (n : ℕ) :
      (pi (w n)).comp ((pi (w n))†) = Submodule.projectionShell V n := by
    change pi (w n) * star (pi (w n)) = _
    rw [← map_star, ← map_mul, hFinal, map_sub, hVproj, hVproj]
    rfl
  have hShell (n : ℕ) : pi (p n - p (n + 1)) =
      Submodule.projectionShell U n := by
    rw [map_sub, hUproj, hUproj]
    rfl
  obtain ⟨S, T, hS, hT, hSnorm, hTnorm, hAdj, hProdU, hProdV,
      hcompletion⟩ :=
    ContinuousLinearMap.exists_strongSums_unitaryCompletion_of_projectionShells
      e (fun n ↦ pi (w n)) U V hUanti hVanti hU0 hV0 hInitialPi hFinalPi
        fun n ↦ by
          rw [← hShell]
          exact hUnitary n
  let P : H →L[ℂ] H := (⨅ n, U n).starProjection
  let Q : H →L[ℂ] H := (⨅ n, V n).starProjection
  let R : H →L[ℂ] H := (e : H →L[ℂ] H).comp P
  change (e : H →L[ℂ] H) = S + R ∧
      R = (e : H →L[ℂ] H).comp P ∧
      (R†).comp R = P ∧ R.comp (R†) = Q ∧
      R = (Q.comp R).comp P ∧
      (∀ x, x ∈ ⨅ n, U n ↔ e x ∈ ⨅ n, V n) at hcompletion
  exact ⟨S, T, P, Q, R, hS, hT, hSnorm, hTnorm, hAdj,
    isStarProjection_starProjection, Submodule.range_starProjection _,
    isStarProjection_starProjection, Submodule.range_starProjection _,
    hProdU, hProdV, hcompletion⟩

end MathlibAnnex.Analysis.CStarAlgebra
