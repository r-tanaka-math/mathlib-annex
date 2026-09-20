import MathlibAnnex.Analysis.CStarAlgebra.Cyclic
import MathlibAnnex.Analysis.CStarAlgebra.Generated
import MathlibAnnex.Analysis.CStarAlgebra.Representation.GeneratedReduction
import Mathlib.Analysis.CStarAlgebra.Spectrum
import MathlibAnnex.Analysis.CStarAlgebra.AtomicConstruction.Concrete

/-!
# Reduction for the Nmk norm-closed generated concrete target

A closed subspace which reduces every nominated generator reduces every
element of the concrete norm-closed generated algebra.  The proof uses the
commutant of the orthogonal projection and density of the algebraic star
algebra; no operator-topology closure is asserted.
-/

set_option autoImplicit false

noncomputable section

open Topology
open scoped CStarAlgebra InnerProduct

namespace MathlibAnnex.CStarAlgebra.AtomicConstruction

open MathlibAnnex.Analysis.CStarAlgebra

universe u v w z

variable {A : Type u} [CStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {J : Type w}
variable {K : Type z} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

/-- Reduction by the represented source and every additional generator
extends to the whole concrete target by norm-closed generation. -/
theorem reduces_concreteTarget_of_generators
    (pi : Representation A H) (U : J → H →L[ℂ] H)
    (rho : Representation (concreteTarget pi U) K)
    (M : Submodule ℂ K) (hMclosed : IsClosed (M : Set K))
    (hsource : ∀ a : A, M.Reduces (rho (sourceHom pi U a)))
    (hgenerator : ∀ j : J, M.Reduces (rho (generator pi U j))) :
    ∀ x : concreteTarget pi U, M.Reduces (rho x) := by
  letI : CompleteSpace M := hMclosed.completeSpace_coe
  letI : M.HasOrthogonalProjection := inferInstance
  let P : K →L[ℂ] K := M.starProjection
  let C : StarSubalgebra ℂ (concreteTarget pi U) :=
    (StarSubalgebra.centralizer ℂ ({P} : Set (K →L[ℂ] K))).comap rho
  have hCclosed : IsClosed (C : Set (concreteTarget pi U)) := by
    change IsClosed (rho ⁻¹'
      (StarSubalgebra.centralizer ℂ ({P} : Set (K →L[ℂ] K)) :
        Set (K →L[ℂ] K)))
    have hcentralizer : IsClosed
        (StarSubalgebra.centralizer ℂ ({P} : Set (K →L[ℂ] K)) :
          Set (K →L[ℂ] K)) := by
      rw [StarSubalgebra.coe_centralizer]
      exact Set.isClosed_centralizer _
    exact hcentralizer.preimage (map_continuous rho)
  have memC_of_reduces {x : concreteTarget pi U}
      (hx : M.Reduces (rho x)) : x ∈ C := by
    change rho x ∈ StarSubalgebra.centralizer ℂ ({P} : Set (K →L[ℂ] K))
    rw [StarSubalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst g
    have hcomm := (Submodule.reduces_iff_starProjection_commute).mp hx
    constructor
    · exact hcomm
    · have hpstar : star P = P := by
        change P† = P
        exact M.starProjection_isSymmetric.clm_adjoint_eq
      rw [hpstar]
      exact hcomm
  let S : Set (H →L[ℂ] H) := Set.range pi ∪ Set.range U
  let B : StarSubalgebra ℂ (H →L[ℂ] H) := StarAlgebra.adjoin ℂ S
  have hlift (x : H →L[ℂ] H) (hx : x ∈ B) :
      (⟨x, StarSubalgebra.le_topologicalClosure B hx⟩ : concreteTarget pi U) ∈ C := by
    induction hx using StarAlgebra.adjoin_induction with
    | mem x hx =>
        rcases hx with hx | hx
        · rcases hx with ⟨a, rfl⟩
          exact memC_of_reduces (hsource a)
        · rcases hx with ⟨j, rfl⟩
          exact memC_of_reduces (hgenerator j)
    | algebraMap c =>
        change (algebraMap ℂ (concreteTarget pi U) c) ∈ C
        exact C.algebraMap_mem c
    | add x y hx hy hxc hyc =>
        change (⟨x, StarSubalgebra.le_topologicalClosure B hx⟩ :
            concreteTarget pi U) +
          ⟨y, StarSubalgebra.le_topologicalClosure B hy⟩ ∈ C
        exact C.add_mem hxc hyc
    | mul x y hx hy hxc hyc =>
        change (⟨x, StarSubalgebra.le_topologicalClosure B hx⟩ :
            concreteTarget pi U) *
          ⟨y, StarSubalgebra.le_topologicalClosure B hy⟩ ∈ C
        exact C.mul_mem hxc hyc
    | star x hx hxc =>
        change star (⟨x, StarSubalgebra.le_topologicalClosure B hx⟩ :
          concreteTarget pi U) ∈ C
        exact star_mem hxc
  let inclusion : B →⋆ₐ[ℂ] concreteTarget pi U :=
    StarSubalgebra.inclusion (StarSubalgebra.le_topologicalClosure B)
  have hinclusion (x : B) : inclusion x ∈ C := by
    exact hlift x x.property
  have hdense : DenseRange inclusion := by
    change DenseRange
      (Set.inclusion (StarSubalgebra.le_topologicalClosure B))
    apply (denseRange_inclusion_iff _).2
    change closure (B : Set (H →L[ℂ] H)) ⊆ closure (B : Set (H →L[ℂ] H))
    exact le_rfl
  intro x
  have hxC : x ∈ C := by
    have hrange : Set.range inclusion ⊆ (C : Set (concreteTarget pi U)) := by
      rintro _ ⟨y, rfl⟩
      exact hinclusion y
    apply closure_minimal hrange hCclosed
    rw [hdense.closure_range]
    exact Set.mem_univ x
  apply Submodule.reduces_iff_starProjection_commute.mpr
  change rho x ∈ StarSubalgebra.centralizer ℂ
    ({P} : Set (K →L[ℂ] K)) at hxC
  rw [StarSubalgebra.mem_centralizer_iff] at hxC
  exact (hxC P (Set.mem_singleton P)).1

/-- An isometric equivalence which intertwines the represented source and all
nominated generators intertwines every element of the norm-closed concrete
target.  Closure is taken in operator norm; no strong-operator continuity is
used. -/
theorem intertwines_concreteTarget_of_generators
    (pi : Representation A H) (U : J → H →L[ℂ] H)
    (e : H ≃ₗᵢ[ℂ] K) (rho : Representation (concreteTarget pi U) K)
    (hsource : ∀ a : A,
      (e : H →L[ℂ] K).comp (pi a) =
        (rho (sourceHom pi U a)).comp (e : H →L[ℂ] K))
    (hgenerator : ∀ j : J,
      (e : H →L[ℂ] K).comp (U j) =
        (rho (generator pi U j)).comp (e : H →L[ℂ] K)) :
    ∀ x : concreteTarget pi U,
      (e : H →L[ℂ] K).comp (ambientInclusion pi U x) =
        (rho x).comp (e : H →L[ℂ] K) := by
  let S : Set (H →L[ℂ] H) := Set.range pi ∪ Set.range U
  let B : StarSubalgebra ℂ (H →L[ℂ] H) := StarAlgebra.adjoin ℂ S
  let good : Set (concreteTarget pi U) := {x |
    (e : H →L[ℂ] K).comp (ambientInclusion pi U x) =
      (rho x).comp (e : H →L[ℂ] K)}
  have hgoodClosed : IsClosed good := by
    apply isClosed_eq
    · exact Continuous.const_clm_comp
        (map_continuous (ambientInclusion pi U)) (e : H →L[ℂ] K)
    · exact Continuous.clm_comp_const (map_continuous rho) (e : H →L[ℂ] K)
  have hlift (x : H →L[ℂ] H) (hx : x ∈ B) :
      (⟨x, StarSubalgebra.le_topologicalClosure B hx⟩ : concreteTarget pi U) ∈
        good := by
    induction hx using StarAlgebra.adjoin_induction with
    | mem x hx =>
        rcases hx with hx | hx
        · rcases hx with ⟨a, rfl⟩
          exact hsource a
        · rcases hx with ⟨j, rfl⟩
          exact hgenerator j
    | algebraMap c =>
        change (e : H →L[ℂ] K).comp
            (algebraMap ℂ (H →L[ℂ] H) c) =
          (rho (algebraMap ℂ (concreteTarget pi U) c)).comp
            (e : H →L[ℂ] K)
        apply ContinuousLinearMap.ext
        intro z
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
        have hc : rho (algebraMap ℂ (concreteTarget pi U) c) =
            algebraMap ℂ (K →L[ℂ] K) c := rho.toAlgHom.commutes c
        rw [hc]
        simpa using e.map_smul c z
    | add x y hx hy hxc hyc =>
        change (e : H →L[ℂ] K).comp x =
          (rho (⟨x, StarSubalgebra.le_topologicalClosure B hx⟩ :
            concreteTarget pi U)).comp (e : H →L[ℂ] K) at hxc
        change (e : H →L[ℂ] K).comp y =
          (rho (⟨y, StarSubalgebra.le_topologicalClosure B hy⟩ :
            concreteTarget pi U)).comp (e : H →L[ℂ] K) at hyc
        change (e : H →L[ℂ] K).comp (x + y) =
          (rho ((⟨x, StarSubalgebra.le_topologicalClosure B hx⟩ :
              concreteTarget pi U) +
            ⟨y, StarSubalgebra.le_topologicalClosure B hy⟩)).comp
              (e : H →L[ℂ] K)
        rw [map_add, ContinuousLinearMap.comp_add,
          ContinuousLinearMap.add_comp, hxc, hyc]
    | mul x y hx hy hxc hyc =>
        change (e : H →L[ℂ] K).comp x =
          (rho (⟨x, StarSubalgebra.le_topologicalClosure B hx⟩ :
            concreteTarget pi U)).comp (e : H →L[ℂ] K) at hxc
        change (e : H →L[ℂ] K).comp y =
          (rho (⟨y, StarSubalgebra.le_topologicalClosure B hy⟩ :
            concreteTarget pi U)).comp (e : H →L[ℂ] K) at hyc
        change (e : H →L[ℂ] K).comp (x * y) =
          (rho ((⟨x, StarSubalgebra.le_topologicalClosure B hx⟩ :
              concreteTarget pi U) *
            ⟨y, StarSubalgebra.le_topologicalClosure B hy⟩)).comp
              (e : H →L[ℂ] K)
        rw [map_mul]
        change (e : H →L[ℂ] K).comp (x.comp y) =
          ((rho (⟨x, StarSubalgebra.le_topologicalClosure B hx⟩ :
              concreteTarget pi U)).comp
            (rho (⟨y, StarSubalgebra.le_topologicalClosure B hy⟩ :
              concreteTarget pi U))).comp (e : H →L[ℂ] K)
        calc
          (e : H →L[ℂ] K).comp (x.comp y) =
              ((e : H →L[ℂ] K).comp x).comp y :=
            (ContinuousLinearMap.comp_assoc _ _ _).symm
          _ = ((rho (⟨x, StarSubalgebra.le_topologicalClosure B hx⟩ :
                concreteTarget pi U)).comp (e : H →L[ℂ] K)).comp y := by
            rw [hxc]
          _ = (rho (⟨x, StarSubalgebra.le_topologicalClosure B hx⟩ :
                concreteTarget pi U)).comp
              ((e : H →L[ℂ] K).comp y) :=
            ContinuousLinearMap.comp_assoc _ _ _
          _ = (rho (⟨x, StarSubalgebra.le_topologicalClosure B hx⟩ :
                concreteTarget pi U)).comp
              ((rho (⟨y, StarSubalgebra.le_topologicalClosure B hy⟩ :
                concreteTarget pi U)).comp (e : H →L[ℂ] K)) := by
            rw [hyc]
          _ = ((rho (⟨x, StarSubalgebra.le_topologicalClosure B hx⟩ :
                concreteTarget pi U)).comp
              (rho (⟨y, StarSubalgebra.le_topologicalClosure B hy⟩ :
                concreteTarget pi U))).comp (e : H →L[ℂ] K) :=
            (ContinuousLinearMap.comp_assoc _ _ _).symm
    | star x hx hxc =>
        change (e : H →L[ℂ] K).comp x =
          (rho (⟨x, StarSubalgebra.le_topologicalClosure B hx⟩ :
            concreteTarget pi U)).comp (e : H →L[ℂ] K) at hxc
        change (e : H →L[ℂ] K).comp (star x) =
          (rho (star (⟨x, StarSubalgebra.le_topologicalClosure B hx⟩ :
            concreteTarget pi U))).comp (e : H →L[ℂ] K)
        rw [map_star, ContinuousLinearMap.star_eq_adjoint,
          ContinuousLinearMap.star_eq_adjoint]
        exact e.intertwines_adjoint hxc
  let inclusion : B →⋆ₐ[ℂ] concreteTarget pi U :=
    StarSubalgebra.inclusion (StarSubalgebra.le_topologicalClosure B)
  have hdense : DenseRange inclusion := by
    change DenseRange (Set.inclusion (StarSubalgebra.le_topologicalClosure B))
    apply (denseRange_inclusion_iff _).2
    change closure (B : Set (H →L[ℂ] H)) ⊆ closure (B : Set (H →L[ℂ] H))
    exact le_rfl
  intro x
  have hrange : Set.range inclusion ⊆ good := by
    rintro _ ⟨y, rfl⟩
    exact hlift y y.property
  apply closure_minimal hrange hgoodClosed
  rw [hdense.closure_range]
  exact Set.mem_univ x

end MathlibAnnex.CStarAlgebra.AtomicConstruction
