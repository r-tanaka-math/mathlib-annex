import MathlibAnnex.Analysis.CStarAlgebra.CAR.TracialCyclic
import MathlibAnnex.Analysis.CStarAlgebra.AtomicConstruction.GeneratedExt

/-!
# Transport between target-cyclic realizations of the source trace

Source cyclicity is proved, not assumed. The source intertwiner passes to
both strong shell sums, and norm generation then gives target intertwining.
-/

set_option autoImplicit false

open Filter Topology
open scoped InnerProduct

namespace MathlibAnnex.CStarAlgebra.CAR

open MathlibAnnex.Analysis.CStarAlgebra

universe v w
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

set_option maxHeartbeats 1000000 in
/-- On a target-cyclic realization of the trace, the source shell sums
converge strongly to the actual represented generator and its adjoint. -/
theorem stronglyConverges_shell_sums_of_trace_of_cyclic
    (family : RepresentativeShellFamily)
    (ρ : Representation (ShellFamilyTarget family) H) (ξ : H)
    (hξ : ∀ a, Representation.vectorFunctional
      (ρ.comp (shellFamilySourceHom family)) ξ a = trace a)
    (hcyclic : DenseRange (fun a ↦ ρ a ξ))
    (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
    ContinuousLinearMap.StronglyConverges
      (ContinuousLinearMap.partialSum (fun n ↦
        ρ (shellFamilySourceHom family ((representativeShellData family i).link n))))
      atTop (ρ (shellFamilyGenerator family i)) ∧
    ContinuousLinearMap.StronglyConverges
      (ContinuousLinearMap.partialSum (fun n ↦
        (ρ (shellFamilySourceHom family ((representativeShellData family i).link n)))†))
      atTop ((ρ (shellFamilyGenerator family i))†) := by
  obtain ⟨S, T, hS, hT, _, _, _, heq⟩ :=
    exists_shell_sums_eq_on_cyclicSubspace family ρ ξ hξ i
  have htop := cyclicSubspace_eq_top_of_trace_of_cyclic family ρ ξ hξ hcyclic
  have hall (x : H) : ρ (shellFamilyGenerator family i) x = S x ∧
      ((ρ (shellFamilyGenerator family i))†) x = T x := by
    apply heq x
    rw [htop]
    trivial
  have hS_eq : S = ρ (shellFamilyGenerator family i) :=
    ContinuousLinearMap.ext fun x ↦ (hall x).1.symm
  have hT_eq : T = (ρ (shellFamilyGenerator family i))† :=
    ContinuousLinearMap.ext fun x ↦ (hall x).2.symm
  exact ⟨hS_eq ▸ hS, hT_eq ▸ hT⟩

private theorem comp_partialSum_eq_partialSum_comp
    (e : H →L[ℂ] K) (A : ℕ → H →L[ℂ] H) (B : ℕ → K →L[ℂ] K)
    (h : ∀ n, e.comp (A n) = (B n).comp e) (N : ℕ) :
    e.comp (ContinuousLinearMap.partialSum A N) =
      (ContinuousLinearMap.partialSum B N).comp e := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.partialSum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact congrArg (fun T : H →L[ℂ] K ↦ T x) (h n)

/-- Two cyclic target representations of the source trace are pointed
unitarily equivalent on the whole target, including every added generator. -/
theorem exists_pointed_unitary_of_trace_of_cyclic
    (family : RepresentativeShellFamily)
    (ρ : Representation (ShellFamilyTarget family) H)
    (σ : Representation (ShellFamilyTarget family) K) (ξ : H) (η : K)
    (hξ : ∀ a, Representation.vectorFunctional
      (ρ.comp (shellFamilySourceHom family)) ξ a = trace a)
    (hη : ∀ a, Representation.vectorFunctional
      (σ.comp (shellFamilySourceHom family)) η a = trace a)
    (hρ : DenseRange (fun a ↦ ρ a ξ)) (hσ : DenseRange (fun a ↦ σ a η)) :
    ∃ e : H ≃ₗᵢ[ℂ] K, e ξ = η ∧
      ∀ a, (e : H →L[ℂ] K).comp (ρ a) = (σ a).comp (e : H →L[ℂ] K) := by
  let ρB := ρ.comp (shellFamilySourceHom family)
  let σB := σ.comp (shellFamilySourceHom family)
  have hdρ : DenseRange (StarAlgHom.orbitMap ρB ξ) :=
    denseRange_source_orbit_of_trace_of_cyclic family ρ ξ hξ hρ
  have hdσ : DenseRange (StarAlgHom.orbitMap σB η) :=
    denseRange_source_orbit_of_trace_of_cyclic family σ η hη hσ
  have hstate (a : Limit) : inner ℂ ξ (ρB a ξ) = inner ℂ η (σB a η) :=
    (hξ a).trans (hη a).symm
  obtain ⟨e, he, _⟩ :=
    StarAlgHom.existsUnique_pointedCyclicTransport ρB σB ξ η hdρ hdσ hstate
  have hgen (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
      (e : H →L[ℂ] K).comp (ρ (shellFamilyGenerator family i)) =
        (σ (shellFamilyGenerator family i)).comp (e : H →L[ℂ] K) := by
    have hρsum := (stronglyConverges_shell_sums_of_trace_of_cyclic family ρ ξ hξ hρ i).1
    have hσsum := (stronglyConverges_shell_sums_of_trace_of_cyclic family σ η hη hσ i).1
    apply ContinuousLinearMap.intertwines_strongLimits (e : H →L[ℂ] K)
      (e : H →L[ℂ] K) hρsum hσsum
    exact comp_partialSum_eq_partialSum_comp _ _ _
      (fun n ↦ he.2.2 ((representativeShellData family i).link n))
  exact ⟨e, he.2.1,
    MathlibAnnex.CStarAlgebra.AtomicConstruction.intertwines_of_source_of_generators
      selectedAtomicRepresentation (shellFamilyLinks family) ρ σ e he.2.2 hgen⟩

end MathlibAnnex.CStarAlgebra.CAR
