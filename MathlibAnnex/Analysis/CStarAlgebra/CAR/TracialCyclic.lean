import MathlibAnnex.Analysis.CStarAlgebra.CAR.AtomicEndpoint
import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceFlag
import MathlibAnnex.Analysis.CStarAlgebra.AtomicConstruction.GeneratedReduction
import MathlibAnnex.Analysis.InnerProductSpace.Reduction

/-!
# A trace-cyclic subspace reduces the same concrete target

This is the connection to the already constructed algebra. We do not infer
a universal mapping property from the finite shell relations. Instead, an
existing representation of the actual target is used, and its source-cyclic
subspace is shown to reduce every target generator and its adjoint.
-/

set_option autoImplicit false

open Filter Topology
open scoped InnerProduct

namespace MathlibAnnex.CStarAlgebra.CAR

open MathlibAnnex.Analysis.CStarAlgebra

universe v
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An actual added generator of the fixed shell-family target. -/
noncomputable def shellFamilyGenerator (family : RepresentativeShellFamily)
    (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) : ShellFamilyTarget family :=
  MathlibAnnex.CStarAlgebra.AtomicConstruction.generator
    selectedAtomicRepresentation (shellFamilyLinks family) i

/-- The generator is unitary as an element of the actual target, not only
as an operator in its ambient realization. -/
theorem shellFamilyGenerator_mem_unitary (family : RepresentativeShellFamily)
    (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
    shellFamilyGenerator family i ∈ unitary (ShellFamilyTarget family) := by
  rw [Unitary.mem_iff]
  constructor
  · apply Subtype.ext
    exact (shellFamilyLinks_unitary family i).1
  · apply Subtype.ext
    exact (shellFamilyLinks_unitary family i).2

@[simp]
theorem shellFamilyGenerator_root (family : RepresentativeShellFamily) :
    shellFamilyGenerator family completedRootPureState.classOf = 1 := by
  apply Subtype.ext
  exact shellFamilyLinks_root family

/-- A compact interface for the inherited five-operator reconstruction:
on the trace-cyclic subspace, both residual terms vanish. -/
theorem exists_shell_sums_eq_on_cyclicSubspace (family : RepresentativeShellFamily)
    (ρ : Representation (ShellFamilyTarget family) H) (ξ : H)
    (hξ : ∀ a, Representation.vectorFunctional
      (ρ.comp (shellFamilySourceHom family)) ξ a = trace a)
    (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
    let σ := ρ.comp (shellFamilySourceHom family)
    let M := Representation.cyclicSubspace σ ξ
    ∃ S T : H →L[ℂ] H,
      ContinuousLinearMap.StronglyConverges
        (ContinuousLinearMap.partialSum
          (fun n ↦ σ ((representativeShellData family i).link n))) atTop S ∧
      ContinuousLinearMap.StronglyConverges
        (ContinuousLinearMap.partialSum
          (fun n ↦ (σ ((representativeShellData family i).link n))†)) atTop T ∧
      ‖S‖ ≤ 1 ∧ ‖T‖ ≤ 1 ∧ T = S† ∧
      ∀ x ∈ M, ρ (shellFamilyGenerator family i) x = S x ∧
        ((ρ (shellFamilyGenerator family i))†) x = T x := by
  dsimp only
  let σ := ρ.comp (shellFamilySourceHom family)
  let M := Representation.cyclicSubspace σ ξ
  obtain ⟨S, T, P, Q, R, hS, hT, hSnorm, hTnorm, hAdj,
      hP, hPrange, hQ, hQrange, _, _, hgen, hR, _, _, hsupport, _⟩ :=
    exists_targetShellReconstruction family (shellFamilyLinks family)
      (shellFamilyLinks_unitary family) (shellFamilyLinks_sourceShell family) ρ i
  have hPzero : ∀ x ∈ M, P x = 0 :=
    projection_eq_zero_on_cyclicSubspace σ ξ (transportedFlag family i)
      (isStarProjection_transportedFlag family i)
      (tendsto_transportedFlag_orbit_zero family i σ ξ hξ) P hP hPrange
  have hQzero : ∀ x ∈ M, Q x = 0 :=
    projection_eq_zero_on_cyclicSubspace σ ξ rootFlag isStarProjection_rootFlag
      (tendsto_rootFlag_orbit_zero σ ξ hξ) Q hQ hQrange
  change ρ (shellFamilyGenerator family i) = S + R at hgen
  change R = (ρ (shellFamilyGenerator family i)).comp P at hR
  have hRzero (x : H) (hx : x ∈ M) : R x = 0 := by
    rw [hR, ContinuousLinearMap.comp_apply, hPzero x hx, map_zero]
  have hstar : star R = P * star R * Q := by
    change R = Q * R * P at hsupport
    have h := congrArg star hsupport
    simpa only [star_mul, hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq,
      mul_assoc] using h
  have hRadjoint_zero (x : H) (hx : x ∈ M) : (R†) x = 0 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, hstar]
    change P ((star R) (Q x)) = 0
    rw [hQzero x hx, map_zero, map_zero]
  refine ⟨S, T, hS, hT, hSnorm, hTnorm, hAdj, ?_⟩
  intro x hx
  constructor
  · rw [hgen, ContinuousLinearMap.add_apply, hRzero x hx, add_zero]
  · rw [hgen, map_add, ContinuousLinearMap.add_apply,
      hRadjoint_zero x hx, add_zero, ← hAdj]

/-- No target irreducibility is used: the source trace alone makes the
source-cyclic subspace reducing for the actual target. -/
theorem reduces_cyclicSubspace_of_trace (family : RepresentativeShellFamily)
    (ρ : Representation (ShellFamilyTarget family) H) (ξ : H)
    (hξ : ∀ a, Representation.vectorFunctional
      (ρ.comp (shellFamilySourceHom family)) ξ a = trace a) :
    ρ.Reduces (Representation.cyclicSubspace
      (ρ.comp (shellFamilySourceHom family)) ξ) := by
  let σ := ρ.comp (shellFamilySourceHom family)
  let M := Representation.cyclicSubspace σ ξ
  have hMclosed : IsClosed (M : Set H) := Representation.isClosed_cyclicSubspace σ ξ
  have hsource (a : Limit) :
      M.Reduces (ρ (shellFamilySourceHom family a)) := by
    constructor
    · intro x hx
      exact Representation.map_mem_cyclicSubspace σ ξ a hx
    · intro x hx
      exact Representation.adjoint_mem_cyclicSubspace σ ξ a hx
  have hgenerator (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
      M.Reduces (ρ (shellFamilyGenerator family i)) := by
    obtain ⟨S, T, hS, hT, _, _, hAdj, heq⟩ :=
      exists_shell_sums_eq_on_cyclicSubspace family ρ ξ hξ i
    have hW (n : ℕ) : M.Reduces (σ ((representativeShellData family i).link n)) :=
      hsource ((representativeShellData family i).link n)
    have hSreduce : M.Reduces S :=
      Submodule.Reduces.of_stronglyConverges_partialSum hMclosed hW hS hT hAdj
    constructor
    · intro x hx
      rw [(heq x hx).1]
      exact hSreduce.1 hx
    · intro x hx
      rw [(heq x hx).2, hAdj]
      exact hSreduce.2 hx
  have hall := MathlibAnnex.CStarAlgebra.AtomicConstruction.reduces_concreteTarget_of_generators
    selectedAtomicRepresentation (shellFamilyLinks family) ρ M hMclosed hsource hgenerator
  refine ⟨hMclosed, ?_⟩
  intro a x hx
  exact ⟨(hall a).1 hx, (hall a).2 hx⟩

/-- In a cyclic representation extending the source trace, source cyclicity
already equals target cyclicity. -/
theorem cyclicSubspace_eq_top_of_trace_of_cyclic (family : RepresentativeShellFamily)
    (ρ : Representation (ShellFamilyTarget family) H) (ξ : H)
    (hξ : ∀ a, Representation.vectorFunctional
      (ρ.comp (shellFamilySourceHom family)) ξ a = trace a)
    (hcyclic : DenseRange (fun a ↦ ρ a ξ)) :
    Representation.cyclicSubspace (ρ.comp (shellFamilySourceHom family)) ξ = ⊤ := by
  let σ := ρ.comp (shellFamilySourceHom family)
  let M := Representation.cyclicSubspace σ ξ
  have hreduce := reduces_cyclicSubspace_of_trace family ρ ξ hξ
  have hmem : ξ ∈ M := Representation.self_mem_cyclicSubspace σ ξ
  apply top_unique
  intro x _
  have hsubset : Set.range (fun a ↦ ρ a ξ) ⊆ (M : Set H) := by
    rintro _ ⟨a, rfl⟩
    exact (hreduce.2 a ξ hmem).1
  apply closure_minimal hsubset hreduce.1
  rw [hcyclic.closure_range]
  exact Set.mem_univ x

theorem denseRange_source_orbit_of_trace_of_cyclic (family : RepresentativeShellFamily)
    (ρ : Representation (ShellFamilyTarget family) H) (ξ : H)
    (hξ : ∀ a, Representation.vectorFunctional
      (ρ.comp (shellFamilySourceHom family)) ξ a = trace a)
    (hcyclic : DenseRange (fun a ↦ ρ a ξ)) :
    DenseRange (fun b ↦ ρ (shellFamilySourceHom family b) ξ) := by
  have htop := cyclicSubspace_eq_top_of_trace_of_cyclic family ρ ξ hξ hcyclic
  have hsets := congrArg (fun M : Submodule ℂ H ↦ (M : Set H)) htop
  apply dense_iff_closure_eq.mpr
  simpa [Representation.cyclicSubspace, Submodule.topologicalClosure_coe,
    LinearMap.coe_range, Representation.orbitLinearMap] using hsets

/-- Separability comes from the actual CAR orbit; the full target algebra is
not assumed norm separable. -/
theorem separableSpace_of_trace_of_cyclic (family : RepresentativeShellFamily)
    (ρ : Representation (ShellFamilyTarget family) H) (ξ : H)
    (hξ : ∀ a, Representation.vectorFunctional
      (ρ.comp (shellFamilySourceHom family)) ξ a = trace a)
    (hcyclic : DenseRange (fun a ↦ ρ a ξ)) : TopologicalSpace.SeparableSpace H := by
  have hdense := denseRange_source_orbit_of_trace_of_cyclic family ρ ξ hξ hcyclic
  let σ := ρ.comp (shellFamilySourceHom family)
  exact hdense.separableSpace
    (((ContinuousLinearMap.apply ℂ H ξ).comp
      (Representation.continuousLinearMap σ)).continuous)

end MathlibAnnex.CStarAlgebra.CAR
