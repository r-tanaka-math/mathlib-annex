import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceExtensionUnique
import MathlibAnnex.Analysis.CStarAlgebra.State.Centralizer
import Mathlib.Analysis.CStarAlgebra.Unitary.Span

/-!
# The unique extension is tracial on the entire target

Uniqueness makes the extension invariant under source unitary conjugation.
Source unitaries span CAR. Strong shell sums then put every added generator
in the state centralizer, and norm generation completes the argument.
-/

set_option autoImplicit false

open Filter Topology
open scoped ComplexOrder InnerProduct

namespace MathlibAnnex.CStarAlgebra.CAR

open MathlibAnnex.Analysis.CStarAlgebra

private theorem trace_star_unitary_mul_mul (u : unitary Limit) (b : Limit) :
    trace (star (u : Limit) * b * (u : Limit)) = trace b := by
  rw [trace_mul_comm (star (u : Limit) * b) (u : Limit), ← mul_assoc,
    u.property.2, one_mul]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The vector functional of the chosen target-state GNS is its state. -/
theorem vectorFunctional_tracialRepresentation (family : RepresentativeShellFamily) :
    Representation.vectorFunctional (tracialRepresentation family) (tracialVector family) =
      traceExtension family := by
  ext a
  exact inner_tracialVector_tracialRepresentation family a

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 5000000 in
/-- Conjugation by any source unitary fixes the state on the full target. -/
theorem traceExtension_star_unitary_mul_mul (family : RepresentativeShellFamily)
    (u : unitary Limit) (a : ShellFamilyTarget family) :
    traceExtension family
      (star (shellFamilySourceHom family (u : Limit)) * a *
        shellFamilySourceHom family (u : Limit)) = traceExtension family a := by
  let ζ := tracialRepresentation family
    (shellFamilySourceHom family (u : Limit)) (tracialVector family)
  let ψ := Representation.vectorFunctional (tracialRepresentation family) ζ
  have hζ : ‖ζ‖ = 1 := by
    change ‖((tracialRepresentation family).comp (shellFamilySourceHom family))
      (u : Limit) (tracialVector family)‖ = 1
    rw [(((tracialRepresentation family).comp (shellFamilySourceHom family))
      (u : Limit)).norm_map_of_mem_unitary
        (Unitary.map_mem ((tracialRepresentation family).comp
          (shellFamilySourceHom family)) u.property)]
    exact norm_tracialVector family
  have hψstate : ψ ∈
      MathlibAnnex.Analysis.CStarAlgebra.stateSpace (ShellFamilyTarget family) :=
    vectorFunctional_mem_stateSpace (tracialRepresentation family) ζ hζ
  have hψsource (b : Limit) : ψ (shellFamilySourceHom family b) = trace b := by
    change Representation.vectorFunctional (tracialRepresentation family)
      (tracialRepresentation family (shellFamilySourceHom family (u : Limit))
        (tracialVector family)) (shellFamilySourceHom family b) = trace b
    calc
      _ = Representation.vectorFunctional (tracialRepresentation family)
          (tracialVector family)
          (star (shellFamilySourceHom family (u : Limit)) *
            shellFamilySourceHom family b * shellFamilySourceHom family (u : Limit)) :=
        Representation.vectorFunctional_map_apply (tracialRepresentation family)
          (tracialVector family) (shellFamilySourceHom family (u : Limit))
          (shellFamilySourceHom family b)
      _ = traceExtension family
          (star (shellFamilySourceHom family (u : Limit)) *
            shellFamilySourceHom family b * shellFamilySourceHom family (u : Limit)) := by
        exact inner_tracialVector_tracialRepresentation family
          (star (shellFamilySourceHom family (u : Limit)) *
            shellFamilySourceHom family b * shellFamilySourceHom family (u : Limit))
      _ = trace (star (u : Limit) * b * (u : Limit)) := by
        have hmap :
            star (shellFamilySourceHom family (u : Limit)) *
              shellFamilySourceHom family b * shellFamilySourceHom family (u : Limit) =
                shellFamilySourceHom family (star (u : Limit) * b * (u : Limit)) := by
          simp only [map_mul, map_star]
        exact (congrArg (traceExtension family) hmap).trans
          (traceExtension_shellFamilySourceHom family (star (u : Limit) * b * (u : Limit)))
      _ = trace b := trace_star_unitary_mul_mul u b
  have hψ : ψ = traceExtension family :=
    eq_traceExtension_of_mem_stateSpace_of_apply_shellFamilySourceHom_eq_trace family ψ hψstate hψsource
  have hvalue := congrArg (fun f : ShellFamilyTarget family →L[ℂ] ℂ ↦ f a) hψ
  change Representation.vectorFunctional (tracialRepresentation family)
    (tracialRepresentation family (shellFamilySourceHom family (u : Limit))
      (tracialVector family)) a = _ at hvalue
  calc
    traceExtension family
        (star (shellFamilySourceHom family (u : Limit)) * a *
          shellFamilySourceHom family (u : Limit)) =
      Representation.vectorFunctional (tracialRepresentation family) (tracialVector family)
        (star (shellFamilySourceHom family (u : Limit)) * a *
          shellFamilySourceHom family (u : Limit)) := by
        exact (inner_tracialVector_tracialRepresentation family
          (star (shellFamilySourceHom family (u : Limit)) * a *
            shellFamilySourceHom family (u : Limit))).symm
    _ = Representation.vectorFunctional (tracialRepresentation family)
        (tracialRepresentation family (shellFamilySourceHom family (u : Limit))
          (tracialVector family)) a :=
      (Representation.vectorFunctional_map_apply (tracialRepresentation family)
        (tracialVector family) (shellFamilySourceHom family (u : Limit)) a).symm
    _ = traceExtension family a := hvalue

private theorem unitary_conjugate_left_mul {B : Type*} [Monoid B] [Star B]
    (v a : B) (hv : star v * v = 1) : star v * (v * a) * v = a * v := by
  rw [← mul_assoc (star v) v a, hv, one_mul]

set_option maxHeartbeats 1000000 in
private theorem traceExtension_unitary_mul (family : RepresentativeShellFamily)
    (u : unitary Limit) (a : ShellFamilyTarget family) :
    traceExtension family (shellFamilySourceHom family (u : Limit) * a) =
      traceExtension family (a * shellFamilySourceHom family (u : Limit)) := by
  let v := shellFamilySourceHom family (u : Limit)
  have hv : star v * v = 1 :=
    (Unitary.map_mem (shellFamilySourceHom family) u.property).1
  exact (traceExtension_star_unitary_mul_mul family u (v * a)).symm.trans
    (congrArg (traceExtension family) (unitary_conjugate_left_mul v a hv))



private theorem source_mul_comm_of_unitary_mul
    {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (f : A →⋆ₐ[ℂ] B) (φ : B →L[ℂ] ℂ)
    (hunit : ∀ (u : unitary A) (a : B), φ (f (u : A) * a) = φ (a * f (u : A)))
    (b : A) (a : B) : φ (f b * a) = φ (a * f b) := by
  obtain ⟨u, c, hb, _⟩ := CStarAlgebra.exists_sum_four_unitary b
  rw [hb]
  simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [hunit]

set_option maxHeartbeats 1000000 in
/-- Every source element, not just source unitaries, lies in the full state's
centralizer. -/
theorem traceExtension_shellFamilySourceHom_mul (family : RepresentativeShellFamily)
    (b : Limit) (a : ShellFamilyTarget family) :
    traceExtension family (shellFamilySourceHom family b * a) =
      traceExtension family (a * shellFamilySourceHom family b) := by
  exact source_mul_comm_of_unitary_mul (shellFamilySourceHom family)
    (traceExtension family) (traceExtension_unitary_mul family) b a

private theorem stronglyConverges_partialSum_representation
    {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : Representation A H) (z : ℕ → A) (T : H →L[ℂ] H)
    (h : ContinuousLinearMap.StronglyConverges
      (ContinuousLinearMap.partialSum (fun n ↦ ρ (z n))) atTop T) :
    ContinuousLinearMap.StronglyConverges
      (fun N ↦ ρ (∑ n ∈ Finset.range N, z n)) atTop T := by
  intro y
  simpa only [ContinuousLinearMap.partialSum, map_sum] using h y

set_option maxHeartbeats 1000000 in
/-- A generator is in the centralizer by the source shell approximants in
this very GNS representation. -/
theorem traceExtension_shellFamilyGenerator_mul (family : RepresentativeShellFamily)
    (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit)
    (a : ShellFamilyTarget family) :
    traceExtension family (shellFamilyGenerator family i * a) =
      traceExtension family (a * shellFamilyGenerator family i) := by
  let x : ℕ → ShellFamilyTarget family := fun N ↦ shellFamilySourceHom family
    (∑ n ∈ Finset.range N, (representativeShellData family i).link n)
  have hx : ContinuousLinearMap.StronglyConverges
      (fun N ↦ tracialRepresentation family (x N)) atTop
      (tracialRepresentation family (shellFamilyGenerator family i)) := by
    exact stronglyConverges_partialSum_representation
      ((tracialRepresentation family).comp (shellFamilySourceHom family))
      (fun n ↦ (representativeShellData family i).link n)
      (tracialRepresentation family (shellFamilyGenerator family i))
      (stronglyConverges_shell_sums_of_trace_of_cyclic family
        (tracialRepresentation family) (tracialVector family)
        (vectorFunctional_tracialRepresentation_source family)
        (denseRange_tracialRepresentation_orbit family) i).1
  have heq (N : ℕ) : Representation.vectorFunctional
      (tracialRepresentation family) (tracialVector family) (x N * a) =
      Representation.vectorFunctional (tracialRepresentation family) (tracialVector family)
        (a * x N) := by
    exact (inner_tracialVector_tracialRepresentation family (x N * a)).trans
      ((traceExtension_shellFamilySourceHom_mul family _ a).trans
        (inner_tracialVector_tracialRepresentation family (a * x N)).symm)
  have h := vectorFunctional_mul_eq_mul_of_stronglyConverges
    (tracialRepresentation family) (tracialVector family) x
    (shellFamilyGenerator family i) a hx heq
  exact (inner_tracialVector_tracialRepresentation family
    (shellFamilyGenerator family i * a)).symm.trans
      (h.trans (inner_tracialVector_tracialRepresentation family
        (a * shellFamilyGenerator family i)))



private theorem trace_mul_comm_of_source_and_generators
    {A H J : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : Representation A H) (U : J → H →L[ℂ] H)
    [order : PartialOrder (AtomicConstruction.concreteTarget π U)]
    [ordered : StarOrderedRing (AtomicConstruction.concreteTarget π U)]
    (φ : AtomicConstruction.concreteTarget π U →L[ℂ] ℂ)
    (hφ : φ ∈ stateSpace (AtomicConstruction.concreteTarget π U))
    (hsource : ∀ c a, φ (AtomicConstruction.sourceHom π U c * a) =
      φ (a * AtomicConstruction.sourceHom π U c))
    (hgenerator : ∀ i a, φ (AtomicConstruction.generator π U i * a) =
      φ (a * AtomicConstruction.generator π U i))
    (a b : AtomicConstruction.concreteTarget π U) : φ (a * b) = φ (b * a) := by
  let C : StarSubalgebra ℂ (AtomicConstruction.concreteTarget π U) := stateCentralizer φ hφ
  have htop : C = ⊤ :=
    AtomicConstruction.eq_top_of_source_mem_of_generator_mem π U C
      (isClosed_stateCentralizer φ hφ)
      (fun c ↦ (mem_stateCentralizer_iff φ hφ _).2 (hsource c))
      (fun i ↦ (mem_stateCentralizer_iff φ hφ _).2 (hgenerator i))
  have ha : a ∈ C := by rw [htop]; trivial
  exact ((mem_stateCentralizer_iff φ hφ a).1 ha) b


set_option maxHeartbeats 2000000 in
/-- The unique state extension of the CAR trace is a trace on the whole
previously constructed target. -/
theorem traceExtension_mul_comm (family : RepresentativeShellFamily)
    (a b : ShellFamilyTarget family) :
    traceExtension family (a * b) = traceExtension family (b * a) := by
  exact trace_mul_comm_of_source_and_generators selectedAtomicRepresentation
    (shellFamilyLinks family)
    (order := shellFamilyTargetPartialOrder family)
    (ordered := shellFamilyTargetStarOrderedRing family)
    (traceExtension family) (traceExtension_mem_stateSpace family)
    (fun c ↦ traceExtension_shellFamilySourceHom_mul family c)
    (fun i ↦ traceExtension_shellFamilyGenerator_mul family i) a b


end MathlibAnnex.CStarAlgebra.CAR
