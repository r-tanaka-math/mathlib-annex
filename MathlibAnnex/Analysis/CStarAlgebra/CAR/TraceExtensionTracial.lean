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

/-- The vector functional of the chosen target-state GNS is its state. -/
theorem vectorFunctional_tracialRepresentation (family : RepresentativeShellFamily) :
    Representation.vectorFunctional (tracialRepresentation family) (tracialVector family) =
      traceExtension family := by
  ext a
  exact inner_tracialVector_tracialRepresentation family a

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
        rw [vectorFunctional_tracialRepresentation]
      _ = trace (star (u : Limit) * b * (u : Limit)) := by
        rw [← map_star, ← map_mul, ← map_mul, traceExtension_shellFamilySourceHom]
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
        rw [vectorFunctional_tracialRepresentation]
    _ = Representation.vectorFunctional (tracialRepresentation family)
        (tracialRepresentation family (shellFamilySourceHom family (u : Limit))
          (tracialVector family)) a :=
      (Representation.vectorFunctional_map_apply (tracialRepresentation family)
        (tracialVector family) (shellFamilySourceHom family (u : Limit)) a).symm
    _ = traceExtension family a := hvalue

set_option maxHeartbeats 1000000 in
private theorem traceExtension_unitary_mul (family : RepresentativeShellFamily)
    (u : unitary Limit) (a : ShellFamilyTarget family) :
    traceExtension family (shellFamilySourceHom family (u : Limit) * a) =
      traceExtension family (a * shellFamilySourceHom family (u : Limit)) := by
  let v := shellFamilySourceHom family (u : Limit)
  have hv : star v * v = 1 := by
    change star (shellFamilySourceHom family (u : Limit)) *
      shellFamilySourceHom family (u : Limit) = 1
    rw [← map_star, ← map_mul, u.property.1, map_one]
  have h := traceExtension_star_unitary_mul_mul family u (v * a)
  change traceExtension family (star v * (v * a) * v) = _ at h
  rw [← mul_assoc (star v) v a, hv, one_mul] at h
  exact h.symm

set_option maxHeartbeats 1000000 in
/-- Every source element, not just source unitaries, lies in the full state's
centralizer. -/
theorem traceExtension_shellFamilySourceHom_mul (family : RepresentativeShellFamily)
    (b : Limit) (a : ShellFamilyTarget family) :
    traceExtension family (shellFamilySourceHom family b * a) =
      traceExtension family (a * shellFamilySourceHom family b) := by
  obtain ⟨u, c, hb, _⟩ := CStarAlgebra.exists_sum_four_unitary b
  rw [hb]
  simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [traceExtension_unitary_mul]

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
    have hfamily : (fun N ↦ tracialRepresentation family (x N)) =
        ContinuousLinearMap.partialSum (fun n ↦
          tracialRepresentation family
            (shellFamilySourceHom family ((representativeShellData family i).link n))) := by
      funext N
      simp only [x, map_sum, ContinuousLinearMap.partialSum]
    rw [hfamily]
    exact (stronglyConverges_shell_sums_of_trace_of_cyclic family
      (tracialRepresentation family) (tracialVector family)
      (vectorFunctional_tracialRepresentation_source family)
      (denseRange_tracialRepresentation_orbit family) i).1
  have heq (N : ℕ) : Representation.vectorFunctional
      (tracialRepresentation family) (tracialVector family) (x N * a) =
      Representation.vectorFunctional (tracialRepresentation family) (tracialVector family)
        (a * x N) := by
    rw [vectorFunctional_tracialRepresentation]
    exact traceExtension_shellFamilySourceHom_mul family _ a
  have h := vectorFunctional_mul_eq_mul_of_stronglyConverges
    (tracialRepresentation family) (tracialVector family) x
    (shellFamilyGenerator family i) a hx heq
  simpa only [vectorFunctional_tracialRepresentation] using h

set_option maxHeartbeats 1000000 in
/-- The unique state extension of the CAR trace is a trace on the whole
previously constructed target. -/
theorem traceExtension_mul_comm (family : RepresentativeShellFamily)
    (a b : ShellFamilyTarget family) :
    traceExtension family (a * b) = traceExtension family (b * a) := by
  let C := stateCentralizer (traceExtension family) (traceExtension_mem_stateSpace family)
  have htop : C = ⊤ :=
    MathlibAnnex.CStarAlgebra.AtomicConstruction.eq_top_of_source_mem_of_generator_mem
      selectedAtomicRepresentation (shellFamilyLinks family) C
      (isClosed_stateCentralizer _ _)
      (fun c ↦ traceExtension_shellFamilySourceHom_mul family c)
      (fun i ↦ traceExtension_shellFamilyGenerator_mul family i)
  have ha : a ∈ C := by rw [htop]; trivial
  exact ha b

end MathlibAnnex.CStarAlgebra.CAR
