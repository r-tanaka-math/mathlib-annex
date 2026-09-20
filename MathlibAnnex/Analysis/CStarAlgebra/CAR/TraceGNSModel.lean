import MathlibAnnex.Analysis.CStarAlgebra.CAR.TracialRepresentation
import MathlibAnnex.Analysis.CStarAlgebra.CAR.TracialTransport

/-!
# The target on the ordinary CAR trace GNS space

The Hilbert space here is constructed from CAR alone and is independent of
the shell-family parameter. The target is unchanged. Its representation is
transported along a proved pointed source-cyclic unitary equivalence.
-/

set_option autoImplicit false

open Filter Topology
open scoped InnerProduct

namespace MathlibAnnex.CStarAlgebra.CAR

open MathlibAnnex.Analysis.CStarAlgebra

/-- The ordinary Hilbert space `L²(CAR, trace)`. -/
abbrev TraceHilbertSpace := tracePositive.GNS

/-- The canonical vector in the CAR trace GNS space. -/
noncomputable def traceVector : TraceHilbertSpace := tracePositive.gnsCyclicVector

/-- The ordinary CAR trace representation. -/
noncomputable def traceRepresentation : Representation Limit TraceHilbertSpace :=
  tracePositive.gnsStarAlgHom

@[simp]
theorem norm_traceVector : ‖traceVector‖ = 1 :=
  tracePositive.norm_gnsCyclicVector tracePositive_one

theorem traceVector_ne_zero : traceVector ≠ 0 := by
  intro hzero
  have h := norm_traceVector
  rw [hzero, norm_zero] at h
  exact zero_ne_one h

/-- Nontriviality is witnessed by the normalized CAR trace vector. -/
theorem nontrivial_traceHilbertSpace : Nontrivial TraceHilbertSpace :=
  nontrivial_of_ne traceVector 0 traceVector_ne_zero

@[simp]
theorem inner_traceVector_traceRepresentation (b : Limit) :
    inner ℂ traceVector (traceRepresentation b traceVector) = trace b :=
  tracePositive.inner_gnsCyclicVector_gnsStarAlgHom b

theorem denseRange_traceRepresentation_orbit :
    DenseRange (fun b ↦ traceRepresentation b traceVector) :=
  tracePositive.denseRange_gnsStarAlgHom_apply_gnsCyclicVector

theorem separableSpace_traceHilbertSpace : TopologicalSpace.SeparableSpace TraceHilbertSpace :=
  denseRange_traceRepresentation_orbit.separableSpace
    (((ContinuousLinearMap.apply ℂ TraceHilbertSpace traceVector).comp
      (Representation.continuousLinearMap traceRepresentation)).continuous)

set_option maxHeartbeats 5000000 in
/-- The target-state GNS and CAR-trace GNS have the same dense pointed source
orbit, so a unitary between them exists without any dimension assumption. -/
theorem exists_linearIsometryEquiv_traceHilbertSpace (family : RepresentativeShellFamily) :
    ∃ e : TraceHilbertSpace ≃ₗᵢ[ℂ] TracialHilbertSpace family,
      e traceVector = tracialVector family ∧
      ∀ b, (e : TraceHilbertSpace →L[ℂ] TracialHilbertSpace family).comp
        (traceRepresentation b) =
        (tracialRepresentation family (shellFamilySourceHom family b)).comp
          (e : TraceHilbertSpace →L[ℂ] TracialHilbertSpace family) := by
  let σ : Representation Limit (TracialHilbertSpace family) :=
    (tracialRepresentation family).comp (shellFamilySourceHom family)
  have hσ : DenseRange (StarAlgHom.orbitMap σ (tracialVector family)) := by
    exact denseRange_tracialRepresentation_source_orbit family
  have hstate (b : Limit) :
      inner ℂ traceVector (traceRepresentation b traceVector) =
        inner ℂ (tracialVector family) (σ b (tracialVector family)) := by
    change inner ℂ traceVector (traceRepresentation b traceVector) =
      inner ℂ (tracialVector family)
        (tracialRepresentation family (shellFamilySourceHom family b) (tracialVector family))
    rw [inner_traceVector_traceRepresentation, inner_tracialVector_tracialRepresentation,
      traceExtension_shellFamilySourceHom]
  obtain ⟨e, he, _⟩ := StarAlgHom.existsUnique_pointedCyclicTransport
    traceRepresentation σ
    traceVector (tracialVector family) denseRange_traceRepresentation_orbit
    hσ hstate
  exact ⟨e, he.2.1, he.2.2⟩

/-- The pointed unitary is fixed once for each already fixed shell family. -/
noncomputable def traceGNSUnitary (family : RepresentativeShellFamily) :
    TraceHilbertSpace ≃ₗᵢ[ℂ] TracialHilbertSpace family :=
  Classical.choose (exists_linearIsometryEquiv_traceHilbertSpace family)

@[simp]
theorem traceGNSUnitary_traceVector (family : RepresentativeShellFamily) :
    traceGNSUnitary family traceVector = tracialVector family :=
  (Classical.choose_spec (exists_linearIsometryEquiv_traceHilbertSpace family)).1

theorem traceGNSUnitary_comp_traceRepresentation (family : RepresentativeShellFamily) (b : Limit) :
    (traceGNSUnitary family : TraceHilbertSpace →L[ℂ] TracialHilbertSpace family).comp
      (traceRepresentation b) =
      (tracialRepresentation family (shellFamilySourceHom family b)).comp
        (traceGNSUnitary family : TraceHilbertSpace →L[ℂ] TracialHilbertSpace family) :=
  (Classical.choose_spec (exists_linearIsometryEquiv_traceHilbertSpace family)).2 b

/-- The same target now acts on the original CAR trace GNS space. -/
noncomputable def traceModelRepresentation (family : RepresentativeShellFamily) :
    Representation (ShellFamilyTarget family) TraceHilbertSpace :=
  (traceGNSUnitary family).symm.conjStarAlgEquiv.toStarAlgHom.comp
    (tracialRepresentation family)

@[simp]
theorem traceModelRepresentation_apply (family : RepresentativeShellFamily)
    (a : ShellFamilyTarget family) (x : TraceHilbertSpace) :
    traceModelRepresentation family a x = (traceGNSUnitary family).symm
      (tracialRepresentation family a (traceGNSUnitary family x)) := rfl

set_option maxHeartbeats 1000000 in
@[simp]
theorem traceModelRepresentation_shellFamilySourceHom (family : RepresentativeShellFamily) (b : Limit) :
    traceModelRepresentation family (shellFamilySourceHom family b) = traceRepresentation b := by
  ext x
  apply (traceGNSUnitary family).injective
  rw [traceModelRepresentation_apply, LinearIsometryEquiv.apply_symm_apply]
  have hcoe (y : TraceHilbertSpace) :
      (traceGNSUnitary family : TraceHilbertSpace →L[ℂ] TracialHilbertSpace family) y =
        traceGNSUnitary family y := rfl
  have h := congrArg (fun T : TraceHilbertSpace →L[ℂ] TracialHilbertSpace family ↦ T x)
    (traceGNSUnitary_comp_traceRepresentation family b)
  simpa only [ContinuousLinearMap.comp_apply, hcoe] using h.symm

theorem traceModelRepresentation_injective (family : RepresentativeShellFamily) :
    Function.Injective (traceModelRepresentation family) :=
  (traceGNSUnitary family).symm.conjStarAlgEquiv.injective.comp
    (tracialRepresentation_injective family)

theorem isometry_traceModelRepresentation (family : RepresentativeShellFamily) :
    Isometry (traceModelRepresentation family) :=
  AddMonoidHomClass.isometry_of_norm (traceModelRepresentation family)
    (NonUnitalStarAlgHom.norm_map (traceModelRepresentation family)
      (traceModelRepresentation_injective family))

@[simp]
theorem inner_traceVector_traceModelRepresentation (family : RepresentativeShellFamily)
    (a : ShellFamilyTarget family) :
    inner ℂ traceVector (traceModelRepresentation family a traceVector) =
      traceExtension family a := by
  rw [← (traceGNSUnitary family).inner_map_map traceVector
    (traceModelRepresentation family a traceVector)]
  simp only [traceModelRepresentation_apply, LinearIsometryEquiv.apply_symm_apply,
    traceGNSUnitary_traceVector, inner_tracialVector_tracialRepresentation]

theorem denseRange_traceModelRepresentation_orbit (family : RepresentativeShellFamily) :
    DenseRange (fun a ↦ traceModelRepresentation family a traceVector) := by
  have hsource : DenseRange (fun b ↦ traceModelRepresentation family
      (shellFamilySourceHom family b) traceVector) := by
    simpa only [traceModelRepresentation_shellFamilySourceHom] using denseRange_traceRepresentation_orbit
  exact hsource.mono (by
    rintro _ ⟨b, rfl⟩
    exact ⟨shellFamilySourceHom family b, rfl⟩)

/-- The strong-sum limit is an actual unitary on the CAR trace Hilbert
space, with both unitary identities inherited through the representation. -/
theorem traceModelRepresentation_shellFamilyGenerator_mem_unitary
    (family : RepresentativeShellFamily)
    (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
    traceModelRepresentation family (shellFamilyGenerator family i) ∈
      unitary (TraceHilbertSpace →L[ℂ] TraceHilbertSpace) :=
  Unitary.map_mem (traceModelRepresentation family) (shellFamilyGenerator_mem_unitary family i)

@[simp]
theorem traceModelRepresentation_shellFamilyGenerator_root
    (family : RepresentativeShellFamily) :
    traceModelRepresentation family
      (shellFamilyGenerator family completedRootPureState.classOf) = 1 := by
  rw [shellFamilyGenerator_root, map_one]

/-- The R51 shell-sum formula holds in the literal CAR trace GNS model, for
the same links that define the already existing atomic target. -/
theorem stronglyConverges_traceRepresentation_shell_sums
    (family : RepresentativeShellFamily)
    (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
    ContinuousLinearMap.StronglyConverges
      (ContinuousLinearMap.partialSum
        (fun n ↦ traceRepresentation ((representativeShellData family i).link n)))
      atTop (traceModelRepresentation family (shellFamilyGenerator family i)) ∧
    ContinuousLinearMap.StronglyConverges
      (ContinuousLinearMap.partialSum
        (fun n ↦ (traceRepresentation ((representativeShellData family i).link n))†))
      atTop ((traceModelRepresentation family (shellFamilyGenerator family i))†) := by
  have htrace (b : Limit) : Representation.vectorFunctional
      ((traceModelRepresentation family).comp (shellFamilySourceHom family)) traceVector b =
        trace b := by
    change inner ℂ traceVector
      (traceModelRepresentation family (shellFamilySourceHom family b) traceVector) = trace b
    rw [traceModelRepresentation_shellFamilySourceHom, inner_traceVector_traceRepresentation]
  simpa only [traceModelRepresentation_shellFamilySourceHom] using
    stronglyConverges_shell_sums_of_trace_of_cyclic family (traceModelRepresentation family)
      traceVector htrace (denseRange_traceModelRepresentation_orbit family) i

end MathlibAnnex.CStarAlgebra.CAR
