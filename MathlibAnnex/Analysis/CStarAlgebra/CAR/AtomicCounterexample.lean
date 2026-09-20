import MathlibAnnex.Analysis.CStarAlgebra.CAR.GlobalTransport
import MathlibAnnex.Analysis.CStarAlgebra.CAR.AtomicEndpoint

/-!
# Ordinary Naimark endpoint from the proved CAR homogeneity theorem

The shell family and concrete target in this file are chosen once.  The
generic `MathlibAnnex.CStarAlgebra.KishimotoOzawaSakaiProperty` is not changed or assumed: the closed CAR theorem
supplies exactly the representative-to-root automorphisms needed by the
family-parametric atomic construction.
-/

set_option autoImplicit false

noncomputable section

namespace MathlibAnnex.CStarAlgebra.CAR

open MathlibAnnex.Analysis.CStarAlgebra

universe v

/-- Canonical identity shell data at the distinguished root class. -/
private noncomputable def rootRepresentativeShellData :
    RepresentativeShellData completedRootPureState.classOf where
  alpha := StarAlgEquiv.refl ℂ Limit
  state_eq := rootShell_identity_family.1
  link := rootShell
  initial_support := fun n ↦ (rootShell_identity_family.2 n).1
  final_support := fun n ↦ (rootShell_identity_family.2 n).2

/-- For one selected pure-state class, closed CAR homogeneity supplies a
single automorphism.  Generic approximate-inner shell matching then supplies
all exact shell links for that same automorphism.  The root branch is fixed
canonically instead of invoking homogeneity. -/
noncomputable def representativeShellDataOfHomogeneity
    (j : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) : RepresentativeShellData j := by
  classical
  by_cases hj : j = completedRootPureState.classOf
  · subst j
    exact rootRepresentativeShellData
  · let hex := homogeneity
      (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState j).1
      completedRootPureState.1
      (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState j).2
      completedRootPureState.2
    let alpha := Classical.choose hex
    have halpha := Classical.choose_spec hex
    let hwex := MathlibAnnex.CStarAlgebra.exists_shell_family_of_approximately_inner
      Limit alpha halpha.2 rootShell isStarProjection_rootShell
    let w := Classical.choose hwex
    have hw := Classical.choose_spec hwex
    exact
      { alpha := alpha
        state_eq := halpha.1
        link := w
        initial_support := fun n ↦ (hw n).1
        final_support := fun n ↦ (hw n).2 }

@[simp]
theorem representativeShellDataOfHomogeneity_root_alpha :
    (representativeShellDataOfHomogeneity
      completedRootPureState.classOf).alpha = StarAlgEquiv.refl ℂ Limit := by
  simp [representativeShellDataOfHomogeneity, rootRepresentativeShellData]

@[simp]
theorem representativeShellDataOfHomogeneity_root_link (n : ℕ) :
    (representativeShellDataOfHomogeneity
      completedRootPureState.classOf).link n = rootShell n := by
  simp [representativeShellDataOfHomogeneity, rootRepresentativeShellData]

/-- The one representative shell family used by the ordinary CAR endpoint. -/
noncomputable def homogeneityShellFamily : RepresentativeShellFamily where
  data := representativeShellDataOfHomogeneity
  root_alpha := representativeShellDataOfHomogeneity_root_alpha
  root_link := representativeShellDataOfHomogeneity_root_link

/-- The single concrete C-star algebra used by every field of `AtomicCounterexampleEndpoint`. -/
abbrev AtomicCounterexampleAlgebra := ShellFamilyTarget homogeneityShellFamily

/-- The actual completed CAR source map into the fixed main target. -/
noncomputable def atomicCounterexampleSourceHom : Limit →⋆ₐ[ℂ] AtomicCounterexampleAlgebra :=
  shellFamilySourceHom homogeneityShellFamily

/-- The fixed faithful irreducible displayed representation of `AtomicCounterexampleAlgebra`. -/
noncomputable def atomicCounterexampleRepresentation :
    Representation AtomicCounterexampleAlgebra
      (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState) :=
  shellFamilyInclusion homogeneityShellFamily

/-- Fully expanded ordinary endpoint for the single target chosen above. -/
abbrev AtomicCounterexampleEndpoint : Prop :=
  ShellFamilyEndpoint.{v} homogeneityShellFamily

/-- Closed ordinary Naimark main for the actual CAR construction.  It has no
generic KOS, shell-data, rank-one, capture, simplicity, or compactness premise. -/
theorem atomicCounterexampleEndpoint : AtomicCounterexampleEndpoint.{v} :=
  shellFamilyEndpoint homogeneityShellFamily

end MathlibAnnex.CStarAlgebra.CAR
