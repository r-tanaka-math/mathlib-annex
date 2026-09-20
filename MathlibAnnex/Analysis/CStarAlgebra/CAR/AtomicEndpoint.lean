import MathlibAnnex.Analysis.CStarAlgebra.CAR.Capture
import MathlibAnnex.Analysis.CStarAlgebra.Representation.UniqueModelConsequences
import MathlibAnnex.Analysis.CStarAlgebra.Representation.NonUnital

/-!
# Shell-family atomic endpoint

The completed-CAR shell family is chosen once, independently of every later
target Hilbert-space universe.  All ordinary consequences below refer to
that same concrete generated C-star algebra.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ComplexOrder InnerProduct

namespace MathlibAnnex.CStarAlgebra.CAR

open MathlibAnnex.Analysis.CStarAlgebra

universe v

/-- The one completed-CAR link family selected from the actual shell-model
construction.  Its definition has no target Hilbert-space universe
parameter. -/
noncomputable def shellFamilyLinks (family : RepresentativeShellFamily) :
    MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit →
      MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState :=
  Classical.choose (exists_completedAtomicShellModel family)

theorem shellFamilyLinks_unitary (family : RepresentativeShellFamily) :
    ∀ i, shellFamilyLinks family i ∈ unitary
      (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState) :=
  (Classical.choose_spec (exists_completedAtomicShellModel family)).1

theorem shellFamilyLinks_map_selectedVector (family : RepresentativeShellFamily) :
    ∀ i, shellFamilyLinks family i
        (MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState i
          (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i)) =
      MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState
        completedRootPureState.classOf
        (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState
          completedRootPureState.classOf) :=
  (Classical.choose_spec (exists_completedAtomicShellModel family)).2.1

theorem shellFamilyLinks_sourceShell (family : RepresentativeShellFamily) :
    ∀ i n, (shellFamilyLinks family i).comp
        (selectedAtomicRepresentation
          (transportedFlag family i n - transportedFlag family i (n + 1))) =
      representedShellLink family i n :=
  (Classical.choose_spec (exists_completedAtomicShellModel family)).2.2.1

theorem shellFamilyLinks_root (family : RepresentativeShellFamily) :
    shellFamilyLinks family completedRootPureState.classOf = 1 :=
  (Classical.choose_spec (exists_completedAtomicShellModel family)).2.2.2.1

/-- The single actual target used by every endpoint property. -/
abbrev ShellFamilyTarget (family : RepresentativeShellFamily) :=
  AtomicTarget (shellFamilyLinks family)

/-- The actual completed CAR embeds unitally into the fixed target. -/
noncomputable def shellFamilySourceHom (family : RepresentativeShellFamily) :
    Limit →⋆ₐ[ℂ] ShellFamilyTarget family :=
  MathlibAnnex.CStarAlgebra.AtomicConstruction.sourceHom selectedAtomicRepresentation (shellFamilyLinks family)

/-- The fixed target's literal inclusion into its ambient operator algebra. -/
noncomputable def shellFamilyInclusion (family : RepresentativeShellFamily) :
    Representation (ShellFamilyTarget family)
      (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState) :=
  MathlibAnnex.CStarAlgebra.AtomicConstruction.ambientInclusion selectedAtomicRepresentation
    (shellFamilyLinks family)

theorem shellFamilySourceHom_injective (family : RepresentativeShellFamily) :
    Function.Injective (shellFamilySourceHom family) := by
  exact
    (Classical.choose_spec
      (exists_completedAtomicShellModel family)).2.2.2.2.1

noncomputable instance shellFamilyTargetNontrivial
    (family : RepresentativeShellFamily) : Nontrivial (ShellFamilyTarget family) :=
  (shellFamilySourceHom_injective family).nontrivial

noncomputable instance shellFamilyTargetPartialOrder
    (family : RepresentativeShellFamily) : PartialOrder (ShellFamilyTarget family) :=
  CStarAlgebra.spectralOrder (ShellFamilyTarget family)

noncomputable instance shellFamilyTargetStarOrderedRing
    (family : RepresentativeShellFamily) : StarOrderedRing (ShellFamilyTarget family) :=
  CStarAlgebra.spectralOrderedRing (ShellFamilyTarget family)

theorem isClosed_shellFamilyTarget (family : RepresentativeShellFamily) :
    IsClosed
      (ShellFamilyTarget family : Set
        (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
          MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState)) := by
  infer_instance

theorem shellFamilySourceHom_map_one (family : RepresentativeShellFamily) :
    shellFamilySourceHom family 1 = 1 :=
  map_one (shellFamilySourceHom family)

theorem shellFamilyInclusion_injective (family : RepresentativeShellFamily) :
    Function.Injective (shellFamilyInclusion family) := by
  exact MathlibAnnex.CStarAlgebra.AtomicConstruction.ambientInclusion_injective selectedAtomicRepresentation
    (shellFamilyLinks family)

theorem isIrreducible_shellFamilyInclusion (family : RepresentativeShellFamily) :
    Representation.IsIrreducible (shellFamilyInclusion family) := by
  exact
    (Classical.choose_spec
      (exists_completedAtomicShellModel family)).2.2.2.2.2

/-- The fixed target is infinite-dimensional because it contains an
injective unital copy of the infinite-dimensional completed CAR algebra. -/
theorem not_finiteDimensional_shellFamilyTarget
    (family : RepresentativeShellFamily) :
    ¬ FiniteDimensional ℂ (ShellFamilyTarget family) := by
  intro hfinite
  letI : FiniteDimensional ℂ (ShellFamilyTarget family) := hfinite
  exact not_finiteDimensional
    (FiniteDimensional.of_injective
      (LinearMapClass.linearMap (shellFamilySourceHom family))
      (shellFamilySourceHom_injective family))

/-- Every unital irreducible representation on an arbitrary independent
Hilbert universe is equivalent to the fixed ambient inclusion. -/
theorem isUniqueIrreducibleModel_shellFamilyInclusion
    (family : RepresentativeShellFamily) :
    Representation.IsUniqueIrreducibleModel.{0, 0, v}
      (shellFamilyInclusion family) := by
  refine ⟨shellFamilyInclusion_injective family,
    isIrreducible_shellFamilyInclusion family, ?_⟩
  intro K _ _ _ rho hrho
  exact ambientInclusion_unitaryEquivalent family
    (shellFamilyLinks family)
    (shellFamilyLinks_unitary family)
    (shellFamilyLinks_map_selectedVector family)
    (shellFamilyLinks_sourceShell family)
    (shellFamilyLinks_root family) rho hrho

/-- The same fixed model captures ordinary nonzero irreducible
representations even when their input bundle does not assume preservation of
the unit. -/
theorem isUniqueIrreducibleModelAmongNonUnital_shellFamilyInclusion
    (family : RepresentativeShellFamily) :
    Representation.IsUniqueIrreducibleModelAmongNonUnital.{0, 0, v}
      (shellFamilyInclusion family) :=
  (isUniqueIrreducibleModel_shellFamilyInclusion.{v} family).isUniqueIrreducibleModelAmongNonUnital

/-- Expanded ordinary capture statement.  The intertwining equation uses the
original possibly nonunital representation, not merely its bundled
`toUnital` view. -/
theorem shellFamilyInclusion_unitaryEquivalent_nonUnital
    (family : RepresentativeShellFamily)
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K]
    (rho : NonUnitalRepresentation
      (A := ShellFamilyTarget family) (H := K))
    (hrho : rho.IsIrreducible) :
    ∃ U :
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState ≃ₗᵢ[ℂ] K,
      ∀ (a : ShellFamilyTarget family)
        (x : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState),
        U (shellFamilyInclusion family a x) = rho a (U x) := by
  obtain ⟨U, hU⟩ :=
    (isUniqueIrreducibleModelAmongNonUnital_shellFamilyInclusion.{v} family).2.2
      K rho hrho
  exact ⟨U, fun a x ↦ by simpa using hU a x⟩

/-- Closed two-sided ideals of the same fixed target are trivial. -/
theorem isSimpleCStarAlgebra_shellFamilyTarget (family : RepresentativeShellFamily) :
    MathlibAnnex.CStarAlgebra.IsSimpleCStarAlgebra (ShellFamilyTarget family) := by
  exact MathlibAnnex.CStarAlgebra.isSimpleCStarAlgebra_of_uniqueIrreducibleModel
    (shellFamilyInclusion family)
    (isUniqueIrreducibleModel_shellFamilyInclusion.{0} family)

/-- The same target is not an exact algebraic model of all compact operators
on any Hilbert space. -/
theorem not_isCompactOperatorModel_shellFamilyTarget
    (family : RepresentativeShellFamily)
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K]
    (e : ShellFamilyTarget family →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    ¬ IsCompactOperatorModel e :=
  not_isCompactOperatorModel_of_infiniteDimensional
    (not_finiteDimensional_shellFamilyTarget family) e

/-- Fully expanded ordinary endpoint for the one fixed actual target. -/
structure ShellFamilyEndpoint (family : RepresentativeShellFamily) : Prop where
  nontrivial_target : Nontrivial (ShellFamilyTarget family)
  isClosed_target :
    IsClosed
      (ShellFamilyTarget family : Set
        (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
          MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState))
  source_injective : Function.Injective (shellFamilySourceHom family)
  source_unital : shellFamilySourceHom family 1 = 1
  not_finiteDimensional_target :
    ¬ FiniteDimensional ℂ (ShellFamilyTarget family)
  ambient_injective : Function.Injective (shellFamilyInclusion family)
  isIrreducible_ambient :
    Representation.IsIrreducible (shellFamilyInclusion family)
  captures_nonunital :
    ∀ (K : Type v) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K]
      (rho : NonUnitalRepresentation
        (A := ShellFamilyTarget family) (H := K)),
      rho.IsIrreducible →
        ∃ U :
            MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState ≃ₗᵢ[ℂ] K,
          ∀ (a : ShellFamilyTarget family)
            (x : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState),
            U (shellFamilyInclusion family a x) = rho a (U x)
  closedIdeal_dichotomy :
    ∀ I : TwoSidedIdeal (ShellFamilyTarget family),
      IsClosed (I : Set (ShellFamilyTarget family)) → I = ⊥ ∨ I = ⊤
  not_compactOperatorModel :
    ∀ (K : Type v) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K]
      (e : ShellFamilyTarget family →⋆ₙₐ[ℂ] (K →L[ℂ] K)),
      ¬ (Function.Injective e ∧
        (∀ a : ShellFamilyTarget family, IsCompactOperator (e a)) ∧
        ∀ T : K →L[ℂ] K, IsCompactOperator T →
          ∃ a : ShellFamilyTarget family, e a = T)

/-- The fixed target is nontrivial, in exactly the form used by the endpoint
record. -/
theorem nontrivial_shellFamilyTarget (family : RepresentativeShellFamily) :
    Nontrivial (ShellFamilyTarget family) := by
  infer_instance

/-- The ordinary nonunital capture theorem with the endpoint's explicit
Hilbert-space binder. -/
theorem shellFamily_captures_nonunital (family : RepresentativeShellFamily) :
    ∀ (K : Type v) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K]
      (rho : NonUnitalRepresentation
        (A := ShellFamilyTarget family) (H := K)),
      rho.IsIrreducible →
        ∃ U :
            MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState ≃ₗᵢ[ℂ] K,
          ∀ (a : ShellFamilyTarget family)
            (x : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState),
            U (shellFamilyInclusion family a x) = rho a (U x) := by
  intro K _ _ _ rho hrho
  exact shellFamilyInclusion_unitaryEquivalent_nonUnital family rho hrho

/-- The simplicity consequence in exactly the form stored by the endpoint. -/
theorem shellFamilyTarget_closedIdeal_dichotomy
    (family : RepresentativeShellFamily) :
    ∀ I : TwoSidedIdeal (ShellFamilyTarget family),
      IsClosed (I : Set (ShellFamilyTarget family)) → I = ⊥ ∨ I = ⊤ :=
  (isSimpleCStarAlgebra_shellFamilyTarget family).2

/-- The non-compact-model result in the endpoint's expanded surface form.
The source theorem has this type definitionally, so no propositional transport
is needed. -/
theorem shellFamilyTarget_not_compactOperatorModel
    (family : RepresentativeShellFamily) :
    ∀ (K : Type v) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K]
      (e : ShellFamilyTarget family →⋆ₙₐ[ℂ] (K →L[ℂ] K)),
      ¬ (Function.Injective e ∧
        (∀ a : ShellFamilyTarget family, IsCompactOperator (e a)) ∧
        ∀ T : K →L[ℂ] K, IsCompactOperator T →
          ∃ a : ShellFamilyTarget family, e a = T) := by
  intro K _ _ _ e
  exact not_isCompactOperatorModel_shellFamilyTarget family e

/-- Ordinary family-parametric main.  Shell matching is the only input;
source faithfulness, capture, ideal simplicity, and noncompactness are proved
in the core tree rather than stored in the family. -/
theorem shellFamilyEndpoint (family : RepresentativeShellFamily) :
    ShellFamilyEndpoint.{v} family := by
  refine
    { nontrivial_target := nontrivial_shellFamilyTarget family
      isClosed_target := isClosed_shellFamilyTarget family
      source_injective := shellFamilySourceHom_injective family
      source_unital := shellFamilySourceHom_map_one family
      not_finiteDimensional_target :=
        not_finiteDimensional_shellFamilyTarget family
      ambient_injective := shellFamilyInclusion_injective family
      isIrreducible_ambient := isIrreducible_shellFamilyInclusion family
      captures_nonunital := shellFamily_captures_nonunital family
      closedIdeal_dichotomy := shellFamilyTarget_closedIdeal_dichotomy family
      not_compactOperatorModel :=
        shellFamilyTarget_not_compactOperatorModel family }

/-! ## Historical KOS-facing compatibility endpoint -/

/-- The original conditional target, now a transparent specialization of the
family-parametric successor. -/
abbrev CompletedAtomicTarget (hKOS : MathlibAnnex.CStarAlgebra.KishimotoOzawaSakaiProperty.{0}) :=
  ShellFamilyTarget (representativeShellFamilyOfKishimotoOzawaSakai hKOS)

/-- Historical source hom, retained as a transparent compatibility wrapper. -/
noncomputable def completedAtomicSourceHom (hKOS : MathlibAnnex.CStarAlgebra.KishimotoOzawaSakaiProperty.{0}) :
    Limit →⋆ₐ[ℂ] CompletedAtomicTarget hKOS :=
  shellFamilySourceHom (representativeShellFamilyOfKishimotoOzawaSakai hKOS)

/-- Historical ambient inclusion, retained as a transparent compatibility
wrapper. -/
noncomputable def completedAtomicInclusion (hKOS : MathlibAnnex.CStarAlgebra.KishimotoOzawaSakaiProperty.{0}) :
    Representation (CompletedAtomicTarget hKOS)
      (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState) :=
  shellFamilyInclusion (representativeShellFamilyOfKishimotoOzawaSakai hKOS)

/-- The original endpoint proposition is the family successor specialized to
the family supplied by the original generic KOS premise. -/
abbrev CompletedAtomicEndpoint (hKOS : MathlibAnnex.CStarAlgebra.KishimotoOzawaSakaiProperty.{0}) : Prop :=
  ShellFamilyEndpoint.{v} (representativeShellFamilyOfKishimotoOzawaSakai hKOS)

/-- Historical conditional main, proved through the family-parametric tree. -/
theorem completedAtomicEndpoint (hKOS : MathlibAnnex.CStarAlgebra.KishimotoOzawaSakaiProperty.{0}) :
    CompletedAtomicEndpoint.{v} hKOS :=
  shellFamilyEndpoint (representativeShellFamilyOfKishimotoOzawaSakai hKOS)

end MathlibAnnex.CStarAlgebra.CAR
