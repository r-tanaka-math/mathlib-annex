import MathlibAnnex.Analysis.CStarAlgebra.CAR.AtomicCounterexample
import MathlibAnnex.Analysis.CStarAlgebra.CAR.SeparableIrreducible

/-!
# The fixed atomic C*-algebra and its ordinary representation endpoint

Private integration candidate, not a compiled theorem or an admitted release.
The carrier and choices below are literally the inherited `MathlibAnnex.CStarAlgebra.CAR.AtomicCounterexampleAlgebra`.
There is no new choice of a target for each comparison Hilbert universe.
The stronger, separate request for a separable faithful representation is NOT
part of this file. No theorem asserting that request is introduced here.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace MathlibAnnex.Analysis.CStarAlgebra
universe u v w z

/-- The single inherited CAR atomic target; this is a transparent name, not
another construction or a project-scoped copy of a C*-algebra. -/
abbrev AtomicCounterexampleAlgebra := MathlibAnnex.CStarAlgebra.CAR.AtomicCounterexampleAlgebra

/-- The original, generally nonseparable, ambient atomic Hilbert space. -/
abbrev AtomicCounterexampleHilbertSpace :=
  MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert MathlibAnnex.CStarAlgebra.CAR.completedRootPureState

/-- The literal faithful irreducible inclusion of the fixed target. -/
abbrev atomicCounterexampleRepresentation :
    Representation AtomicCounterexampleAlgebra AtomicCounterexampleHilbertSpace :=
  MathlibAnnex.CStarAlgebra.CAR.atomicCounterexampleRepresentation

/-- The same completed CAR embeds into the same fixed target. -/
abbrev atomicCounterexampleSourceHom :
    MathlibAnnex.CStarAlgebra.CAR.Limit →⋆ₐ[ℂ] AtomicCounterexampleAlgebra := MathlibAnnex.CStarAlgebra.CAR.atomicCounterexampleSourceHom

/-- Definitional target-identity guard used by the integrated consumer. -/
theorem atomicCounterexampleAlgebra_eq_legacy :
    AtomicCounterexampleAlgebra = MathlibAnnex.CStarAlgebra.CAR.AtomicCounterexampleAlgebra := rfl

/-- The expanded inherited ordinary endpoint, without generic KOS, shell,
rank-one, capture, simplicity or compactness hypotheses. -/
theorem atomicCounterexample_endpoint : MathlibAnnex.CStarAlgebra.CAR.AtomicCounterexampleEndpoint.{v} :=
  MathlibAnnex.CStarAlgebra.CAR.atomicCounterexampleEndpoint.{v}

/-- No Hilbert-space separability is assumed or concluded here. -/
theorem atomicCounterexampleRepresentation_injective :
    Function.Injective atomicCounterexampleRepresentation :=
  (MathlibAnnex.CStarAlgebra.CAR.atomicCounterexampleEndpoint.{0}).ambient_injective

theorem isIrreducible_atomicCounterexampleRepresentation :
    Representation.IsIrreducible atomicCounterexampleRepresentation :=
  (MathlibAnnex.CStarAlgebra.CAR.atomicCounterexampleEndpoint.{0}).isIrreducible_ambient

theorem atomicCounterexampleSourceHom_injective :
    Function.Injective atomicCounterexampleSourceHom :=
  (MathlibAnnex.CStarAlgebra.CAR.atomicCounterexampleEndpoint.{0}).source_injective

theorem not_finiteDimensional_atomicCounterexampleAlgebra :
    ¬ FiniteDimensional ℂ AtomicCounterexampleAlgebra :=
  (MathlibAnnex.CStarAlgebra.CAR.atomicCounterexampleEndpoint.{0}).not_finiteDimensional_target

/-- Simplicity uses the already defined project-independent ideal predicate. -/
theorem isSimpleCStarAlgebra_atomicCounterexampleAlgebra :
    IsSimpleCStarAlgebra AtomicCounterexampleAlgebra := by
  exact ⟨(MathlibAnnex.CStarAlgebra.CAR.atomicCounterexampleEndpoint.{0}).nontrivial_target,
    (MathlibAnnex.CStarAlgebra.CAR.atomicCounterexampleEndpoint.{0}).closedIdeal_dichotomy⟩

/-- Capture of arbitrary nonzero irreducible competitors, including maps
not initially bundled as unital. The fixed carrier is independent of `v`. -/
theorem atomicCounterexample_unitaryEquivalent
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (rho : NonUnitalRepresentation (A := AtomicCounterexampleAlgebra) (H := K))
    (hrho : rho.IsIrreducible) :
    ∃ U : AtomicCounterexampleHilbertSpace ≃ₗᵢ[ℂ] K,
      ∀ (a : AtomicCounterexampleAlgebra) (x : AtomicCounterexampleHilbertSpace),
        U (atomicCounterexampleRepresentation a x) = rho a (U x) :=
  (MathlibAnnex.CStarAlgebra.CAR.atomicCounterexampleEndpoint.{v}).captures_nonunital K rho hrho

/-- Compose the same two captures while the common ambient carrier is abstract. -/
private theorem equivalent_of_two_captures
    {A : Type u} [CStarAlgebra A]
    {F : Type z} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (ambient : Representation A F)
    (rho : NonUnitalRepresentation (A := A) (H := H))
    (sigma : NonUnitalRepresentation (A := A) (H := K))
    (hcaptureR : ∃ R : F ≃ₗᵢ[ℂ] H, ∀ (a : A) (x : F),
      R (ambient a x) = rho a (R x))
    (hcaptureS : ∃ S : F ≃ₗᵢ[ℂ] K, ∀ (a : A) (x : F),
      S (ambient a x) = sigma a (S x)) :
    ∃ U : H ≃ₗᵢ[ℂ] K, ∀ (a : A) (x : H), U (rho a x) = sigma a (U x) := by
  obtain ⟨R, hR⟩ := hcaptureR
  obtain ⟨S, hS⟩ := hcaptureS
  refine ⟨R.symm.trans S, ?_⟩
  intro a x
  have hRx : R.symm (rho a x) = ambient a (R.symm x) := by
    apply R.injective
    simpa only [R.apply_symm_apply] using (hR a (R.symm x)).symm
  change S (R.symm (rho a x)) = sigma a (S (R.symm x))
  rw [hRx]
  exact hS a (R.symm x)

/-- Two arbitrary irreducible representations, on independent universes,
are compared through the SAME fixed atomic model. -/
theorem atomicCounterexample_irreducibleModels_equivalent
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (rho : NonUnitalRepresentation (A := AtomicCounterexampleAlgebra) (H := H))
    (sigma : NonUnitalRepresentation (A := AtomicCounterexampleAlgebra) (H := K))
    (hrho : rho.IsIrreducible) (hsigma : sigma.IsIrreducible) :
    ∃ U : H ≃ₗᵢ[ℂ] K, ∀ (a : AtomicCounterexampleAlgebra) (x : H),
      U (rho a x) = sigma a (U x) := by
  exact equivalent_of_two_captures atomicCounterexampleRepresentation rho sigma
    (atomicCounterexample_unitaryEquivalent rho hrho)
    (atomicCounterexample_unitaryEquivalent sigma hsigma)

/-- The same algebra is not a full compact-operator model on any Hilbert
space. The conclusion includes surjectivity onto ALL compact operators. -/
theorem not_isCompactOperatorModel_atomicCounterexample
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : AtomicCounterexampleAlgebra →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    ¬ IsCompactOperatorModel e :=
  (MathlibAnnex.CStarAlgebra.CAR.atomicCounterexampleEndpoint.{v}).not_compactOperatorModel K e

/-- There is no nonzero irreducible representation of the same target on a
separable Hilbert space. This is NOT a statement about faithful reducible
representations. -/
theorem not_isIrreducible_atomicCounterexample_of_separable
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (rho : NonUnitalRepresentation (A := AtomicCounterexampleAlgebra) (H := H)) :
    ¬ rho.IsIrreducible := MathlibAnnex.CStarAlgebra.CAR.not_isIrreducible_of_separable rho

end MathlibAnnex.Analysis.CStarAlgebra
