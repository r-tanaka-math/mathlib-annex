import MathlibAnnex.Analysis.CStarAlgebra.PureStateGNS.IrreduciblePure
import MathlibAnnex.Analysis.CStarAlgebra.AtomicConstruction.AtomicShell

/-!
# The chosen pure-GNS family as atomic-model source data

This file specializes the generic arbitrary-index shell model to the literal
root-preserving representatives already selected in `MathlibAnnex.CStarAlgebra.SourceRepresentatives`.
The remaining flag and shell inputs are representation-local data; no target
capture statement is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Filter Topology
open scoped ComplexOrder ENNReal lp InnerProduct

namespace MathlibAnnex.CStarAlgebra

universe u

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace PureState

/-- The Hilbert fiber of one chosen pure-state GNS representative. -/
abbrev SelectedGNS (root : PureState A) (j : GNSClass A) :=
  (representative root j).positiveFunctional.GNS

/-- The chosen irreducible source representation on one selected fiber. -/
noncomputable def selectedRepresentation (root : PureState A) (j : GNSClass A) :
    MathlibAnnex.Analysis.CStarAlgebra.Representation A (SelectedGNS root j) :=
  (representative root j).positiveFunctional.gnsStarAlgHom

/-- The canonical selected unit vector in one chosen GNS fiber. -/
noncomputable def selectedVector (root : PureState A) (j : GNSClass A) :
    SelectedGNS root j :=
  (representative root j).positiveFunctional.gnsCyclicVector

theorem norm_selectedVector (root : PureState A) (j : GNSClass A) :
    ‖selectedVector root j‖ = 1 :=
  norm_representative_gnsCyclicVector root j

/-- The canonical vector in a selected GNS fiber realizes its selected pure
state exactly. -/
theorem selected_vectorFunctional (root : PureState A) (j : GNSClass A) :
    MathlibAnnex.Analysis.CStarAlgebra.Representation.vectorFunctional
      (selectedRepresentation root j) (selectedVector root j) =
        (representative root j).1 := by
  apply ContinuousLinearMap.ext
  intro a
  exact PositiveLinearMap.inner_gnsCyclicVector_gnsStarAlgHom
    (representative root j).positiveFunctional a

noncomputable instance SelectedGNS.instNontrivial
    (root : PureState A) (j : GNSClass A) : Nontrivial (SelectedGNS root j) := by
  apply nontrivial_of_ne (selectedVector root j) 0
  intro hzero
  have hnorm := congrArg norm hzero
  simpa [norm_selectedVector] using hnorm

/-- Every chosen pure-GNS fiber is irreducible. -/
theorem isIrreducible_selectedRepresentation (root : PureState A) (j : GNSClass A) :
    StarAlgHom.IsIrreducible (selectedRepresentation root j) := by
  apply isIrreducible_starAlgHom_of_isPureState
    (selectedRepresentation root j) (selectedVector root j)
    (norm_selectedVector root j)
    (denseRange_representative_gns_orbit root j)
  rw [selected_vectorFunctional]
  exact (representative root j).2

/-- Distinct chosen classes admit no unitary intertwiner. -/
theorem no_unitaryIntertwiner_selectedRepresentation (root : PureState A)
    {i j : GNSClass A} (hij : i ≠ j) (e : SelectedGNS root i ≃ₗᵢ[ℂ] SelectedGNS root j) :
    ¬ StarAlgHom.Intertwines (selectedRepresentation root i)
      (selectedRepresentation root j)
      (e : SelectedGNS root i →L[ℂ] SelectedGNS root j) := by
  intro he
  apply hij
  apply representative_injective_on_classes root
  refine ⟨e, ?_⟩
  intro a x
  have hx := congrArg
    (fun T : SelectedGNS root i →L[ℂ] SelectedGNS root j ↦ T x) (he a)
  simpa [selectedRepresentation, ContinuousLinearMap.comp_apply] using hx

/-- The arbitrary dependent sum of the literal chosen pure-GNS fibers. -/
abbrev SelectedAtomicHilbert (root : PureState A) :=
  MathlibAnnex.Analysis.InnerProductSpace.HilbertSum (SelectedGNS root)

/-- Coordinate inclusion using a local classical equality decision. -/
noncomputable def selectedEmbedding (root : PureState A) (j : GNSClass A) :
    SelectedGNS root j →L[ℂ] SelectedAtomicHilbert root := by
  classical
  exact MathlibAnnex.Analysis.InnerProductSpace.coordinateEmbedding j

end PureState

namespace AtomicConstruction

open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.Analysis.InnerProductSpace

/-- Natural projection-shell data on the chosen pure-GNS family yields the
actual irreducible atomic model with unitary inter-block generators. -/
theorem exists_irreducible_pureAtomicShellModel
    (root : PureState A)
    (W : PureState.GNSClass A → ℕ →
      PureState.SelectedAtomicHilbert root →L[ℂ]
        PureState.SelectedAtomicHilbert root)
    (U V : PureState.GNSClass A → ℕ →
      Submodule ℂ (PureState.SelectedAtomicHilbert root))
    [∀ i n, (U i n).HasOrthogonalProjection]
    [∀ i n, (V i n).HasOrthogonalProjection]
    [∀ i, (⨅ n, U i n).HasOrthogonalProjection]
    [∀ i, (⨅ n, V i n).HasOrthogonalProjection]
    (hU : ∀ i, Antitone (U i)) (hV : ∀ i, Antitone (V i))
    (hU0 : ∀ i, U i 0 = ⊤) (hV0 : ∀ i, V i 0 = ⊤)
    (hInitial : ∀ i n, ((W i n)†).comp (W i n) =
      Submodule.projectionShell (U i) n)
    (hFinal : ∀ i n, (W i n).comp ((W i n)†) =
      Submodule.projectionShell (V i) n)
    (hUinf : ∀ i, (⨅ n, U i n).starProjection =
      InnerProductSpace.rankOne ℂ
        (PureState.selectedEmbedding root i (PureState.selectedVector root i))
        (PureState.selectedEmbedding root i (PureState.selectedVector root i)))
    (hVinf : ∀ i, (⨅ n, V i n).starProjection =
      InnerProductSpace.rankOne ℂ
        (PureState.selectedEmbedding root root.classOf
          (PureState.selectedVector root root.classOf))
        (PureState.selectedEmbedding root root.classOf
          (PureState.selectedVector root root.classOf))) :
    ∃ L : PureState.GNSClass A →
        PureState.SelectedAtomicHilbert root →L[ℂ]
          PureState.SelectedAtomicHilbert root,
      (∀ i, L i ∈ unitary
        (PureState.SelectedAtomicHilbert root →L[ℂ]
          PureState.SelectedAtomicHilbert root)) ∧
      (∀ i, L i (PureState.selectedEmbedding root i
          (PureState.selectedVector root i)) =
        PureState.selectedEmbedding root root.classOf
          (PureState.selectedVector root root.classOf)) ∧
      (∀ i n, (L i).comp (Submodule.projectionShell (U i) n) = W i n) ∧
      Representation.IsIrreducible
        (ambientInclusion
          (atomicRepresentation (PureState.selectedRepresentation root)) L) := by
  classical
  simpa [PureState.selectedEmbedding] using
    (exists_irreducible_atomicShellModel
    (PureState.selectedRepresentation root)
    (PureState.isIrreducible_selectedRepresentation root)
    (fun {i j} hij e ↦
      PureState.no_unitaryIntertwiner_selectedRepresentation root hij e)
    root.classOf (PureState.selectedVector root)
    (PureState.norm_selectedVector root)
    W U V hU hV hU0 hV0 hInitial hFinal hUinf hVinf)

end AtomicConstruction

end MathlibAnnex.CStarAlgebra
