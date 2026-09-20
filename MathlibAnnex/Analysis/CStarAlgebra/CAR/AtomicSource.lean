import MathlibAnnex.Analysis.CStarAlgebra.CAR.DifferenceShell
import MathlibAnnex.Analysis.CStarAlgebra.AtomicConstruction.PureAtomic
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CommonFixedSubspace

/-!
# Completed CAR data for the atomic shell model

The downstream construction is parameterized by one family of shell data.
The historical KOS-facing constructor remains as a compatibility provider;
the closed CAR homogeneity theorem supplies a second provider in `Main`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Filter Topology
open scoped ENNReal lp InnerProduct

namespace MathlibAnnex.CStarAlgebra.CAR

open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.Analysis.InnerProductSpace

/-- Natural source data for one selected pure-state class.  Its fields are
only the automorphism and exact algebraic shell links obtained from KOS. -/
structure RepresentativeShellData (j : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) where
  alpha : Limit ≃⋆ₐ[ℂ] Limit
  state_eq : ∀ a : Limit,
    (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState j).1 (alpha a) =
      completedRootPureState.1 a
  link : ℕ → Limit
  initial_support : ∀ n,
    star (link n) * link n = alpha (rootShell n)
  final_support : ∀ n,
    link n * star (link n) = rootShell n

/-- A single fixed family of shell data.  The distinguished root component is
definitionally controlled by explicit identity/link equations; no rank-one,
capture, simplicity, or compactness conclusion is stored in this input. -/
structure RepresentativeShellFamily where
  data : ∀ j : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit, RepresentativeShellData j
  root_alpha : (data completedRootPureState.classOf).alpha =
    StarAlgEquiv.refl ℂ Limit
  root_link : ∀ n, (data completedRootPureState.classOf).link n = rootShell n

/-- The component of a fixed representative shell family. -/
noncomputable def representativeShellData (family : RepresentativeShellFamily)
    (j : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) : RepresentativeShellData j :=
  family.data j

/-- Historical KOS provider for one component, retained only to build the
compatibility family below. -/
noncomputable def representativeShellDataOfKishimotoOzawaSakai (hKOS : MathlibAnnex.CStarAlgebra.KishimotoOzawaSakaiProperty.{0})
    (j : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) : RepresentativeShellData j := by
  classical
  by_cases hj : j = completedRootPureState.classOf
  · subst j
    exact
      { alpha := StarAlgEquiv.refl ℂ Limit
        state_eq := rootShell_identity_family.1
        link := rootShell
        initial_support := fun n ↦ (rootShell_identity_family.2 n).1
        final_support := fun n ↦ (rootShell_identity_family.2 n).2 }
  · let hex := exists_representative_rootShell_family_of_kishimotoOzawaSakai hKOS j
    let alpha := Classical.choose hex
    have halpha := Classical.choose_spec hex
    let w := Classical.choose halpha.2
    have hw := Classical.choose_spec halpha.2
    exact
      { alpha := alpha
        state_eq := halpha.1
        link := w
        initial_support := fun n ↦ (hw n).1
        final_support := fun n ↦ (hw n).2 }

/-- Historical all-simple-algebras KOS input produces the same natural family
interface used by the successor construction. -/
noncomputable def representativeShellFamilyOfKishimotoOzawaSakai
    (hKOS : MathlibAnnex.CStarAlgebra.KishimotoOzawaSakaiProperty.{0}) : RepresentativeShellFamily where
  data := representativeShellDataOfKishimotoOzawaSakai hKOS
  root_alpha := by simp [representativeShellDataOfKishimotoOzawaSakai]
  root_link := by
    intro n
    simp [representativeShellDataOfKishimotoOzawaSakai]

@[simp]
theorem representativeShellData_root_alpha (family : RepresentativeShellFamily) :
    (representativeShellData family completedRootPureState.classOf).alpha =
      StarAlgEquiv.refl ℂ Limit :=
  family.root_alpha

@[simp]
theorem representativeShellData_root_link (family : RepresentativeShellFamily)
    (n : ℕ) :
    (representativeShellData family completedRootPureState.classOf).link n =
      rootShell n :=
  family.root_link n

/-- The transported decreasing flag associated with one selected state. -/
noncomputable def transportedFlag (family : RepresentativeShellFamily)
    (j : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (n : ℕ) : Limit :=
  (representativeShellData family j).alpha (rootFlag n)

theorem isStarProjection_transportedFlag (family : RepresentativeShellFamily)
    (j : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (n : ℕ) :
    IsStarProjection (transportedFlag family j n) :=
  (isStarProjection_rootFlag n).map (representativeShellData family j).alpha

@[simp]
theorem transportedFlag_root (family : RepresentativeShellFamily) (n : ℕ) :
    transportedFlag family completedRootPureState.classOf n = rootFlag n := by
  simp [transportedFlag]

@[simp]
theorem transportedFlag_zero (family : RepresentativeShellFamily)
    (j : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) : transportedFlag family j 0 = 1 := by
  simp [transportedFlag]

theorem rootFlag_mul_of_le {m n : ℕ} (hmn : m ≤ n) :
    rootFlag m * rootFlag n = rootFlag n :=
  ((isStarProjection_rootFlag n).le_iff_mul_eq_right
    (isStarProjection_rootFlag m)).1 (antitone_rootFlag hmn)

theorem transportedFlag_mul_of_le (family : RepresentativeShellFamily)
    (j : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) {m n : ℕ} (hmn : m ≤ n) :
    transportedFlag family j m * transportedFlag family j n =
      transportedFlag family j n := by
  change (representativeShellData family j).alpha (rootFlag m) *
      (representativeShellData family j).alpha (rootFlag n) =
        (representativeShellData family j).alpha (rootFlag n)
  rw [← map_mul, rootFlag_mul_of_le hmn]

theorem representativeLink_initial (family : RepresentativeShellFamily)
    (j : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (n : ℕ) :
    star ((representativeShellData family j).link n) *
        (representativeShellData family j).link n =
      transportedFlag family j n - transportedFlag family j (n + 1) := by
  simpa [transportedFlag, rootShell] using
    (representativeShellData family j).initial_support n

theorem representativeLink_final (family : RepresentativeShellFamily)
    (j : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (n : ℕ) :
    (representativeShellData family j).link n *
        star ((representativeShellData family j).link n) =
      rootFlag n - rootFlag (n + 1) := by
  simpa [rootShell] using (representativeShellData family j).final_support n

theorem tendsto_representative_transported_compression
    (family : RepresentativeShellFamily) (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit)
    (b : Limit) :
    Tendsto
      (fun n ↦ transportedFlag family i n * b * transportedFlag family i n -
        (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1 b •
          transportedFlag family i n)
      atTop (nhds 0) := by
  exact tendsto_transported_compressionError
    (representativeShellData family i).alpha
    (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1
    (representativeShellData family i).state_eq b

/-- Every transported flag fixes the canonical vector in its matching selected
GNS fiber. -/
theorem selectedVector_fixed_transportedFlag (family : RepresentativeShellFamily)
    (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (n : ℕ) :
    MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState i
        (transportedFlag family i n)
        (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i) =
      MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i := by
  apply projection_apply_eq_self_of_vectorFunctional_eq_one
    (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState i)
    (transportedFlag family i n) (isStarProjection_transportedFlag family i n)
    (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i)
    (MathlibAnnex.CStarAlgebra.PureState.norm_selectedVector completedRootPureState i)
  calc
    Representation.vectorFunctional
        (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState i)
        (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i)
        (transportedFlag family i n) =
      (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1
        (transportedFlag family i n) :=
          DFunLike.congr_fun (MathlibAnnex.CStarAlgebra.PureState.selected_vectorFunctional
            completedRootPureState i) _
    _ = rootState (rootFlag n) :=
      (representativeShellData family i).state_eq (rootFlag n)
    _ = 1 := rootState_rootFlag n

/-- In the matching selected fiber the common fixed projection is the
rank-one projection onto its canonical GNS vector. -/
theorem selected_commonFixedProjection_eq_rankOne
    (family : RepresentativeShellFamily) (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
    commonFixedProjection (fun n ↦
      MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState i
        (transportedFlag family i n)) =
      InnerProductSpace.rankOne ℂ
        (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i)
        (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i) := by
  apply commonFixedProjection_eq_rankOne_of_dense_orbit
    (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState i)
    (transportedFlag family i)
    (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1
    (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i)
  · intro n
    exact (isStarProjection_transportedFlag family i n).isSelfAdjoint.star_eq
  · exact tendsto_representative_transported_compression family i
  · exact selectedVector_fixed_transportedFlag family i
  · intro b
    exact (DFunLike.congr_fun (MathlibAnnex.CStarAlgebra.PureState.selected_vectorFunctional
      completedRootPureState i) b).symm
  · exact MathlibAnnex.CStarAlgebra.PureState.denseRange_representative_gns_orbit
      completedRootPureState i

/-- In every inequivalent selected fiber the same transported flag has zero
common fixed projection. -/
theorem selected_commonFixedProjection_eq_zero
    (family : RepresentativeShellFamily) {i j : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit}
    (hij : j ≠ i) :
    commonFixedProjection (fun n ↦
      MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState j
        (transportedFlag family i n)) = 0 := by
  apply commonFixedProjection_eq_zero_of_no_unitary
    (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState i)
    (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState j)
    (transportedFlag family i)
    (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1
    (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i)
  · intro n
    exact (isStarProjection_transportedFlag family i n).isSelfAdjoint.star_eq
  · exact tendsto_representative_transported_compression family i
  · intro b
    exact DFunLike.congr_fun (MathlibAnnex.CStarAlgebra.PureState.selected_vectorFunctional
      completedRootPureState i) b
  · exact MathlibAnnex.CStarAlgebra.PureState.denseRange_representative_gns_orbit
      completedRootPureState i
  · exact MathlibAnnex.CStarAlgebra.PureState.isIrreducible_selectedRepresentation
      completedRootPureState j
  · intro U
    exact MathlibAnnex.CStarAlgebra.PureState.no_unitaryIntertwiner_selectedRepresentation
      completedRootPureState hij.symm U

/-- The transported flag has precisely one fixed coordinate in the displayed
arbitrary-index atomic representation. -/
theorem iInf_range_atomic_transportedFlag_eq_span
    (family : RepresentativeShellFamily) (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
    (⨅ n, (atomicRepresentation
      (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState)
      (transportedFlag family i n)).range) =
      ℂ ∙ MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState i
        (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i) := by
  classical
  simpa [MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding] using
    (iInf_range_atomicRepresentation_eq_span
      (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState)
      (transportedFlag family i)
      (isStarProjection_transportedFlag family i) i
      (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i)
      (MathlibAnnex.CStarAlgebra.PureState.norm_selectedVector completedRootPureState i)
      (selected_commonFixedProjection_eq_rankOne family i)
      (fun j hji ↦ selected_commonFixedProjection_eq_zero family hji))

end MathlibAnnex.CStarAlgebra.CAR
