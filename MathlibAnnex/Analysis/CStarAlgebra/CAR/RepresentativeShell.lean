import Mathlib.RingTheory.SimpleRing.Basic
import MathlibAnnex.Analysis.CStarAlgebra.CAR.PureRoot
import MathlibAnnex.Analysis.CStarAlgebra.CAR.ShellMatching
import MathlibAnnex.Analysis.CStarAlgebra.Representation.PureStateRepresentatives

/-!
# Finite-stage source data

This module assembles every source field which is already available on an
actual binary matrix stage: simplicity/separability, a retained pure root,
set-indexed pure-GNS representatives, normalized cyclic vectors, and exact
conditional shell links.  It does not call these finite stages the CAR
completion and does not claim arbitrary-irrep coverage without the missing
pure/GNS bridge.
-/

set_option autoImplicit false

open scoped ComplexOrder

namespace MathlibAnnex.CStarAlgebra.CAR

/-- The ordinary closed-ideal formulation of simplicity holds at each matrix stage. -/
theorem isSimpleCStarAlgebra_stage (n : ℕ) : MathlibAnnex.CStarAlgebra.IsSimpleCStarAlgebra (Stage n) := by
  constructor
  · infer_instance
  · intro I _
    exact eq_bot_or_eq_top I

/-- The finite-stage root state bundled as a pure state. -/
noncomputable def rootPureState (n : ℕ) : MathlibAnnex.CStarAlgebra.PureState (Stage n) :=
  ⟨rootFunctional n, isPureState_rootFunctional n⟩

/-- The chosen pure-GNS representative family retains the root state literally. -/
@[simp]
theorem representative_rootPureState (n : ℕ) :
    MathlibAnnex.CStarAlgebra.PureState.representative (rootPureState n) (rootPureState n).classOf =
      rootPureState n :=
  MathlibAnnex.CStarAlgebra.PureState.representative_root _

/-- KOS, supplied only as an explicit theorem argument, provides an exact shell
link from every selected finite-stage pure-GNS class to the root class. -/
theorem exists_representative_shell_link_of_kishimotoOzawaSakai (hKOS : MathlibAnnex.CStarAlgebra.KishimotoOzawaSakaiProperty.{0})
    (n : ℕ) (j : MathlibAnnex.CStarAlgebra.PureState.GNSClass (Stage n))
    (f : Stage n) (hf : IsStarProjection f) :
    ∃ alpha : Stage n ≃⋆ₐ[ℂ] Stage n,
      (∀ a : Stage n,
        (MathlibAnnex.CStarAlgebra.PureState.representative (rootPureState n) j).1 (alpha a) =
          (rootPureState n).1 a) ∧
      ∃ w : Stage n, star w * w = alpha f ∧ w * star w = f := by
  exact MathlibAnnex.CStarAlgebra.exists_shell_link_of_kishimotoOzawaSakai hKOS (Stage n)
    (isSimpleCStarAlgebra_stage n)
    (MathlibAnnex.CStarAlgebra.PureState.representative (rootPureState n) j).1
    (rootPureState n).1
    (MathlibAnnex.CStarAlgebra.PureState.representative (rootPureState n) j).2
    (rootPureState n).2 f hf

end MathlibAnnex.CStarAlgebra.CAR
