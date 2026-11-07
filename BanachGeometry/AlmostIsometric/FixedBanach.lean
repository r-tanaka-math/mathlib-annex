import BanachGeometry.AlmostIsometric.Insertion
import BanachGeometry.SequenceSpaces.C0Banach
import BanachGeometry.SequenceSpaces.L1Separable

/-!
# Connection of the fixed metric spaces to the Banach bundles

The carriers and inherited norms are those of AlmostIsometricFamily.FixedX
and FixedY. The bundles use the completeness, separability and nontriviality
instances proved in the sequence-space modules. The metric conclusion uses
the explicit H1 data. HeadSplitting and NoC0Closure supply the additional
linear obstruction used for nonisomorphism in Existence.
-/

noncomputable section
namespace BanachGeometry
namespace AlmostIsometricFamily
variable (d : AlmostIsometricFamily)

def fixedXBanach : SeparableRealBanach where
  Carrier := d.FixedX
  normedAddCommGroup := inferInstance
  normedSpace := inferInstance
  completeSpace := inferInstance
  separableSpace := inferInstance
  nontrivial := inferInstance

def fixedYBanach : SeparableRealBanach where
  Carrier := d.FixedY
  normedAddCommGroup := inferInstance
  normedSpace := inferInstance
  completeSpace := inferInstance
  separableSpace := inferInstance
  nontrivial := inferInstance

@[simp] theorem fixedXBanach_norm (x : d.FixedX) :
    @norm d.fixedXBanach.Carrier _ x = ‖x‖ := rfl

@[simp] theorem fixedYBanach_norm (x : d.FixedY) :
    @norm d.fixedYBanach.Carrier _ x = ‖x‖ := rfl

/-- The H1 metric conclusion for exactly the fixed Banach bundles and
their inherited norms, with the same spaces chosen before every tolerance. -/
theorem almostIsometricAtEveryTolerance_fixedXBanach_fixedYBanach :
    AlmostIsometricAtEveryTolerance d.fixedXBanach d.fixedYBanach := by
  intro ε hε
  exact d.fixed_spaces_almost_isometric ε hε

end AlmostIsometricFamily
end BanachGeometry
