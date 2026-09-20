import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn

/-! Compact C¹ test fields. A variable compact carrier packages the existing
`ContDiffMapSupportedIn` provider; no duplicate regularity/support structure.
The parent RET2 source was independently elaborated.  This bounded API-repair
revision is qualified by the exact build evidence accompanying this source. -/

noncomputable section
open Set TopologicalSpace

namespace MathlibAnnex

/-- A C¹ vector field together with one compact set containing its support. -/
abbrev CompactC1VectorField (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  Σ K : Compacts E, ContDiffMapSupportedIn E E 1 K

namespace CompactC1VectorField
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

instance : CoeFun (CompactC1VectorField E) (fun _ => E → E) :=
  ⟨fun W => W.2⟩

/-- The chosen compact carrier; it need not equal topological support. -/
def carrier (W : CompactC1VectorField E) : Set E := W.1

theorem isCompact_carrier (W : CompactC1VectorField E) : IsCompact W.carrier :=
  W.1.isCompact

theorem support_subset (W : CompactC1VectorField E) : Function.support W ⊆ W.carrier :=
  W.2.support_subset

theorem tsupport_subset (W : CompactC1VectorField E) : tsupport W ⊆ W.carrier :=
  W.2.tsupport_subset

theorem contDiff (W : CompactC1VectorField E) : ContDiff ℝ 1 W := W.2.contDiff

theorem continuous (W : CompactC1VectorField E) : Continuous W := W.contDiff.continuous

theorem hasCompactSupport (W : CompactC1VectorField E) : HasCompactSupport W :=
  W.2.hasCompactSupport

/-- Construct a variable-carrier field using the existing fixed-carrier provider. -/
def ofSupport (f : E → E) (K : Set E) (hK : IsCompact K)
    (hs : Function.support f ⊆ K) (hf : ContDiff ℝ 1 f) : CompactC1VectorField E :=
  ⟨⟨K, hK⟩, ContDiffMapSupportedIn.of_support_subset hf hs⟩

@[simp] theorem ofSupport_apply (f : E → E) (K : Set E) (hK : IsCompact K)
    (hs : Function.support f ⊆ K) (hf : ContDiff ℝ 1 f) (x : E) :
    ofSupport f K hK hs hf x = f x := rfl

@[simp] theorem carrier_ofSupport (f : E → E) (K : Set E) (hK : IsCompact K)
    (hs : Function.support f ⊆ K) (hf : ContDiff ℝ 1 f) :
    (ofSupport f K hK hs hf).carrier = K := rfl

/-- A field vanishes, with its derivative, off its closed compact carrier. -/
theorem fderiv_eq_zero_of_not_mem_carrier (W : CompactC1VectorField E)
    {x : E} (hx : x ∉ W.carrier) : fderiv ℝ W x = 0 := by
  exact fderiv_of_notMem_tsupport ℝ (fun h => hx (W.tsupport_subset h))

end CompactC1VectorField
end MathlibAnnex
