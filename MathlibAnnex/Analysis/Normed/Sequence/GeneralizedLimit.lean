import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A norm-one generalized limit on bounded complex sequences

Hahn--Banach extends the ordinary limit on the subspace of convergent
sequences.  No shift-invariance, multiplicativity, or ultrafilter is claimed.
This is sufficient to turn a norm-approximating sequence of pairs for a
bilinear form into an actual norm-attaining pair on bounded-sequence spaces.

This construction is distinct from the invariant isometry mean required by
KOS.  It cannot be substituted for that mean: its domain and invariance
properties are different.

Controller source C01; compilation pending.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open BoundedContinuousFunction

namespace MathlibAnnex.SequenceLimit

abbrev ScalarSequence := ℕ →ᵇ ℂ

/-- The linear subspace on which the usual scalar limit exists. -/
def convergent : Submodule ℂ ScalarSequence where
  carrier := {x | ∃ z : ℂ, Tendsto (fun n : ℕ => x n) atTop (𝓝 z)}
  zero_mem' := ⟨0, by simpa using (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, ha.add hb⟩
  smul_mem' := by
    rintro c x ⟨a, ha⟩
    exact ⟨c • a, ha.const_smul c⟩

/-- The limit of a convergent bounded sequence; uniqueness below controls
all algebraic laws of this choice. -/
def value (x : convergent) : ℂ := Classical.choose x.property

theorem value_spec (x : convergent) :
    Tendsto (fun n : ℕ => (x : ScalarSequence) n) atTop (𝓝 (value x)) :=
  Classical.choose_spec x.property

theorem value_eq_of_tendsto (x : convergent) {z : ℂ}
    (hz : Tendsto (fun n : ℕ => (x : ScalarSequence) n) atTop (𝓝 z)) :
    value x = z := tendsto_nhds_unique (value_spec x) hz

@[simp]
theorem value_add (x y : convergent) : value (x + y) = value x + value y :=
  value_eq_of_tendsto (x + y) ((value_spec x).add (value_spec y))

@[simp]
theorem value_smul (c : ℂ) (x : convergent) : value (c • x) = c • value x :=
  value_eq_of_tendsto (c • x) ((value_spec x).const_smul c)

theorem norm_value_le (x : convergent) : ‖value x‖ ≤ ‖x‖ := by
  have ht : Tendsto (fun n : ℕ => ‖(x : ScalarSequence) n‖) atTop (𝓝 ‖value x‖) :=
    (value_spec x).norm
  apply le_of_tendsto ht
  exact Filter.Eventually.of_forall fun n => norm_coe_le_norm (x : ScalarSequence) n

/-- The ordinary limit as an actual norm-bounded linear functional. -/
def limitCLM : convergent →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := value
      map_add' := value_add
      map_smul' := value_smul }
    1 (fun x => by
      change ‖value x‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using norm_value_le x)

@[simp]
theorem limitCLM_apply (x : convergent) : limitCLM x = value x := rfl

theorem norm_limitCLM_le_one : ‖limitCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul, limitCLM_apply] using norm_value_le x

/-- A constant sequence, regarded in the convergent subspace. -/
def constantConvergent (z : ℂ) : convergent :=
  ⟨BoundedContinuousFunction.const ℕ z, z, tendsto_const_nhds⟩

@[simp]
theorem value_constantConvergent (z : ℂ) : value (constantConvergent z) = z :=
  value_eq_of_tendsto _ tendsto_const_nhds

/-- Hahn--Banach is invoked once on the actual limit functional. -/
theorem exists_generalizedLimit :
    ∃ L : ScalarSequence →L[ℂ] ℂ,
      ‖L‖ ≤ 1 ∧ ∀ x : ScalarSequence, ∀ z : ℂ,
        Tendsto (fun n : ℕ => x n) atTop (𝓝 z) → L x = z := by
  obtain ⟨L, hext, hnorm⟩ := exists_extension_norm_eq convergent limitCLM
  refine ⟨L, hnorm.le.trans norm_limitCLM_le_one, ?_⟩
  intro x z hx
  let y : convergent := ⟨x, z, hx⟩
  calc
    L x = limitCLM y := hext y
    _ = z := value_eq_of_tendsto y hx

/-- A fixed generalized limit used by all subsequent sequence constructions. -/
def generalizedLimit : ScalarSequence →L[ℂ] ℂ :=
  Classical.choose exists_generalizedLimit

theorem norm_generalizedLimit_le_one : ‖generalizedLimit‖ ≤ 1 :=
  (Classical.choose_spec exists_generalizedLimit).1

theorem generalizedLimit_of_tendsto (x : ScalarSequence) (z : ℂ)
    (hx : Tendsto (fun n : ℕ => x n) atTop (𝓝 z)) :
    generalizedLimit x = z :=
  (Classical.choose_spec exists_generalizedLimit).2 x z hx

@[simp]
theorem generalizedLimit_const (z : ℂ) :
    generalizedLimit (BoundedContinuousFunction.const ℕ z) = z :=
  generalizedLimit_of_tendsto _ z tendsto_const_nhds

@[simp]
theorem norm_generalizedLimit : ‖generalizedLimit‖ = 1 := by
  apply le_antisymm norm_generalizedLimit_le_one
  have h := generalizedLimit.le_opNorm (BoundedContinuousFunction.const ℕ (1 : ℂ))
  simpa only [generalizedLimit_const, norm_one, norm_const_eq, mul_one] using h

/-- Null sequences are annihilated.  This property does not imply either
multiplicativity or invariance of the generalized limit. -/
theorem generalizedLimit_eq_zero (x : ScalarSequence)
    (hx : Tendsto (fun n : ℕ => x n) atTop (𝓝 0)) : generalizedLimit x = 0 :=
  generalizedLimit_of_tendsto x 0 hx

end MathlibAnnex.SequenceLimit
