import BanachGeometry.Complemented.FiniteRows
import BanachGeometry.Complemented.FinitePerturbation
import BanachGeometry.Complemented.Corner

/-! R6 finite-head split G×D and the H1–H4 criterion. G is kept as a finite
product of Y-only ℓ₁ rows; FiniteRows proves the required no-copy statement
without changing any fixed norm. D has a constructed separable dual.
The empty head/triangular array is included.
Execution evidence is recorded in the external receipts. -/
noncomputable section
open TopologicalSpace
namespace BanachGeometry
namespace HeadSplitting

abbrev Triangular (n : ℕ) := ∀ r : Fin n, Fin r.val → C0L2

def triangularPad (n : ℕ) : Triangular n →L[ℝ] (Fin n → Fin n → C0L2) where
  toFun v r s := if hs : s.val < r.val then v r ⟨s.val,hs⟩ else 0
  map_add' := by
    intro v w; funext r s; dsimp; split_ifs <;> simp
  map_smul' := by
    intro a v; funext r s; dsimp; split_ifs <;> simp
  cont := by
    apply continuous_pi; intro r
    apply continuous_pi; intro s
    by_cases hs : s.val < r.val
    · simpa only [dif_pos hs, Function.comp_def] using
        (continuous_apply (⟨s.val,hs⟩ : Fin r.val)).comp (continuous_apply r)
    · simpa only [dif_neg hs] using (continuous_const : Continuous (fun _ : Triangular n => (0 : C0L2)))

def triangularRestrict (n : ℕ) : (Fin n → Fin n → C0L2) →L[ℝ] Triangular n where
  toFun v r s := v r ⟨s.val,lt_trans s.isLt r.isLt⟩
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  cont := continuous_pi (fun r => continuous_pi (fun s =>
    (continuous_apply (⟨s.val,lt_trans s.isLt r.isLt⟩ : Fin n)).comp (continuous_apply r)))

theorem triangularRestrict_pad (n : ℕ) :
    (triangularRestrict n).comp (triangularPad n) = ContinuousLinearMap.id ℝ (Triangular n) := by
  apply ContinuousLinearMap.ext
  intro v
  funext r s
  change (if hs : s.val < r.val then v r ⟨s.val,hs⟩ else 0) = v r s
  rw [dif_pos s.isLt]

theorem separableSpace_dual_triangular (n : ℕ) : SeparableSpace (Triangular n →L[ℝ] ℝ) := by
  letI : SeparableSpace ((Fin n → Fin n → C0L2) →L[ℝ] ℝ) :=
    separableSpace_dual_pi (Fin n → C0L2) (separableSpace_dual_pi_c0L2 n) n
  exact DualTransport.separable_of_split (triangularPad n) (triangularRestrict n) (triangularRestrict_pad n)

def piProductEquiv (G : Type*) [NormedAddCommGroup G] [NormedSpace ℝ G] (n : ℕ) :
    (∀ r : Fin n, G × (Fin r.val → C0L2)) ≃L[ℝ] ((Fin n → G) × Triangular n) where
  toLinearEquiv := {
    toFun := fun z => (fun r => (z r).1, fun r => (z r).2)
    invFun := fun z r => (z.1 r, z.2 r)
    left_inv := by intro z; funext r; rfl
    right_inv := by intro z; apply Prod.ext <;> rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  continuous_toFun := (continuous_pi (fun r => continuous_fst.comp (continuous_apply r))).prodMk
    (continuous_pi (fun r => continuous_snd.comp (continuous_apply r)))
  continuous_invFun := continuous_pi (fun r => ((continuous_apply r).comp continuous_fst).prodMk
    ((continuous_apply r).comp continuous_snd))

def equiv (d : AlmostIsometricFamily)
    (e : ∀ i, (d.X i).Carrier ≃L[ℝ] ((d.Y i).Carrier × C0L2)) (n : ℕ) :
    C0Sum.FiniteHead (fun k => d.Z k) n ≃L[ℝ]
      ((Fin n → RowSplitting.G d) × Triangular n) :=
  (C0Sum.finiteHeadEquivPi (fun k => d.Z k) n).toContinuousLinearEquiv |>.trans
    ((ContinuousLinearEquiv.piCongrRight (fun r : Fin n => RowSplitting.equiv d e r.val)).trans
      (piProductEquiv (RowSplitting.G d) n))

theorem no_complemented_finiteHead (d : AlmostIsometricFamily) (h3 : d.HasCoordinateSplitting) (h4 : d.ExcludesFiniteSumCopy) (n : ℕ) :
    ¬ ContainsComplementedCopy L1C0L2 (C0Sum.FiniteHead (fun k => d.Z k) n) := by
  classical
  let e := fun i => Classical.choice (h3 i)
  intro h
  have hprod := Factorization.complemented_transport (equiv d e n) h
  exact FinitePerturbation.no_complemented_l1 C0L2 (Fin n → RowSplitting.G d) (Triangular n)
    (FiniteRows.noCopy_product_Yrows d h4 n) (separableSpace_dual_triangular n) hprod

end HeadSplitting

namespace AlmostIsometricFamily

/-- ExistsAlmostIsometricNonisomorphicPair from H2, H3 and H4 for an
AlmostIsometricFamily carrying the H1 metric data. Corner supplies the joint
corner estimate and no_complemented_finiteHead uses H3/H4. NoC0Closure and
Existence apply this criterion to the constructed quantitative Hilbert family. -/
theorem exists_almostIsometric_nonisomorphic_pair_of_complemented_splitting_exclusion (d : AlmostIsometricFamily) (h2 : d.HasContractivelyComplementedCopy) (h3 : d.HasCoordinateSplitting) (h4 : d.ExcludesFiniteSumCopy) : ExistsAlmostIsometricNonisomorphicPair :=
  d.exists_almostIsometric_nonisomorphic_pair_of_head_exclusions h2 (HeadSplitting.no_complemented_finiteHead d h3 h4)

theorem not_complemented_fixedY_of_splitting_and_finite_exclusion (d : AlmostIsometricFamily) (h3 : d.HasCoordinateSplitting) (h4 : d.ExcludesFiniteSumCopy) :
    ¬ ContainsComplementedCopy L1C0L2 d.FixedY :=
  Corner.no_complemented_of_finite_heads C0L2 (fun k => d.Z k)
    (HeadSplitting.no_complemented_finiteHead d h3 h4)

theorem nonisomorphic_fixedX_fixedY_of_complemented_splitting_exclusion (d : AlmostIsometricFamily)
    (h2 : d.HasContractivelyComplementedCopy) (h3 : d.HasCoordinateSplitting) (h4 : d.ExcludesFiniteSumCopy) : IsEmpty (d.FixedX ≃L[ℝ] d.FixedY) :=
  Factorization.nonisomorphic_of_complemented_distinction (d.fixedX_contains_complemented h2)
    (d.not_complemented_fixedY_of_splitting_and_finite_exclusion h3 h4)

end AlmostIsometricFamily
end BanachGeometry
