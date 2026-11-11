/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.HereditaryStageAction
import MathlibAnnex.Analysis.CStarAlgebra.Hereditary.MatrixActionQuotient
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.CARQuotientCompletion
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.ClosedIdealQuotient

/-!
# An actual CAR subquotient of a nonzero antiliminal algebra

The recursively selected plateau cores define concrete closed subalgebras of
the original algebra: an element belongs to level `n` precisely when both of
its actions on that core are given by a scalar matrix. Local units in the
larger coefficient corner supply every such matrix. Transport of the next
core by the same links proves inclusion of the actual subalgebras and the
standard CAR compatibility of their quotient maps.

The existing completion theorem constructs a continuous surjection from the
norm closure of their increasing union onto the existing `CAR.Limit`.
The ideal in the final subquotient is the actual kernel of this homomorphism.
There is no ambient embedding of CAR or nonzero ambient projection hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open Set
open scoped CStarAlgebra
open MathlibAnnex.CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- Every nonzero antiliminal C-star algebra has an actual norm-closed
subalgebra admitting a surjective homomorphism onto the fixed CAR completion.
The statement allows arbitrary nonunital and nonseparable ambient algebras. -/
theorem IsAntiliminal.exists_car_subquotient (hA : IsAntiliminal A) [Nontrivial A] :
    ∃ (D : NonUnitalStarSubalgebra ℂ A) (_hD : IsClosed (D : Set A)),
      ∃ q : D →⋆ₙₐ[ℂ] CAR.Limit, Function.Surjective q := by
  classical
  obtain ⟨x, hx⟩ := exists_ne (0 : A)
  have hp : star x * x ≠ 0 := fun h => hx (star_mul_self_eq_zero.mp h)
  obtain ⟨c, b, e, v, _hc0, hc, hb, hv⟩ :=
    hA.exists_hereditary_matrix_data (star_mul_self_nonneg x) hp
  have hbc (n : ℕ) : hereditarySubalgebra (b n) ≤ hereditarySubalgebra (c n) :=
    hereditarySubalgebra_le_of_mem (hb n).2.2.1
  have hchild (n : ℕ) : c (n + 1) ∈ hereditarySubalgebra (c n) :=
    hbc n (hv n).1
  have hlink (n : ℕ) : v n ∈ hereditarySubalgebra (c n) :=
    hbc n (hv n).2.1
  have hfix (n : ℕ) : star (v n) * v n * c (n + 1) = c (n + 1) :=
    (hv n).2.2.2.2.1
  have hzero (n : ℕ) : c (n + 1) * v n = 0 := (hv n).2.2.2.2.2
  have hcself (n : ℕ) : IsSelfAdjoint (c n) := (hc n).1.isSelfAdjoint
  have hcore (n : ℕ) : hereditarySubalgebra (b (n + 1)) ≤ hereditarySubalgebra (b n) :=
    (hbc (n + 1)).trans (hereditarySubalgebra_le_of_mem (hv n).1)
  let E (n : ℕ) := hereditaryStageCoreEntry b v n
  have hstar (n : ℕ) (i j : Fin (2 ^ n)) (z : hereditarySubalgebra (b n)) :
      star (E n i j z) = E n j i (star z) :=
    star_hereditaryStageEntry v n i j (z : A)
  have hmul (n : ℕ) (i j k l : Fin (2 ^ n))
      (z w : hereditarySubalgebra (b n)) :
      E n i j z * E n k l w = if j = k then E n i l (z * w) else 0 :=
    hereditaryStageEntry_mul c v hcself hchild hlink hfix hzero n i j k l
      (hbc n z.property) (hbc n w.property)
  have hnorm (n : ℕ) (i j : Fin (2 ^ n)) (z : hereditarySubalgebra (b n)) :
      ‖E n i j z‖ = ‖z‖ :=
    norm_hereditaryStageEntry c v hcself hchild hlink hfix n i j (hbc n z.property)
  let z (n : ℕ) : hereditarySubalgebra (b n) :=
    ⟨b n, self_mem_hereditarySubalgebra (hb n).1⟩
  have hz (n : ℕ) : z n ≠ 0 := by
    intro h
    exact (hb n).2.1 (congrArg Subtype.val h)
  let D (n : ℕ) : NonUnitalStarSubalgebra ℂ A := matrixActionSubalgebra (E n) (hstar n)
  have hclosed (n : ℕ) : IsClosed (D n : Set A) :=
    isClosed_matrixActionSubalgebra (E n) (hstar n)
  let q (n : ℕ) : D n →⋆ₙₐ[ℂ] CAR.Stage n :=
    matrixActionQuotient (E n) (hstar n) (hmul n) (hnorm n) (z n) (hz n)
  have hq (n : ℕ) : Function.Surjective (q n) := by
    let U (i j : Fin (2 ^ n)) : A := hereditaryStageEntry v n i j (e n)
    have he_mem : e n ∈ hereditarySubalgebra (c n) := (hb n).2.2.2.2.2.1
    have he_left (w : hereditarySubalgebra (b n)) : e n * (w : A) = w :=
      mul_eq_self_of_mem_hereditarySubalgebra (hb n).2.2.2.2.2.2.1 w.property
    have he_right (w : hereditarySubalgebra (b n)) : (w : A) * e n = w := by
      apply mul_eq_self_of_mem_hereditarySubalgebra_right _ w.property
      simpa only [(hb n).1.star_eq] using (hb n).2.2.2.2.2.2.2
    apply matrixActionQuotient_surjective (E n) (hstar n) (hmul n) (hnorm n)
      (z n) (hz n) U
    · intro i j k l w
      change hereditaryStageEntry v n i j (e n) * hereditaryStageEntry v n k l (w : A) = _
      rw [hereditaryStageEntry_mul c v hcself hchild hlink hfix hzero n i j k l
        he_mem (hbc n w.property), he_left]
      rfl
    · intro i j k l w
      change hereditaryStageEntry v n k l (w : A) * hereditaryStageEntry v n i j (e n) = _
      rw [hereditaryStageEntry_mul c v hcself hchild hlink hfix hzero n k l i j
        (hbc n w.property) he_mem, he_right]
      rfl
  have hDstep (n : ℕ) : D n ≤ D (n + 1) := by
    rintro a ⟨M, hM⟩
    exact ⟨CAR.step n M,
      hM.hereditaryStageCoreEntry_step b v n (hcore n) (hv n).2.1⟩
  have hD : Monotone D := monotone_nat_of_le_succ hDstep
  have hqstep (n : ℕ) (a : D n) :
      q (n + 1) (NonUnitalStarSubalgebra.inclusion (hD (Nat.le_succ n)) a) =
        CAR.step n (q n a) := by
    apply ActsOnMatrixCorners.matrix_eq (E (n + 1)) (hmul (n + 1)) (hnorm (n + 1))
      (z (n + 1)) (hz (n + 1))
    · exact actsOnMatrixCorners_matrixActionQuotient (E (n + 1)) (hstar (n + 1))
        (hmul (n + 1)) (hnorm (n + 1)) (z (n + 1)) (hz (n + 1)) _
    · exact (actsOnMatrixCorners_matrixActionQuotient (E n) (hstar n)
        (hmul n) (hnorm n) (z n) (hz n) a).hereditaryStageCoreEntry_step
          b v n (hcore n) (hv n).2.1
  obtain ⟨Q, hQ, _hstage⟩ := CAR.exists_surjective_hom_topologicalClosure_iSup_of_step
    D hD hclosed q hq hqstep
  exact ⟨(⨆ n, D n).topologicalClosure,
    NonUnitalStarSubalgebra.isClosed_topologicalClosure _, Q, hQ⟩

private theorem exists_closed_kernel_equiv_car {D : Type*} [NonUnitalCStarAlgebra D]
    (q : D →⋆ₙₐ[ℂ] CAR.Limit) (hq : Function.Surjective q) :
    ∃ (J : TwoSidedIdeal D) (hJ : IsClosed (J : Set D)), J ≠ ⊤ ∧
      Nonempty (ClosedIdealQuotient.Quotient J hJ ≃⋆ₐ[ℂ] CAR.Limit) := by
  let J : TwoSidedIdeal D := TwoSidedIdeal.ker q
  have hJ : IsClosed (J : Set D) := by
    have hs : (J : Set D) = {a : D | q a = 0} := by
      ext a
      exact TwoSidedIdeal.mem_ker q
    rw [hs]
    exact isClosed_eq (map_continuous q) continuous_const
  have hproper : J ≠ ⊤ := by
    intro htop
    obtain ⟨a, ha⟩ := hq 1
    have hamem : a ∈ J := by rw [htop]; trivial
    have ha0 : q a = 0 := (TwoSidedIdeal.mem_ker q).1 hamem
    exact one_ne_zero (ha.symm.trans ha0)
  exact ⟨J, hJ, hproper,
    ⟨ClosedIdealQuotient.equivOfSurjective J hJ q hq
      (fun _ => (TwoSidedIdeal.mem_ker q).symm)⟩⟩

set_option maxHeartbeats 6000000 in
set_option diagnostics true in
/-- The preceding hom gives a literal quotient by its closed kernel, with an
actual star-algebra equivalence to the already existing CAR completion. -/
theorem IsAntiliminal.exists_car_quotient_equiv (hA : IsAntiliminal A) [Nontrivial A] :
    ∃ (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosed (D : Set A)),
      letI : IsClosed (D : Set A) := hD
      ∃ (J : TwoSidedIdeal D) (hJ : IsClosed (J : Set D)), J ≠ ⊤ ∧
        Nonempty (ClosedIdealQuotient.Quotient J hJ ≃⋆ₐ[ℂ] CAR.Limit) := by
  obtain ⟨D, hD, q, hq⟩ := hA.exists_car_subquotient
  letI : IsClosed (D : Set A) := hD
  refine ⟨D, hD, ?_⟩
  exact exists_closed_kernel_equiv_car (D := ↥D) q hq

end MathlibAnnex.Analysis.CStarAlgebra
