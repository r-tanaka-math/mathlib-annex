/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.KernelNorm
import Mathlib.RingTheory.TwoSidedIdeal.Kernel

/-!
# C-star algebra operations on the actual kernel quotient

Addition, scalar multiplication, norm and completeness remain those of the
standard Banach quotient. Representatives are chosen solely to define the
product and star operation. The injective induced map proves independence
of every such choice, the algebra laws, and the C-star norm identity.
No field assumes a quotient theorem, a closed range, or an isometry.
-/

set_option autoImplicit false
noncomputable section
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra.HomKernelQuotient

universe u v
variable {A : Type u} {B : Type v}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable (q : A →⋆ₙₐ[ℂ] B)

private def representative (x : HomKernelQuotient q) : A :=
  Classical.choose (mk_surjective q x)

private theorem mk_representative (x : HomKernelQuotient q) :
    mk q (representative q x) = x := Classical.choose_spec (mk_surjective q x)

private theorem apply_representative (x : HomKernelQuotient q) :
    q (representative q x) = toCodomain q x := by
  simpa only [toCodomain_mk] using congrArg (toCodomain q) (mk_representative q x)

instance instMul : Mul (HomKernelQuotient q) :=
  ⟨fun x y => mk q (representative q x * representative q y)⟩

instance instStar : Star (HomKernelQuotient q) :=
  ⟨fun x => mk q (star (representative q x))⟩

@[simp]
theorem toCodomain_mul (x y : HomKernelQuotient q) :
    toCodomain q (x * y) = toCodomain q x * toCodomain q y := by
  change q (representative q x * representative q y) = _
  rw [map_mul, apply_representative, apply_representative]

@[simp]
theorem toCodomain_star (x : HomKernelQuotient q) :
    toCodomain q (star x) = star (toCodomain q x) := by
  change q (star (representative q x)) = _
  rw [map_star, apply_representative]

/-- Multiplication is the product of ANY representatives, not only the
chosen representatives used by the definition. -/
@[simp]
theorem mk_mul (a b : A) : mk q (a * b) = mk q a * mk q b := by
  apply toCodomain_injective q
  simp only [toCodomain_mul, toCodomain_mk, map_mul]

@[simp]
theorem mk_star (a : A) : mk q (star a) = star (mk q a) := by
  apply toCodomain_injective q
  simp only [toCodomain_star, toCodomain_mk, map_star]

instance instNonUnitalRing : NonUnitalRing (HomKernelQuotient q) where
  __ := (inferInstance : AddCommGroup (HomKernelQuotient q))
  __ := (inferInstance : Mul (HomKernelQuotient q))
  mul_assoc x y z := toCodomain_injective q (by simp only [toCodomain_mul, mul_assoc])
  left_distrib x y z := toCodomain_injective q (by simp only [toCodomain_mul, map_add, mul_add])
  right_distrib x y z := toCodomain_injective q (by simp only [toCodomain_mul, map_add, add_mul])
  zero_mul x := toCodomain_injective q (by simp only [toCodomain_mul, map_zero, zero_mul])
  mul_zero x := toCodomain_injective q (by simp only [toCodomain_mul, map_zero, mul_zero])

instance instStarRing : StarRing (HomKernelQuotient q) where
  star := star
  star_involutive x := toCodomain_injective q (by simp only [toCodomain_star, star_star])
  star_mul x y := toCodomain_injective q (by simp only [toCodomain_mul, toCodomain_star, star_mul])
  star_add x y := toCodomain_injective q (by simp only [toCodomain_star, map_add, star_add])

instance instIsScalarTower : IsScalarTower ℂ (HomKernelQuotient q) (HomKernelQuotient q) where
  smul_assoc c x y := by
    change (c • x) * y = c • (x * y)
    apply toCodomain_injective q
    simp only [toCodomain_mul, map_smul, smul_mul_assoc]

instance instSMulCommClass : SMulCommClass ℂ (HomKernelQuotient q) (HomKernelQuotient q) where
  smul_comm c x y := by
    change c • (x * y) = x * (c • y)
    apply toCodomain_injective q
    simp only [toCodomain_mul, map_smul, mul_smul_comm]

instance instStarModule : StarModule ℂ (HomKernelQuotient q) where
  star_smul c x := toCodomain_injective q (by simp only [toCodomain_star, map_smul, star_smul])

/-- The actual quotient map as a nonunital star homomorphism. -/
def mkHom : A →⋆ₙₐ[ℂ] HomKernelQuotient q where
  toFun := mk q
  map_zero' := map_zero (mk q)
  map_add' := map_add (mk q)
  map_mul' := mk_mul q
  map_smul' := map_smul (mk q)
  map_star' := mk_star q

/-- The induced injective star homomorphism into the original codomain. -/
def toCodomainHom : HomKernelQuotient q →⋆ₙₐ[ℂ] B where
  toFun := toCodomain q
  map_zero' := map_zero (toCodomain q)
  map_add' := map_add (toCodomain q)
  map_mul' := toCodomain_mul q
  map_smul' := map_smul (toCodomain q)
  map_star' := toCodomain_star q

@[simp]
theorem mkHom_apply (a : A) : mkHom q a = mk q a := rfl

@[simp]
theorem toCodomainHom_apply (x : HomKernelQuotient q) :
    toCodomainHom q x = toCodomain q x := rfl

@[simp]
theorem toCodomainHom_comp_mkHom : (toCodomainHom q).comp (mkHom q) = q := by
  ext a
  rfl

theorem mkHom_surjective : Function.Surjective (mkHom q) := mk_surjective q

theorem toCodomainHom_injective : Function.Injective (toCodomainHom q) := toCodomain_injective q

/-- The quotient kills exactly the original homomorphism kernel. -/
@[simp]
theorem mkHom_eq_zero_iff (a : A) : mkHom q a = 0 ↔ q a = 0 := by
  simpa only [mkHom_apply, map_zero] using mk_eq_mk_iff q a 0

/-- Identification with the genuine algebraic two-sided kernel, in addition
to the closed linear kernel used for the Banach norm. -/
theorem ker_mkHom : TwoSidedIdeal.ker (mkHom q) = TwoSidedIdeal.ker q := by
  apply TwoSidedIdeal.ext
  intro a
  simp only [TwoSidedIdeal.mem_ker, mkHom_eq_zero_iff]

/-- Nonzero action, rather than a unit element, provides nontriviality. -/
theorem nontrivial_of_exists_apply_ne_zero (h : ∃ a : A, q a ≠ 0) :
    Nontrivial (HomKernelQuotient q) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨⟨mk q a, 0, ?_⟩⟩
  intro hz
  have hzero := congrArg (toCodomain q) hz
  exact ha (by simpa only [toCodomain_mk, map_zero] using hzero)

/-- The algebraic quotient also correctly handles the zero homomorphism. -/
theorem subsingleton_iff : Subsingleton (HomKernelQuotient q) ↔ ∀ a : A, q a = 0 := by
  constructor
  · intro hs a
    letI : Subsingleton (HomKernelQuotient q) := hs
    have h := congrArg (toCodomain q) (Subsingleton.elim (mk q a) 0)
    simpa only [toCodomain_mk, map_zero] using h
  · intro h
    refine ⟨fun x y => ?_⟩
    obtain ⟨a, rfl⟩ := mk_surjective q x
    obtain ⟨b, rfl⟩ := mk_surjective q y
    exact (mk_eq_mk_iff q a b).2 ((h a).trans (h b).symm)

variable [PartialOrder A] [StarOrderedRing A]
variable [PartialOrder B] [StarOrderedRing B]

instance instNonUnitalNormedRing : NonUnitalNormedRing (HomKernelQuotient q) where
  __ := instNormedAddCommGroup q
  __ := instNonUnitalRing q
  norm_mul_le x y := by
    calc
      ‖x * y‖ = ‖toCodomain q (x * y)‖ := (norm_toCodomain q _).symm
      _ = ‖toCodomain q x * toCodomain q y‖ := by rw [toCodomain_mul]
      _ ≤ ‖toCodomain q x‖ * ‖toCodomain q y‖ := norm_mul_le _ _
      _ = ‖x‖ * ‖y‖ := by rw [norm_toCodomain, norm_toCodomain]

instance instCStarRing : CStarRing (HomKernelQuotient q) where
  norm_mul_self_le x := by
    calc
      ‖x‖ * ‖x‖ = ‖toCodomain q x‖ * ‖toCodomain q x‖ := by rw [norm_toCodomain]
      _ = ‖star (toCodomain q x) * toCodomain q x‖ := (CStarRing.norm_star_mul_self (x := toCodomain q x)).symm
      _ = ‖toCodomain q (star x * x)‖ := by rw [toCodomain_mul, toCodomain_star]
      _ ≤ ‖star x * x‖ := (norm_toCodomain q _).le

/-- All algebra laws and the norm identity have been proved above for the
standard Banach quotient. This instance does not transport a new norm. -/
instance instNonUnitalCStarAlgebra : NonUnitalCStarAlgebra (HomKernelQuotient q) where

end MathlibAnnex.Analysis.CStarAlgebra.HomKernelQuotient
