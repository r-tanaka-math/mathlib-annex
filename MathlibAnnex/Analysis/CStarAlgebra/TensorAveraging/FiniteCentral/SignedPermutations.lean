import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.NormNum

/-!
# A finite signed-permutation group, as permutations of signed labels

C06, UNBUILT. Defining the group as a subgroup of Perm (κ × Bool) avoids
assuming that a finite set of matrices happens to be closed under inverse.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace MathlibAnnex.FiniteCentral
universe u
variable {κ : Type u}

def flipLabel (x : κ × Bool) : κ × Bool := (x.1, !x.2)

@[simp] theorem flipLabel_flip (x : κ × Bool) : flipLabel (flipLabel x) = x := by
  rcases x with ⟨i, t⟩
  cases t <;> rfl

/-- Centralizer of sign reversal, written explicitly to fix the action. -/
def signedPermutationSubgroup (κ : Type u) : Subgroup (Equiv.Perm (κ × Bool)) where
  carrier := {e | ∀ x, e (flipLabel x) = flipLabel (e x)}
  one_mem' := by intro x; rfl
  mul_mem' := by
    intro e f he hf x
    change e (f (flipLabel x)) = flipLabel (e (f x))
    rw [hf, he]
  inv_mem' := by
    intro e he x
    change e.symm (flipLabel x) = flipLabel (e.symm x)
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]

abbrev SignedPermutation (κ : Type u) := signedPermutationSubgroup κ

instance [Fintype κ] : Fintype (SignedPermutation κ) := by
  classical
  exact Fintype.ofFinite _

/-- The scalar attached to a signed label. -/
def signScalar (t : Bool) : ℂ := if t then -1 else 1

@[simp] theorem signScalar_false : signScalar false = 1 := rfl
@[simp] theorem signScalar_true : signScalar true = -1 := rfl
@[simp] theorem signScalar_flip (t : Bool) : signScalar (!t) = -signScalar t := by
  cases t <;> norm_num [signScalar]
@[simp] theorem norm_signScalar (t : Bool) : ‖signScalar t‖ = 1 := by
  cases t <;> norm_num [signScalar]
@[simp] theorem star_signScalar (t : Bool) : star (signScalar t) = signScalar t := by
  cases t <;> simp [signScalar]
@[simp] theorem signScalar_sq (t : Bool) : signScalar t * signScalar t = 1 := by
  cases t <;> norm_num [signScalar]

/-- A signed permutation sends the two signs of one coordinate to the two
signs of one coordinate. -/
theorem signed_apply_true (g : SignedPermutation κ) (i : κ) :
    g.val (i, true) = flipLabel (g.val (i, false)) := g.property (i, false)

/-- Distinct positive coordinates cannot be identified after forgetting the sign. -/
theorem signed_first_injective (g : SignedPermutation κ) :
    Function.Injective (fun i : κ => (g.val (i, false)).1) := by
  intro i j hij
  have hp : g.val (i, false) = g.val (j, false) ∨
      g.val (i, false) = flipLabel (g.val (j, false)) := by
    have hcases : ∀ p q : κ × Bool, p.1 = q.1 → p = q ∨ p = flipLabel q := by
      rintro ⟨a, s⟩ ⟨c, t⟩ h
      dsimp at h
      subst c
      cases s <;> cases t <;> simp [flipLabel]
    exact hcases _ _ hij
  rcases hp with hp | hp
  · exact congrArg Prod.fst (g.val.injective hp)
  · rw [← signed_apply_true g j] at hp
    have hbad := congrArg Prod.snd (g.val.injective hp)
    exact Bool.noConfusion hbad

/-- Ordinary permutations embedded as sign-preserving permutations. -/
def unsignedPermutation (e : Equiv.Perm κ) : SignedPermutation κ :=
  ⟨Equiv.prodCongr e (Equiv.refl Bool), by intro x; rfl⟩

@[simp] theorem unsignedPermutation_apply (e : Equiv.Perm κ) (i : κ) (t : Bool) :
    (unsignedPermutation e).val (i, t) = (e i, t) := rfl

/-- Change the sign of exactly one coordinate. -/
def flipCoordinate [DecidableEq κ] (i : κ) : SignedPermutation κ := by
  let f : κ × Bool → κ × Bool := fun x => (x.1, if x.1 = i then !x.2 else x.2)
  have hinv : Function.Involutive f := by
    rintro ⟨j,t⟩
    by_cases h : j = i <;> simp [f, h]
  refine ⟨{ toFun := f, invFun := f, left_inv := hinv, right_inv := hinv }, ?_⟩
  rintro ⟨j,t⟩
  by_cases h : j = i <;> simp [f, h, flipLabel]

@[simp] theorem flipCoordinate_apply [DecidableEq κ] (i j : κ) (t : Bool) :
    (flipCoordinate i).val (j,t) = (j, if j = i then !t else t) := rfl

end MathlibAnnex.FiniteCentral
