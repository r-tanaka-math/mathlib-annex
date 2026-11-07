import BanachGeometry.Complemented.Factorization
import BanachGeometry.SequenceSpaces.C0Operators

/-! Algebraic finite-coordinate localization from explicit corner and
shift inputs. CornerAssembly applies the concrete L1Shifts maps, and Corner
proves the joint estimate from disjoint c₀ blocks and weak ℓ₁ tails. -/

noncomputable section
namespace BanachGeometry
namespace Localization

variable {F W : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup W] [NormedSpace ℝ W]

def intoProjectionRange (P : W →L[ℝ] W) (J : F →L[ℝ] W) (Sp : F →L[ℝ] F) :
    F →L[ℝ] LinearMap.range P.toLinearMap where
  toFun x := ⟨P (J (Sp x)), ⟨J (Sp x), rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    change P (J (Sp (x + y))) = P (J (Sp x)) + P (J (Sp y))
    simp only [map_add]
  map_smul' a x := by
    apply Subtype.ext
    change P (J (Sp (a • x))) = a • P (J (Sp x))
    simp only [map_smul]
  cont := (P.continuous.comp (J.continuous.comp Sp.continuous)).subtype_mk _

/-- R6 5.2's factorization repair for one selected corner. P need not even be
idempotent for this factorization through its range. -/
theorem through_projection_range
    (J : F →L[ℝ] W) (T : W →L[ℝ] F) (hTJ : T.comp J = ContinuousLinearMap.id ℝ F)
    (Sp Sm : F →L[ℝ] F) (hSmSp : Sm.comp Sp = ContinuousLinearMap.id ℝ F)
    (hSp : ‖Sp‖ ≤ 1) (P : W →L[ℝ] W)
    (hsmall : ‖Sm.comp (T.comp (ContinuousLinearMap.id ℝ W - P))‖ * ‖J‖ < 1) :
    ContainsComplementedCopy F (LinearMap.range P.toLinearMap) := by
  let C := Sm.comp (T.comp (ContinuousLinearMap.id ℝ W - P))
  let Δ := C.comp (J.comp Sp)
  have hΔ : ‖Δ‖ < 1 := by
    calc
      ‖Δ‖ ≤ ‖C‖ * ‖J.comp Sp‖ := C.opNorm_comp_le _
      _ ≤ ‖C‖ * (‖J‖ * ‖Sp‖) :=
        mul_le_mul_of_nonneg_left (J.opNorm_comp_le Sp) (norm_nonneg C)
      _ ≤ ‖C‖ * (‖J‖ * 1) := by gcongr
      _ = ‖C‖ * ‖J‖ := by rw [mul_one]
      _ < 1 := hsmall
  let A := intoProjectionRange P J Sp
  let B := Sm.comp (T.comp (LinearMap.range P.toLinearMap).subtypeL)
  have hBA : B.comp A = ContinuousLinearMap.id ℝ F - Δ := by
    ext x
    change Sm (T (P (J (Sp x)))) = x - Sm (T (J (Sp x) - P (J (Sp x))))
    rw [map_sub, map_sub]
    have hTJx : T (J (Sp x)) = Sp x :=
      congrArg (fun f : F →L[ℝ] F => f (Sp x)) hTJ
    have hSx : Sm (Sp x) = x := congrArg (fun f : F →L[ℝ] F => f x) hSmSp
    rw [hTJx, hSx]
    abel
  obtain ⟨R, hR⟩ := Factorization.repair_left_inverse A B Δ hΔ hBA
  exact ⟨A, R, hR⟩

/-- The selected finite range is exactly the finite-head subtype of the c₀
model; no shift is applied to heterogeneous coordinate spaces. -/
theorem finite_head_localization
    (V : ℕ → Type*) [∀ n, NormedAddCommGroup (V n)] [∀ n, NormedSpace ℝ (V n)]
    (J : F →L[ℝ] C0Sum V) (T : C0Sum V →L[ℝ] F)
    (hTJ : T.comp J = ContinuousLinearMap.id ℝ F)
    (Sp Sm : F →L[ℝ] F) (hSmSp : Sm.comp Sp = ContinuousLinearMap.id ℝ F)
    (hSp : ‖Sp‖ ≤ 1) (n : ℕ)
    (hsmall : ‖Sm.comp (T.comp (C0Sum.tailCLM V n))‖ * ‖J‖ < 1) :
    ContainsComplementedCopy F (C0Sum.FiniteHead V n) :=
  through_projection_range J T hTJ Sp Sm hSmSp hSp (C0Sum.headCLM V n) hsmall

end Localization
end BanachGeometry
