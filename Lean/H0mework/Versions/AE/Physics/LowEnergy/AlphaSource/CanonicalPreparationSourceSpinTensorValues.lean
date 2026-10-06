import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceSpinCoefficientTransform
import Lean

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumSpinGaussContraction
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open DiracCliffordRepresentation PointwiseDiracSpinConnectionLift
open PreparationVacuumGravityLegendreSource PreparationVacuumCoframeSpinReduction
open PreparationVacuumCoframeLegendreSource SourceQuantumGaugeSliceCoordinates GaussHistoryHilbert
open scoped BigOperators Matrix

def sourceFlatSpinSlot (i : LorentzIndex) : Fin 8:=
  ![![1,2,3,4,5,6],
    ![0,6,5,7,3,2],
    ![6,0,4,3,7,1],
    ![5,4,0,2,1,7]] i.1 i.2

def sourceFlatSpinWeight (i : LorentzIndex) : ℝ:=
  ![![1,1,1,1,1,1],
    ![-1/2,-1,1,1,1,-1],
    ![1,-1/2,-1,-1,1,1],
    ![-1,1,-1/2,1,-1,1]] i.1 i.2

open Lean Elab Tactic in
elab "unfold_source_flat_coordinate" : tactic => do
  let info ← getConstInfo ``sourceFlatSpinCoefficient
  let some value := info.value? | throwError "source coefficient has no body"
  let some coordinate := value.getUsedConstants.find? (fun n=>n.toString.endsWith ".realCoordinate")
    | throwError "source coefficient lost its original real coordinate"
  evalTactic (← `(tactic| unfold $(mkIdent coordinate)))

private theorem sourceFlatCoefficient_original (i : LorentzIndex) (a : Fin 8) :
    sourceFlatSpinCoefficient i a=
      (if a.val<4 then (sourceSpinCoordinates (sourceSpinWord i.1 i.2) a).im
        else (sourceSpinCoordinates (sourceSpinWord i.1 i.2) a).re)/2:=by
  simp only [sourceFlatSpinCoefficient,Matrix.of_apply]
  unfold_source_flat_coordinate
  by_cases phase : a.val<4
  · simp only [phase,ite_true]
    rfl
  · simp only [phase,ite_false]
    rfl

theorem sourceFlatSpinCoefficient_values (i : LorentzIndex) (a : Fin 8) :
    sourceFlatSpinCoefficient i a=if a=sourceFlatSpinSlot i then sourceFlatSpinWeight i else 0:=by
  rw [sourceFlatCoefficient_original]
  rcases i with ⟨mu,p⟩
  cases a using Fin.cases with
  | zero=>
    simp only [sourceSpinCoordinates,Fin.cases_zero,Fin.val_zero]
    fin_cases mu <;> fin_cases p <;>
      norm_num [sourceFlatSpinSlot,sourceFlatSpinWeight,sourceSpinWord,lorentzBivectorFirst,
        lorentzBivectorSecond,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,
        diracGammaThree,Matrix.trace,Matrix.mul_apply,Matrix.smul_apply,Fin.sum_univ_four,
        Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Fin.coe_ofNat_eq_mod,Nat.reduceMod] <;> decide
  | succ a=>
    simp only [sourceSpinCoordinates,Fin.cases_succ,Fin.val_succ]
    fin_cases mu <;> fin_cases p <;> fin_cases a <;>
      norm_num [sourceFlatSpinSlot,sourceFlatSpinWeight,sourceSpinWord,GaussCoframeSpin.sourceSpin,
        lorentzBivectorFirst,lorentzBivectorSecond,diracGamma,diracGammaZero,diracGammaOne,
        diracGammaTwo,diracGammaThree,diracGammaFive,Matrix.trace,Matrix.mul_apply,
        Matrix.smul_apply,Matrix.diagonal,Fin.sum_univ_four,Matrix.cons_val,Matrix.cons_val_two,
        Matrix.cons_val_three,Fin.coe_ofNat_eq_mod,Nat.reduceMod] <;> decide

def sourceFlatSpinPrice : Fin 8→ℝ:=![-3/8,3/2,3/2,3/2,-3/2,-3/2,-3/2,3/2]

attribute [local irreducible] sourceFlatSpinCoefficient sourceFlatLorentzMatrix sourceFlatOrderedTensor sourceFlatLorentzInverse

private theorem sourceConsVal5 {α : Type*} {m : ℕ} (x : α) (u : Fin m.succ.succ.succ.succ.succ→α) :
    Matrix.vecCons x u 5=Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (u))))):=rfl

private theorem sourceConsVal6 {α : Type*} {m : ℕ} (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ→α) :
    Matrix.vecCons x u 6=Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (u)))))):=rfl

private theorem sourceConsVal7 {α : Type*} {m : ℕ} (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ→α) :
    Matrix.vecCons x u 7=Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (u))))))):=rfl

private theorem sourceFlatOrderedTensor_row0 (b : Fin 8) :
    sourceFlatOrderedTensor 0 b=if (0:Fin 8)=b then sourceFlatSpinPrice 0 else 0:=by
  simp only [sourceFlatOrderedTensor,Matrix.mul_apply,Matrix.transpose_apply,sourceFlatSpinCoefficient_values,
    sourceFlatLorentzMatrix,Matrix.of_apply,Fintype.sum_prod_type]
  fin_cases b <;>
    norm_num [sourceFlatSpinSlot,sourceFlatSpinWeight,sourceFlatSpinPrice,
      Fin.sum_univ_four,Fin.sum_univ_six,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,sourceConsVal5,sourceConsVal6,sourceConsVal7,
      Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.ext_iff,Fin.val_ofNat,Fin.val_natCast,
      Fin.reduceEq,Fin.coe_ofNat_eq_mod,Nat.reduceMod]
  all_goals norm_num [sourceFlatLorentzInverse,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,sourceConsVal5,sourceConsVal6,sourceConsVal7,
      Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.ext_iff,Fin.val_ofNat,Fin.val_natCast,
    Fin.coe_ofNat_eq_mod,Nat.reduceMod]

private theorem sourceFlatOrderedTensor_row1 (b : Fin 8) :
    sourceFlatOrderedTensor 1 b=if (1:Fin 8)=b then sourceFlatSpinPrice 1 else 0:=by
  simp only [sourceFlatOrderedTensor,Matrix.mul_apply,Matrix.transpose_apply,sourceFlatSpinCoefficient_values,
    sourceFlatLorentzMatrix,Matrix.of_apply,Fintype.sum_prod_type]
  fin_cases b <;>
    norm_num [sourceFlatSpinSlot,sourceFlatSpinWeight,sourceFlatSpinPrice,
      Fin.sum_univ_four,Fin.sum_univ_six,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,sourceConsVal5,sourceConsVal6,sourceConsVal7,
      Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.ext_iff,Fin.val_ofNat,Fin.val_natCast,
      Fin.reduceEq,Fin.coe_ofNat_eq_mod,Nat.reduceMod]
  all_goals norm_num [sourceFlatLorentzInverse,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,sourceConsVal5,sourceConsVal6,sourceConsVal7,
      Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.ext_iff,Fin.val_ofNat,Fin.val_natCast,
    Fin.coe_ofNat_eq_mod,Nat.reduceMod]

private theorem sourceFlatOrderedTensor_row2 (b : Fin 8) :
    sourceFlatOrderedTensor 2 b=if (2:Fin 8)=b then sourceFlatSpinPrice 2 else 0:=by
  simp only [sourceFlatOrderedTensor,Matrix.mul_apply,Matrix.transpose_apply,sourceFlatSpinCoefficient_values,
    sourceFlatLorentzMatrix,Matrix.of_apply,Fintype.sum_prod_type]
  fin_cases b <;>
    norm_num [sourceFlatSpinSlot,sourceFlatSpinWeight,sourceFlatSpinPrice,
      Fin.sum_univ_four,Fin.sum_univ_six,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,sourceConsVal5,sourceConsVal6,sourceConsVal7,
      Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.ext_iff,Fin.val_ofNat,Fin.val_natCast,
      Fin.reduceEq,Fin.coe_ofNat_eq_mod,Nat.reduceMod]
  all_goals norm_num [sourceFlatLorentzInverse,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,sourceConsVal5,sourceConsVal6,sourceConsVal7,
      Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.ext_iff,Fin.val_ofNat,Fin.val_natCast,
    Fin.coe_ofNat_eq_mod,Nat.reduceMod]

private theorem sourceFlatOrderedTensor_row3 (b : Fin 8) :
    sourceFlatOrderedTensor 3 b=if (3:Fin 8)=b then sourceFlatSpinPrice 3 else 0:=by
  simp only [sourceFlatOrderedTensor,Matrix.mul_apply,Matrix.transpose_apply,sourceFlatSpinCoefficient_values,
    sourceFlatLorentzMatrix,Matrix.of_apply,Fintype.sum_prod_type]
  fin_cases b <;>
    norm_num [sourceFlatSpinSlot,sourceFlatSpinWeight,sourceFlatSpinPrice,
      Fin.sum_univ_four,Fin.sum_univ_six,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,sourceConsVal5,sourceConsVal6,sourceConsVal7,
      Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.ext_iff,Fin.val_ofNat,Fin.val_natCast,
      Fin.reduceEq,Fin.coe_ofNat_eq_mod,Nat.reduceMod]
  all_goals norm_num [sourceFlatLorentzInverse,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,sourceConsVal5,sourceConsVal6,sourceConsVal7,
      Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.ext_iff,Fin.val_ofNat,Fin.val_natCast,
    Fin.coe_ofNat_eq_mod,Nat.reduceMod]

private theorem sourceFlatOrderedTensor_row4 (b : Fin 8) :
    sourceFlatOrderedTensor 4 b=if (4:Fin 8)=b then sourceFlatSpinPrice 4 else 0:=by
  simp only [sourceFlatOrderedTensor,Matrix.mul_apply,Matrix.transpose_apply,sourceFlatSpinCoefficient_values,
    sourceFlatLorentzMatrix,Matrix.of_apply,Fintype.sum_prod_type]
  fin_cases b <;>
    norm_num [sourceFlatSpinSlot,sourceFlatSpinWeight,sourceFlatSpinPrice,
      Fin.sum_univ_four,Fin.sum_univ_six,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,sourceConsVal5,sourceConsVal6,sourceConsVal7,
      Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.ext_iff,Fin.val_ofNat,Fin.val_natCast,
      Fin.reduceEq,Fin.coe_ofNat_eq_mod,Nat.reduceMod]
  all_goals norm_num [sourceFlatLorentzInverse,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,sourceConsVal5,sourceConsVal6,sourceConsVal7,
      Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.ext_iff,Fin.val_ofNat,Fin.val_natCast,
    Fin.coe_ofNat_eq_mod,Nat.reduceMod]

private theorem sourceFlatOrderedTensor_row5 (b : Fin 8) :
    sourceFlatOrderedTensor 5 b=if (5:Fin 8)=b then sourceFlatSpinPrice 5 else 0:=by
  simp only [sourceFlatOrderedTensor,Matrix.mul_apply,Matrix.transpose_apply,sourceFlatSpinCoefficient_values,
    sourceFlatLorentzMatrix,Matrix.of_apply,Fintype.sum_prod_type]
  fin_cases b <;>
    norm_num [sourceFlatSpinSlot,sourceFlatSpinWeight,sourceFlatSpinPrice,
      Fin.sum_univ_four,Fin.sum_univ_six,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,sourceConsVal5,sourceConsVal6,sourceConsVal7,
      Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.ext_iff,Fin.val_ofNat,Fin.val_natCast,
      Fin.reduceEq,Fin.coe_ofNat_eq_mod,Nat.reduceMod]
  all_goals norm_num [sourceFlatLorentzInverse,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,sourceConsVal5,sourceConsVal6,sourceConsVal7,
      Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.ext_iff,Fin.val_ofNat,Fin.val_natCast,
    Fin.coe_ofNat_eq_mod,Nat.reduceMod]

private theorem sourceFlatOrderedTensor_row6 (b : Fin 8) :
    sourceFlatOrderedTensor 6 b=if (6:Fin 8)=b then sourceFlatSpinPrice 6 else 0:=by
  simp only [sourceFlatOrderedTensor,Matrix.mul_apply,Matrix.transpose_apply,sourceFlatSpinCoefficient_values,
    sourceFlatLorentzMatrix,Matrix.of_apply,Fintype.sum_prod_type]
  fin_cases b <;>
    norm_num [sourceFlatSpinSlot,sourceFlatSpinWeight,sourceFlatSpinPrice,
      Fin.sum_univ_four,Fin.sum_univ_six,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,sourceConsVal5,sourceConsVal6,sourceConsVal7,
      Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.ext_iff,Fin.val_ofNat,Fin.val_natCast,
      Fin.reduceEq,Fin.coe_ofNat_eq_mod,Nat.reduceMod]
  all_goals norm_num [sourceFlatLorentzInverse,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,sourceConsVal5,sourceConsVal6,sourceConsVal7,
      Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.ext_iff,Fin.val_ofNat,Fin.val_natCast,
    Fin.coe_ofNat_eq_mod,Nat.reduceMod]

private theorem sourceFlatOrderedTensor_row7 (b : Fin 8) :
    sourceFlatOrderedTensor 7 b=if (7:Fin 8)=b then sourceFlatSpinPrice 7 else 0:=by
  simp only [sourceFlatOrderedTensor,Matrix.mul_apply,Matrix.transpose_apply,sourceFlatSpinCoefficient_values,
    sourceFlatLorentzMatrix,Matrix.of_apply,Fintype.sum_prod_type]
  fin_cases b <;>
    norm_num [sourceFlatSpinSlot,sourceFlatSpinWeight,sourceFlatSpinPrice,
      Fin.sum_univ_four,Fin.sum_univ_six,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,sourceConsVal5,sourceConsVal6,sourceConsVal7,
      Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.ext_iff,Fin.val_ofNat,Fin.val_natCast,
      Fin.reduceEq,Fin.coe_ofNat_eq_mod,Nat.reduceMod]
  all_goals norm_num [sourceFlatLorentzInverse,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,sourceConsVal5,sourceConsVal6,sourceConsVal7,
      Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.ext_iff,Fin.val_ofNat,Fin.val_natCast,
    Fin.coe_ofNat_eq_mod,Nat.reduceMod]

theorem sourceFlatOrderedTensor_values (a b : Fin 8) :
    sourceFlatOrderedTensor a b=if a=b then sourceFlatSpinPrice a else 0:=by
  fin_cases a
  · exact sourceFlatOrderedTensor_row0 b
  · exact sourceFlatOrderedTensor_row1 b
  · exact sourceFlatOrderedTensor_row2 b
  · exact sourceFlatOrderedTensor_row3 b
  · exact sourceFlatOrderedTensor_row4 b
  · exact sourceFlatOrderedTensor_row5 b
  · exact sourceFlatOrderedTensor_row6 b
  · exact sourceFlatOrderedTensor_row7 b

end LowEnergy.PreparationVacuumSpinGaussContraction
