import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalRResidualInverse.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalRResidualInverse
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex MeasureTheory Set Filter
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input expression expression_eval)
end N
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (oldPaid old_paid_const old_paid_value)
end WB
local instance qualificationGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade target

theorem collapse_add (grade : Nat) (left right : PairValue (L.Value (PairValue C.Value) grade) ()) :
 CF.collapseValue grade (left + right) = CF.collapseValue grade left + CF.collapseValue grade right := by
 induction grade with
 | zero => rfl
 | succ grade prior =>
  change CF.collapseValue grade ((left.1+right.1)+(left.2+right.2)) = _
  have ordered : (left.1+right.1)+(left.2+right.2) = (left.1+left.2)+(right.1+right.2) := by abel
  rw [ordered]
  exact prior _ _

theorem total_add (grade : Nat) (left right : PairValue (L.Value (PairValue C.Value) grade) ()) :
 totalAt grade (left+right) = totalAt grade left+totalAt grade right := by
 unfold totalAt
 rw [collapse_add]
 unfold Prior.totalBranches
 simp only [Prod.fst_add,Prod.snd_add]
 abel

theorem total_neg (grade : Nat) (value : PairValue (L.Value (PairValue C.Value) grade) ()) :
 totalAt grade (-value) = -totalAt grade value := by
 have allZero : ∀ grade, totalAt grade (0 : PairValue (L.Value (PairValue C.Value) grade) ()) = 0 := by
  intro level
  induction level with
  | zero => simp [totalAt,CF.collapseValue,Prior.totalBranches]
  | succ level previous =>
   change totalAt level (0+0) = 0
   simpa only [add_zero] using previous
 have zero := allZero grade
 have generated := total_add grade value (-value)
 rw [add_neg_cancel,zero] at generated
 exact eq_neg_of_add_eq_zero_right generated.symm

theorem total_sub (grade : Nat) (left right : PairValue (L.Value (PairValue C.Value) grade) ()) :
 totalAt grade (left-right) = totalAt grade left-totalAt grade right := by
 rw [sub_eq_add_neg,total_add,total_neg,sub_eq_add_neg]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n+1))
variable (half : OriginalKCombCalculation.Half observation)

theorem original_R_code_total (grade : Nat)
 (environment : Env (PairValue (L.Value (PairValue C.Value) grade)) C.Var) :
 totalAt grade ((CF.codeAt (FR.jointCode (P.code observation nontrivial half)) grade).eval environment) =
 P.R observation nontrivial half (totalAt grade (environment () ())) :=
 (congrArg Prior.totalBranches
  (CF.code_base_value (FR.jointCode (P.code observation nontrivial half)) grade environment)).trans
  (R_code_total observation nontrivial half _)

theorem original_R_effect_total (grade : Nat)
 (environment increment : Env (PairValue (L.Value (PairValue C.Value) grade)) C.Var) :
 totalAt grade ((CF.codeAt (FR.jointCode (P.code observation nontrivial half)) grade).effect environment increment) =
 P.R observation nontrivial half (totalAt grade (increment () ())) := by
 let code := CF.codeAt (FR.jointCode (P.code observation nontrivial half)) grade
 have effect : code.effect environment increment = code.eval (environment+increment)-code.eval environment := by
  rw [Expr.eval_update]
  abel
 rw [effect,total_sub,original_R_code_total,original_R_code_total]
 change P.R observation nontrivial half (totalAt grade (environment () ()+increment () ()))-
  P.R observation nontrivial half (totalAt grade (environment () ())) = _
 rw [total_add,map_add,add_sub_cancel_left]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalRResidualInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
