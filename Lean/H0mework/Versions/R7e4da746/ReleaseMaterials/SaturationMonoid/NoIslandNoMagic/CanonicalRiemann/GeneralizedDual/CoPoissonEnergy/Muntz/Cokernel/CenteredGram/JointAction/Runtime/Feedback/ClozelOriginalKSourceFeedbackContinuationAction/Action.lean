import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackContinuationAction.Emitter
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackContinuationAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex BurnolPhysicalState OriginalKFullSourceRAction OriginalKMaterialExpandedDualSourceAction
namespace Parent
export OriginalKSourceFeedbackSuccessorAction
 (sourceInitBornPacket actualNextSourceFrame sourceNextFrame sourceActualContinuation actualNestedSourceBinding
  sourceNextBase source_init_born_grade sourceActualCode sourceActualEnvironment sourceFeedbackNext sourceSlotsRead sourceRawSlots)
end Parent
namespace CurrentStock
export OriginalKBoundaryNativeSourceAction.Future (continuationFactory fromSourceSeed)
end CurrentStock
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (nextBase template stockCfg write)
end AS
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (oldPaid nativeAt programme)
end WB
local instance actionGroups (grade : Nat) (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
namespace P
export OriginalKSourceFeedbackSuccessorAction (sourceExprAt sourceEnvironmentAt sourceValueAt)
end P

private theorem actual_grade_eval {oldGrade newGrade : Nat} (same : oldGrade=newGrade)
 (code : P.sourceExprAt oldGrade) (environment : P.sourceEnvironmentAt newGrade) :
 (cast (congrArg P.sourceExprAt same) code).eval environment=
 cast (congrArg P.sourceValueAt same)
  (code.eval (cast (congrArg P.sourceEnvironmentAt same.symm) environment)) := by
 cases same
 rfl

private theorem actual_grade_environment {oldGrade newGrade : Nat} (same : oldGrade=newGrade)
 (environment : P.sourceEnvironmentAt oldGrade) :
 (cast (congrArg P.sourceEnvironmentAt same) environment) () ()=
 cast (congrArg P.sourceValueAt same) (environment () ()) := by
 cases same
 rfl

variable (t : ℝ) (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : OriginalKSourceFeedbackSuccessorAction.AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
local instance actionBaseGroups (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1 target) :=
 L.groups (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1 target
local instance actionNestedGroups (relative : Nat) (target : Unit) : AddCommGroup
 (L.Value (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) relative target) :=
 L.groups (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) relative target

def actualSourceValueRead
 (sourceValue : L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1 ()) : Prior.Branches :=
 CF.collapseValue packet.1 (cast (congrArg P.sourceValueAt (Parent.source_init_born_grade t factory packet)) sourceValue)

/-- Collapse only the actual native before/effect pair through its lawful original graded carrier; neither role is identified with the previous raw state. -/
def actualNativeTotalRead
 (sourceTotal : PairValue (L.Value (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) 0) ()) : Prior.Branches :=
 actualSourceValueRead t factory packet (sourceTotal.1+sourceTotal.2)

/-- The actual literal tail writer generates the complete four raw successor roles before target observer prices. -/
theorem actual_literal_source_action
 (sourceTotal : PairValue (L.Value (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) 0) ()) :
 actualNativeTotalRead t factory packet ((continuationSourceWrite t factory packet sourceTotal) () ())=
 OriginalKSourceFeedbackSuccessorAction.sourceSlotNext (actualNativeTotalRead t factory packet sourceTotal) := by
 unfold continuationSourceWrite actualCurrentTailCode
 dsimp only
 have sourceEnv : AS.write (actualCurrentSourceFactory t factory packet) 0 (actualCurrentSourceData t factory packet)
  (actualCurrentSourceBase t factory packet) rfl sourceTotal=fun _ _ => sourceTotal := by
  funext target name
  cases target
  cases name
  simp only [AS.write,dite_true]
 rw [sourceEnv]
 have paired := eval_liftExpr (Parent.actualNestedSourceBinding t factory packet () ())
  (fun _ _ => sourceTotal.1) (fun _ _ => sourceTotal.2)
 change actualNativeTotalRead t factory packet
  ((liftExpr (Parent.actualNestedSourceBinding t factory packet () ())).eval
   (pairEnvironment (fun _ _ => sourceTotal.1) (fun _ _ => sourceTotal.2)))=_
 rw [paired]
 unfold actualNativeTotalRead
 dsimp only [Prod.fst,Prod.snd]
 rw [←Expr.eval_update]
 change actualSourceValueRead t factory packet
  ((Parent.actualNestedSourceBinding t factory packet () ()).eval
   ((fun _ _ => sourceTotal.1)+(fun _ _ => sourceTotal.2)))=_
 unfold actualSourceValueRead Parent.actualNestedSourceBinding
 rw [actual_grade_eval (Parent.source_init_born_grade t factory packet).symm]
 simp only [cast_cast,cast_eq]
 rw [CF.code_base_value,OriginalKSourceFeedbackSuccessorAction.source_next_code_read]
 rw [actual_grade_environment]
 · rfl
 · exact Parent.source_init_born_grade t factory packet
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackContinuationAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
