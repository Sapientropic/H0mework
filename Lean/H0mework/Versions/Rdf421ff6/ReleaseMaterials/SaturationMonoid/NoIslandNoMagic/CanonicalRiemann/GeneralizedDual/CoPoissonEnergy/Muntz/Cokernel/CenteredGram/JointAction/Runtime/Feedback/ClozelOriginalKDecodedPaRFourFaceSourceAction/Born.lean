import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDecodedPaRFourFaceSourceAction.Emitter
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRFourFaceSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
namespace Complete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion (receipt atReceipt receipt_next receipt_compiles)
end Complete
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (nextBorn)
end Shared
namespace Environment
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment (At active)
end Environment
namespace CF
export OriginalKFullSourceRAction.CF (collapseValue code_base_value)
end CF
namespace Pay
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (nativeEventValue)
end Pay

private theorem receipt_native_value {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (cfg : A.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=()))
 (initial : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=())) :
 Pay.nativeEventValue (Complete.atReceipt cfg initial 0).event = (Complete.receipt cfg initial 0).2.1.1 := by
 have actual := (Complete.receipt cfg initial 0).2.2.2
 change RootGeneratedDebtActivationJointSource.mathAction (Complete.atReceipt cfg initial 0).event = Sum.inl (Complete.receipt cfg initial 0).2.1 at actual
 unfold Pay.nativeEventValue
 rw [actual]

private theorem eval_language_transport {Y Z : Unit → Type} (same : Y=Z)
 {Value : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (code : Expr Value Z ()) (environment : Env Value Y) :
 (same.symm ▸ code : Expr Value Y ()).eval environment = code.eval (same ▸ environment : Env Value Z) := by
 cases same
 rfl

local instance bornSuccessorGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N : ℝ)
variable (factory : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var)

def actorCfg := AS.stockCfg (sourceEmitterBase observation nontrivial half depth ordinal h H N factory grade data sourceCfg language)
def actorReceipt := Complete.receipt (actorCfg observation nontrivial half depth ordinal h H N factory grade data sourceCfg language)
 (AS.receiver factory grade data sourceCfg language) 0
def actorSelected := Complete.atReceipt (actorCfg observation nontrivial half depth ordinal h H N factory grade data sourceCfg language)
 (AS.receiver factory grade data sourceCfg language) 0
def actorBorn := Shared.nextBorn (actorSelected observation nontrivial half depth ordinal h H N factory grade data sourceCfg language)
 (actorCfg observation nontrivial half depth ordinal h H N factory grade data sourceCfg language)
def updatedSourceTotal : PairValue (L.Value (PairValue C.Value) grade) () := WB.oldPaid data.1 sourceCfg +
 (show PairValue (L.Value (PairValue C.Value) grade) () from
  (actorReceipt observation nontrivial half depth ordinal h H N factory grade data sourceCfg language).2.1.1)

/-- The installed source decoder is executed by this actual receipt and born occurrence. -/
theorem actual_actor_born_environment : Environment.At
 (actorBorn observation nontrivial half depth ordinal h H N factory grade data sourceCfg language)
 (sourceActorWrite observation nontrivial half depth ordinal h H N factory grade data sourceCfg language
  (updatedSourceTotal observation nontrivial half depth ordinal h H N factory grade data sourceCfg language)) := by
 intro current occurrence
 change sourceActorWrite observation nontrivial half depth ordinal h H N factory grade data sourceCfg language
  (WB.oldPaid data.1 sourceCfg + (show PairValue (L.Value (PairValue C.Value) grade) () from Pay.nativeEventValue
   (actorSelected observation nontrivial half depth ordinal h H N factory grade data sourceCfg language).event)) = _
 have value : Pay.nativeEventValue (actorSelected observation nontrivial half depth ordinal h H N factory grade data sourceCfg language).event =
  (actorReceipt observation nontrivial half depth ordinal h H N factory grade data sourceCfg language).2.1.1 := receipt_native_value _ _
 exact congrArg (fun value => sourceActorWrite observation nontrivial half depth ordinal h H N factory grade data sourceCfg language
  (WB.oldPaid data.1 sourceCfg+value)) value

theorem actual_actor_active_environment :
 (actorBorn observation nontrivial half depth ordinal h H N factory grade data sourceCfg language).activeEnvironment =
 sourceActorWrite observation nontrivial half depth ordinal h H N factory grade data sourceCfg language
  (updatedSourceTotal observation nontrivial half depth ordinal h H N factory grade data sourceCfg language) :=
 Environment.active (actual_actor_born_environment _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem actual_actor_write_four_stock (value : PairValue (L.Value (PairValue C.Value) grade) ()) (name : sourceCfg.LowVar ()) :
 CF.collapseValue grade (sourceActorWrite observation nontrivial half depth ordinal h H N factory grade data sourceCfg language value () name) =
 CF.collapseValue grade value + ownFourFaceSource observation nontrivial half depth ordinal h H N := by
 unfold sourceActorWrite
 dsimp only
 rw [eval_language_transport language]
 rw [CF.code_base_value]
 change (CF.collapseValue grade ((language ▸ AS.write factory grade data sourceCfg language value) () ())+
  ownFourFaceSource observation nontrivial half depth ordinal h H N) = _
 congr 1
 cases sourceCfg with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=C.Var at language
  cases language
  simp only [AS.write,dite_true]

theorem actual_born_four_stock_increment (name : sourceCfg.LowVar ()) :
 CF.collapseValue grade ((actorBorn observation nontrivial half depth ordinal h H N factory grade data sourceCfg language).activeEnvironment () name)-
 CF.collapseValue grade (updatedSourceTotal observation nontrivial half depth ordinal h H N factory grade data sourceCfg language) =
 ownFourFaceSource observation nontrivial half depth ordinal h H N := by
 rw [actual_actor_active_environment,actual_actor_write_four_stock]
 abel

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRFourFaceSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
