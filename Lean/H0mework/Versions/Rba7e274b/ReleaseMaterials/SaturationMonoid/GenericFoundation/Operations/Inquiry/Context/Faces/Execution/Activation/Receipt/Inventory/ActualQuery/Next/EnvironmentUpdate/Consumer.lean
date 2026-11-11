import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.ActualQuery.Next.EnvironmentUpdate.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualQueryBornEnvironmentUpdate
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input expression)
end N
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment (active)
end E
namespace SS
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor
 (nextFactory actual_writeback actual_whole actual_next born_inventories write)
end SS
variable {W X : PUnit.{u+1} → Type u} [∀ t, AddCommGroup (W t)]
local instance consumerGroups (n : Nat) (t : PUnit.{u+1}) : AddCommGroup (L.Value W n t) := L.groups W n t
variable (factory : SF.Factory W X PUnit.unit) (n : Nat)
variable (data : SF.Packet (W := W) (X := X) (s := PUnit.unit) n)
variable (sourceCfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := PUnit.unit))
variable (language : sourceCfg.LowVar = X)

theorem actual_emitter_current : type_of% (Admission.target_current data.1 sourceCfg
 (SS.scalar factory n data sourceCfg language) (SS.pair factory n data sourceCfg language)
 (programme factory n data sourceCfg language) (Admission.sourceEvent data.1 sourceCfg)) :=
 Admission.target_current data.1 sourceCfg (SS.scalar factory n data sourceCfg language)
  (SS.pair factory n data sourceCfg language) (programme factory n data sourceCfg language)
  (Admission.sourceEvent data.1 sourceCfg)
theorem actual_emitter_compiles : type_of% (Admission.compiles data.1 sourceCfg
 (SS.scalar factory n data sourceCfg language) (SS.pair factory n data sourceCfg language)
 (programme factory n data sourceCfg language)) :=
 Admission.compiles data.1 sourceCfg (SS.scalar factory n data sourceCfg language)
  (SS.pair factory n data sourceCfg language) (programme factory n data sourceCfg language)
theorem actual_emitter_whole : type_of% (generated factory n data sourceCfg language).target.firstDestination_heq :=
 (generated factory n data sourceCfg language).target.firstDestination_heq

-- Own new registered action consumes the very same nonzero-allowed delta AST.
theorem updated_pair :
 (R.actualMaterial (receiver factory n data sourceCfg language) (programme factory n data sourceCfg language)).raw.eval
  (N.input (R.actualMaterial (receiver factory n data sourceCfg language) (programme factory n data sourceCfg language))).environment =
 ((fullRaw n data sourceCfg).expression.eval (fullRaw n data sourceCfg).environment,
  (fullRaw n data sourceCfg).expression.effect (fullRaw n data sourceCfg).environment
   (increment factory n data sourceCfg language)) := by
 have same : (N.input (R.actualMaterial (receiver factory n data sourceCfg language)
     (programme factory n data sourceCfg language))).environment = (raw factory n data sourceCfg language).environment :=
  add_sub_cancel _ _
 exact (congrArg (fun env => (raw factory n data sourceCfg language).expression.eval env) same).trans
  (raw_pair factory n data sourceCfg language)

def ownData : SF.Packet (W := W) (X := sourceCfg.LowVar) (s := PUnit.unit) (n+1) :=
 ⟨receiver factory n data sourceCfg language, RootedAccountedUnfolding.zero
  (CofinalHistorySettlement.PresentedRelationEventAt.generator
   (receiver factory n data sourceCfg language).registered.input.expression)⟩
abbrev ownBorn := SS.born (SS.nextFactory factory n sourceCfg language) (n+1)
 (ownData factory n data sourceCfg language) (programme factory n data sourceCfg language) (by rfl)

theorem own_written : (ownBorn factory n data sourceCfg language).activeEnvironment =
 (fun _ _ => ((fullRaw n data sourceCfg).expression.eval (fullRaw n data sourceCfg).environment,
  (fullRaw n data sourceCfg).expression.effect (fullRaw n data sourceCfg).environment
   (increment factory n data sourceCfg language))) := by
 have written := E.active (SS.actual_writeback (SS.nextFactory factory n sourceCfg language) (n+1)
  (ownData factory n data sourceCfg language) (programme factory n data sourceCfg language) (by rfl))
 have writer : SS.write (n+1) (programme factory n data sourceCfg language)
   ((R.actualMaterial (receiver factory n data sourceCfg language) (programme factory n data sourceCfg language)).raw.eval
    (N.input (R.actualMaterial (receiver factory n data sourceCfg language) (programme factory n data sourceCfg language))).environment) =
  (fun _ _ => ((fullRaw n data sourceCfg).expression.eval (fullRaw n data sourceCfg).environment,
   (fullRaw n data sourceCfg).expression.effect (fullRaw n data sourceCfg).environment
    (increment factory n data sourceCfg language))) := by
  funext target name
  cases target
  exact updated_pair factory n data sourceCfg language
 exact written.trans writer

theorem own_whole : type_of% (SS.actual_whole (SS.nextFactory factory n sourceCfg language) (n+1)
 (ownData factory n data sourceCfg language) (programme factory n data sourceCfg language) (by rfl)) := SS.actual_whole _ _ _ _ _
theorem own_next : type_of% (SS.actual_next (SS.nextFactory factory n sourceCfg language) (n+1)
 (ownData factory n data sourceCfg language) (programme factory n data sourceCfg language) (by rfl)) := SS.actual_next _ _ _ _ _
theorem own_inventories : type_of% (SS.born_inventories (SS.nextFactory factory n sourceCfg language) (n+1)
 (ownData factory n data sourceCfg language) (programme factory n data sourceCfg language) (by rfl)) := SS.born_inventories _ _ _ _ _

end ActualQueryBornEnvironmentUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
