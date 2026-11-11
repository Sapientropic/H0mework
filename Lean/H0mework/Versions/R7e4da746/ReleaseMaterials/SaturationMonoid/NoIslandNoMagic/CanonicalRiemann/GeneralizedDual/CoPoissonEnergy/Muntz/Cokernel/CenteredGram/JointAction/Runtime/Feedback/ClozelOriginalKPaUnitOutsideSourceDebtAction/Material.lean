import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaUnitOutsideSourceDebtAction.Born
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaUnitOutsideSourceDebtAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
namespace Reader
export SourceGeneratedInquiryReceiptAction (actionReader actualMaterial afterEnvironment)
end Reader
namespace Input
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation (raw transported_action_raw actual_environment)
end Input
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (next actualOccurrence)
end Shared
namespace Epoch
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
end Epoch
private theorem paired_environment_difference {Sorts : Type} {Value Var : Sorts → Type}
 [∀ target,AddCommGroup (Value target)] (after before : Env Value Var) :
 pairEnvironment after 0-pairEnvironment before 0 = pairEnvironment (after-before) 0 := by
 funext target name
 simp only [Pi.sub_apply,pairEnvironment,Prod.mk_sub_mk,sub_self]
 rfl

local instance materialSuccessorGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (source : Branches) (shift : ℝ)
variable (producer : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var)

abbrev stockSelected := actorSelected source shift
 (splitFactory producer) grade data sourceCfg language
abbrev stockCfg := actorCfg source shift
 (splitFactory producer) grade data sourceCfg language
abbrev stockBorn := actorBorn source shift
 (splitFactory producer) grade data sourceCfg language
abbrev stockMaterial := Reader.actualMaterial
 (stockSelected source shift producer grade data sourceCfg language)
 (stockCfg source shift producer grade data sourceCfg language)

/-- The literal identity reader consumes the actual stock quantity in the supplied source occurrence after its source action. -/
theorem actual_material_reader_stock
 (frame : SourceFrame grade sourceCfg)
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)) :
 Reader.actionReader frame (stockCfg source shift producer grade data sourceCfg language) supplied =
 Input.raw (grade+1) (Epoch.epoch frame) (language.symm ▸ stockReadCode) supplied := by
 change Reader.actionReader frame (AS.stockCfg (AS.template (splitFactory producer)
  grade data sourceCfg language)) supplied = _
 unfold AS.template
 exact Input.transported_action_raw language producer (stockReadCode) (grade+1) _ frame supplied

/-- The literal stock calculation and actual material reader share Raw/Env; their query traces retain separate contexts. -/
theorem actual_calculation_before_source_raw (frame : SourceFrame grade sourceCfg) :
 sourceCalculationBeforeRaw (splitFactory producer) grade data sourceCfg language frame =
 Reader.actionReader frame (stockCfg source shift producer grade data sourceCfg language)
  (Shared.actualOccurrence frame) := rfl

private theorem settled_receipt_next {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (cfg : A.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=()))
 (initial : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=())) :
 Shared.next (Complete.atReceipt cfg initial 0) cfg = Shared.nextBorn (Complete.atReceipt cfg initial 0) cfg := by
 have actual := (Complete.receipt cfg initial 0).2.2.2
 change (Complete.atReceipt cfg initial 0).action = Sum.inl (Complete.receipt cfg initial 0).2.1 at actual
 unfold Shared.next
 rw [actual]

theorem actual_stock_environment (frame : SourceFrame grade sourceCfg) :
 (Reader.actionReader frame (stockCfg source shift producer grade data sourceCfg language)
  (Shared.actualOccurrence frame)).environment = pairEnvironment frame.activeEnvironment 0 := by
 have reader := actual_material_reader_stock source shift producer grade data sourceCfg language frame (Shared.actualOccurrence frame)
 exact (congrArg (fun raw => raw.environment) reader).trans
  (congrArg (fun env => pairEnvironment env (0 : Env _ sourceCfg.LowVar)) (Input.actual_environment (grade+1) frame))

theorem actual_material_next : Shared.next
 (stockSelected source shift producer grade data sourceCfg language)
 (stockCfg source shift producer grade data sourceCfg language) =
 stockBorn source shift producer grade data sourceCfg language := settled_receipt_next _ _

theorem actual_material_after_environment : Reader.afterEnvironment
 (stockSelected source shift producer grade data sourceCfg language)
 (stockCfg source shift producer grade data sourceCfg language) =
 pairEnvironment (stockBorn source shift producer grade data sourceCfg language).activeEnvironment 0 := by
 unfold Reader.afterEnvironment
 rw [actual_material_next]
 exact actual_stock_environment source shift producer grade data sourceCfg language _

theorem actual_material_source_increment :
 (stockMaterial source shift producer grade data sourceCfg language).increment =
 pairEnvironment ((stockBorn source shift producer grade data sourceCfg language).activeEnvironment-
  (stockSelected source shift producer grade data sourceCfg language).activeEnvironment) 0 := by
 change Reader.afterEnvironment _ _ - (stockMaterial source shift producer grade data sourceCfg language).environment = _
 rw [actual_material_after_environment]
 have before := actual_stock_environment source shift producer grade data sourceCfg language
  (stockSelected source shift producer grade data sourceCfg language)
 change (stockMaterial source shift producer grade data sourceCfg language).environment = _ at before
 rw [before]
 exact paired_environment_difference _ _

/-- The actual calculation receipt keeps its own trace in the existing configured lowStock. -/
theorem actual_stock_receipt_low_stock :
 SourceGeneratedInquiryReceiptAction.Configured.lowStock
  (stockSelected source shift producer grade data sourceCfg language)
  (stockCfg source shift producer grade data sourceCfg language) =
 SourceOperationPaidRelations.exposure
  (stockMaterial source shift producer grade data sourceCfg language).state.2 := rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaUnitOutsideSourceDebtAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
