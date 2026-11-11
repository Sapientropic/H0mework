import H0mework.Versions.Rdf421ff6.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake.Consumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Configured.Material
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (base baseRoot root visit actualOccurrence queryRoot resultRoot consumerRoot queryLaw resultLaw consumerLaw compilationLaw runtime)
end S
namespace I
export SourceOperationInquiry.Context.Installation (Occurrence materialAt)
end I
namespace J
export RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw (Current)
end J
namespace R
export SourceGeneratedInquiryReceiptAction (occurrence actualMaterial actionResultAt sourceEvent afterEnvironment)
end R
namespace CF
export SourceGeneratedInquiryReceiptAction.Configured (lowInitial lowProgramme)
end CF
namespace Intake
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake.Lower
 (generatedAction state sourcePresentation targetPresentation target_root target_next compiles successor_valid)
end Intake

variable {Sorts : Type u} {Value Var : Sorts → Type u}
 [∀ target, AddCommGroup (Value target)] {sort : Sorts}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value := Value) (Var := Var) (sort := sort))
variable (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
variable (baseProgramme : A.Programme (PhysicalValue := PairValue Value) (PhysicalVar := cfg.LowVar) (sort := sort))
variable (receiver : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value := PairValue Value) (Var := cfg.LowVar) (sort := sort))
variable {current : J.Current receiver.registered}
variable (supplied : I.Occurrence receiver (current := current))

/-- The fixed prefix and the receiver's supplied current retain their own occurrence indices. -/
structure SourceAt where
 prefixMaterial : type_of% (R.actualMaterial frame cfg)
 prefixResult : type_of% (R.actionResultAt frame cfg (R.occurrence frame cfg))
 currentMaterial : type_of% (I.materialAt receiver supplied)

def sourceAt : SourceAt frame cfg receiver supplied :=
 ⟨R.actualMaterial frame cfg, R.actionResultAt frame cfg (R.occurrence frame cfg), I.materialAt receiver supplied⟩

def prefixLaw : SourceNativeProjectionLaw
 (S.base receiver).root.source.base.restructuringSource.toLedgerSource where
 Projection := PUnit.{u+1}
 ActiveAt := fun _ {_current} _ => PUnit.{u+1}
 InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun _ {_current} occurrence _ => SourceAt frame cfg receiver occurrence
 project := fun _ {_current} occurrence _ => sourceAt frame cfg receiver occurrence

def fullSource := (S.root receiver baseProgramme).source.base.withProjectionCoface
 (prefixLaw frame cfg receiver)

def programme : A.Programme (PhysicalValue := PairValue Value) (PhysicalVar := cfg.LowVar) (sort := sort) :=
 { baseProgramme with
   datum := fun receiver => {
    baseProgramme.datum receiver with
    component := some (fullSource frame cfg baseProgramme receiver).projectionLaw } }

def componentInstallation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
 (S.base receiver).root.source.base
 (fullSource frame cfg baseProgramme (A.epoch receiver)).projectionLaw).trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (S.baseRoot receiver (programme frame cfg baseProgramme)).source.base
  (S.queryLaw (A.epoch receiver) (programme frame cfg baseProgramme))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (S.queryRoot receiver (programme frame cfg baseProgramme)).source.base
  (S.resultLaw (A.epoch receiver) (programme frame cfg baseProgramme))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (S.resultRoot receiver (programme frame cfg baseProgramme)).source.base
  (S.consumerLaw (A.epoch receiver) (programme frame cfg baseProgramme))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (S.consumerRoot receiver (programme frame cfg baseProgramme)).source.base
  (S.compilationLaw (A.epoch receiver) (programme frame cfg baseProgramme)))

def oldInstallation := (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
 (S.root receiver baseProgramme).source.base
 (prefixLaw frame cfg (A.epoch receiver))).trans
 (componentInstallation frame cfg baseProgramme receiver)

def prefixInstallation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
 (S.root receiver baseProgramme).source.base
 (prefixLaw frame cfg (A.epoch receiver))).trans
 (componentInstallation frame cfg baseProgramme receiver)

abbrev initial := CF.lowInitial frame cfg
abbrev generatedAction := Intake.generatedAction frame cfg (programme frame cfg baseProgramme)
abbrev state := Intake.state frame cfg (programme frame cfg baseProgramme)
abbrev sourcePresentation := Intake.sourcePresentation frame cfg (programme frame cfg baseProgramme)
abbrev targetPresentation := Intake.targetPresentation frame cfg (programme frame cfg baseProgramme)
abbrev runtime := S.runtime (initial frame cfg) (programme frame cfg baseProgramme)

def nextMaterialFace : SourceNativeRootSemanticFaceAt
 (generatedAction frame cfg baseProgramme).target.targetRoot
 (generatedAction frame cfg baseProgramme).target.targetVisit where
 projection := (prefixInstallation frame cfg baseProgramme (initial frame cfg)).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl

theorem next_prefix_material :
 (nextMaterialFace frame cfg baseProgramme).rootRead.prefixMaterial = R.actualMaterial frame cfg := rfl

theorem next_prefix_result :
 (nextMaterialFace frame cfg baseProgramme).rootRead.prefixResult =
 R.actionResultAt frame cfg (R.occurrence frame cfg) := rfl

theorem programme_reader : ((programme frame cfg baseProgramme).datum receiver).reader supplied =
 (baseProgramme.datum receiver).reader supplied := rfl

theorem programme_calculation_reader : ((programme frame cfg baseProgramme).datum receiver).calculationReader =
 (baseProgramme.datum receiver).calculationReader := rfl

theorem programme_decoder : ((programme frame cfg baseProgramme).datum receiver).nextEnvironmentRead =
 (baseProgramme.datum receiver).nextEnvironmentRead := rfl

theorem programme_dependent_decoder : ((programme frame cfg baseProgramme).datum receiver).nextEnvironmentReadAt =
 (baseProgramme.datum receiver).nextEnvironmentReadAt := rfl

theorem programme_inventory : (programme frame cfg baseProgramme).nextInventory = baseProgramme.nextInventory := rfl

theorem programme_pair_inventory : (programme frame cfg baseProgramme).nextPairInventory = baseProgramme.nextPairInventory := rfl

theorem target_root : type_of% (Intake.target_root frame cfg (programme frame cfg baseProgramme) (R.sourceEvent frame cfg)) :=
 Intake.target_root frame cfg (programme frame cfg baseProgramme) (R.sourceEvent frame cfg)

theorem target_next : type_of% (Intake.target_next frame cfg (programme frame cfg baseProgramme) (R.sourceEvent frame cfg)) :=
 Intake.target_next frame cfg (programme frame cfg baseProgramme) (R.sourceEvent frame cfg)

theorem compiles : type_of% (Intake.compiles frame cfg (programme frame cfg baseProgramme)) :=
 Intake.compiles frame cfg (programme frame cfg baseProgramme)

theorem whole_first : type_of% (generatedAction frame cfg baseProgramme).target.firstDestination_heq :=
 (generatedAction frame cfg baseProgramme).target.firstDestination_heq

theorem successor_valid : type_of% (Intake.successor_valid frame cfg (programme frame cfg baseProgramme)) :=
 Intake.successor_valid frame cfg (programme frame cfg baseProgramme)

theorem runtime_initial : (runtime frame cfg baseProgramme).initialState.engine.node =
 .active (targetPresentation frame cfg baseProgramme) := rfl

end SourceGeneratedInquiryReceiptAction.Configured.Material
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
