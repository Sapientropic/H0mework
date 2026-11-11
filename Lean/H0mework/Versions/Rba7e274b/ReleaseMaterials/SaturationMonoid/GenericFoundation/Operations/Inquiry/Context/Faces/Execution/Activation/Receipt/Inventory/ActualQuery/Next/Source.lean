import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.ActualQuery.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Common.RootConsumer.Consumer
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.ActualQuery.Next
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
end A
namespace C
export SourceGeneratedInquiryReceiptAction.Configured (generatedAction lowInitial lowProgramme)
end C
namespace Intake
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake.Lower
  (generatedAction state target_root target_next compiles successor_valid)
end Intake
namespace Q
export SourceGeneratedInquiryReceiptAction.Inventory.ActualQuery (programme commonInstalled)
end Q
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
variable (configuration : A.Programme
  (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))

abbrev sourceCfg := Q.programme configuration
abbrev target := (C.generatedAction frame (sourceCfg configuration)).target
abbrev receiver := C.lowInitial frame (sourceCfg configuration)

def projection := (target frame configuration).oldProjection
  ((Q.commonInstalled frame configuration).embed PUnit.unit)

def commonAtNext := (target frame configuration).targetRoot.source.base.projectionLaw.project
  (projection frame configuration)
  ((target frame configuration).targetRoot.emitted (target frame configuration).targetVisit.current)
  PUnit.unit

def fullRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value := PairValue PhysicalValue) (Var := configuration.LowVar) (sort := sort) :=
  (commonAtNext frame configuration).2.1

-- The next action reads the inherited complete source, including its own environment.
def actionRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value := PairValue (PairValue PhysicalValue)) (Var := configuration.LowVar) (sort := sort) :=
  ⟨pairEnvironment (fullRaw frame configuration).environment 0,
    liftExpr (fullRaw frame configuration).expression⟩

def lowProgramme :=
  { C.lowProgramme frame (sourceCfg configuration) with
    datum := fun current =>
      { (C.lowProgramme frame (sourceCfg configuration)).datum current with
        calculationReader := some (fun {_current} _supplied => actionRaw frame configuration) } }

def programme := Q.programme (lowProgramme frame configuration)

abbrev admitted := Intake.generatedAction frame (sourceCfg configuration) (programme frame configuration)
abbrev admittedState := Intake.state frame (sourceCfg configuration) (programme frame configuration)

def admittedCommon := (admitted frame configuration).target.targetRoot.source.base.projectionLaw.project
  ((admitted frame configuration).target.oldProjection ((Q.commonInstalled frame configuration).embed PUnit.unit))
  ((admitted frame configuration).target.targetRoot.emitted (admitted frame configuration).target.targetVisit.current)
  PUnit.unit

end SourceGeneratedInquiryReceiptAction.Inventory.ActualQuery.Next
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
