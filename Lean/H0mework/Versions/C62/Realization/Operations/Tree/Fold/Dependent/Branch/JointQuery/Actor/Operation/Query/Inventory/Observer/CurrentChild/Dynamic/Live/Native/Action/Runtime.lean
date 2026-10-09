import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance : ∀ slot, AddCommGroup (PhysicalValue root visit rec slot) := inferInstance
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (LowValue root visit rec) (LowVar root visit rec) (sort root rec))))
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=LowValue root visit rec) (Var:=LowVar root visit rec) (sort:=sort root rec))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (actual : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
variable (initial : type_of% frame)
inductive Projection
 | material
 | actualRaw
 deriving DecidableEq

def component : SourceNativeProjectionLaw (A.Shared.base frame).root.source.base.restructuringSource.toLedgerSource where
 Projection:=ULift.{u} Projection
 ActiveAt:=fun _ {_current} _ => PUnit.{u+1}
 InactiveAt:=fun _ {_current} _ => PEmpty.{u+1}
 classify:=fun _ {_current} _ => .inl PUnit.unit
 PayloadAt:=fun projection {_current} supplied _ => match projection.down with
  | .material => type_of%
   (material root visit rec seed frame supplied,physicalRaw root visit rec frame supplied,
    physicalNext root visit rec frame supplied,physicalActionRaw root visit rec frame supplied,
    physicalReplay root visit rec frame supplied,scalarWritten root visit rec seed frame supplied,
    pairWritten root visit rec seed frame supplied)
  | .actualRaw => type_of% (actualRaw root visit rec frame supplied)
 project:=fun projection {_current} supplied _ => match projection.down with
  | .material =>
   (material root visit rec seed frame supplied,physicalRaw root visit rec frame supplied,
    physicalNext root visit rec frame supplied,physicalActionRaw root visit rec frame supplied,
    physicalReplay root visit rec frame supplied,scalarWritten root visit rec seed frame supplied,
    pairWritten root visit rec seed frame supplied)
  | .actualRaw => actualRaw root visit rec frame supplied
def configuration := {R.programme seed with
 datum:=fun sourceFrame => {
  component:=some (component root visit rec seed sourceFrame)
  reader:=fun {_current} supplied => raw root visit rec seed sourceFrame supplied
  nextEnvironmentReadAt:=some (fun {_current} supplied _ =>
   physicalNext root visit rec sourceFrame supplied) }
 nextInventory:=fun sourceFrame => some (scalarWritten root visit rec seed sourceFrame
  (A.Shared.actualOccurrence sourceFrame))
 nextPairInventory:=fun sourceFrame => some (pairWritten root visit rec seed sourceFrame
  (A.Shared.actualOccurrence sourceFrame)) }
abbrev born := A.Shared.nextBorn frame (configuration root visit rec seed)
abbrev runtime := A.Shared.runtime initial (configuration root visit rec seed)
abbrev frameAt (offset : Nat) := A.Shared.frames initial (configuration root visit rec seed) offset
def installation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
 (A.Shared.base frame).root.source.base (component root visit rec seed (A.epoch frame))).trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame (configuration root visit rec seed)).source.base
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.queryLaw (A.epoch frame) (configuration root visit rec seed))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.queryRoot frame (configuration root visit rec seed)).source.base
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultLaw (A.epoch frame) (configuration root visit rec seed))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultRoot frame (configuration root visit rec seed)).source.base
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.consumerLaw (A.epoch frame) (configuration root visit rec seed))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.consumerRoot frame (configuration root visit rec seed)).source.base
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.compilationLaw (A.epoch frame) (configuration root visit rec seed)))
def actualRawFace : SourceNativeRootSemanticFaceAt (A.Shared.root frame (configuration root visit rec seed))
 (A.Shared.visit frame (configuration root visit rec seed)) where
 projection := (installation root visit rec seed frame).embed (ULift.up .actualRaw)
 active := PUnit.unit
 classifier_eq := rfl
def frameRestriction : SourceOperationInquiry.Context.RawRestrictionAt
 (PhysicalValue:=LowValue root visit rec) (PhysicalVar:=LowVar root visit rec) (sort:=sort root rec)
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.presentation frame (configuration root visit rec seed)).erase where
 projection := (actualRawFace root visit rec seed frame).projection
 active := (actualRawFace root visit rec seed frame).active
 classifier_eq := (actualRawFace root visit rec seed frame).classifier_eq
 payload_eq := rfl

def actualRawSource (state : (runtime root visit rec seed initial).State) :
 SourceOperationInquiry.Context.RawAt
 (PhysicalValue:=LowValue root visit rec) (PhysicalVar:=LowVar root visit rec) (sort:=sort root rec)
 (runtime root visit rec seed initial) state := by
 rcases state with ⟨⟨count⟩,activation⟩
 exact frameRestriction root visit rec seed (frameAt root visit rec seed initial count.down)

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
