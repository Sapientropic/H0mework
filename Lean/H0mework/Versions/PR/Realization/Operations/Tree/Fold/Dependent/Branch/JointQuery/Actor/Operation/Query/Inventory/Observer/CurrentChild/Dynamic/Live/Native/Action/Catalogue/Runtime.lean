import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Catalogue.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Catalogue
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance : ∀ slot, AddCommGroup (Act.PhysicalValue root visit rec slot) := inferInstance
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor : Nat)
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (Act.LowValue root visit rec) (Act.LowVar root visit rec) (Act.sort root rec))))
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=Act.LowValue root visit rec) (Var:=Act.LowVar root visit rec) (sort:=Act.sort root rec))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (actual : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
variable (sourceStage stage : Nat)
abbrev initial : LowFrame root visit rec := Act.Owned.sourceInitial root visit rec U7 calculus anchor sourceStage stage
abbrev sourceSeed := Act.Owned.sourceSeed root visit rec U7 calculus anchor sourceStage stage
abbrev sourceConfiguration := configuration root visit rec U7 calculus anchor (sourceSeed root visit rec U7 calculus anchor sourceStage stage)
abbrev runtime := A.Shared.runtime (initial root visit rec U7 calculus anchor sourceStage stage)
 (sourceConfiguration root visit rec U7 calculus anchor sourceStage stage)
abbrev frameAt : Nat → LowFrame root visit rec := A.Shared.frames (initial root visit rec U7 calculus anchor sourceStage stage)
 (sourceConfiguration root visit rec U7 calculus anchor sourceStage stage)
def actEmbedding := SourceNativeProjectionLaw.InstallationAt.inheritedCoface
 ({(A.Shared.base frame).root.source.base with projectionLaw:=Act.component root visit rec seed frame})
 (component root visit rec U7 calculus anchor seed frame)
def installed := (actEmbedding root visit rec U7 calculus anchor seed (A.epoch frame)).trans
 (SourceNativeProjectionLaw.InstallationAt.componentCoface (A.Shared.base frame).root.source.base
  (combined root visit rec U7 calculus anchor seed (A.epoch frame))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (A.Shared.baseRoot frame (configuration root visit rec U7 calculus anchor seed)).source.base
  (A.Shared.queryLaw (A.epoch frame) (configuration root visit rec U7 calculus anchor seed))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (A.Shared.queryRoot frame (configuration root visit rec U7 calculus anchor seed)).source.base
  (A.Shared.resultLaw (A.epoch frame) (configuration root visit rec U7 calculus anchor seed))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (A.Shared.resultRoot frame (configuration root visit rec U7 calculus anchor seed)).source.base
  (A.Shared.consumerLaw (A.epoch frame) (configuration root visit rec U7 calculus anchor seed))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (A.Shared.consumerRoot frame (configuration root visit rec U7 calculus anchor seed)).source.base
  (A.Shared.compilationLaw (A.epoch frame) (configuration root visit rec U7 calculus anchor seed)))
def actualRawFace : SourceNativeRootSemanticFaceAt (A.Shared.root frame (configuration root visit rec U7 calculus anchor seed))
 (A.Shared.visit frame (configuration root visit rec U7 calculus anchor seed)) where
 projection := (installed root visit rec U7 calculus anchor seed frame).embed (ULift.up
  SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Projection.actualRaw)
 active := PUnit.unit
 classifier_eq := rfl

def restriction : SourceOperationInquiry.Context.RawRestrictionAt
 (PhysicalValue:=Act.LowValue root visit rec) (PhysicalVar:=Act.LowVar root visit rec) (sort:=Act.sort root rec)
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.presentation frame
  (configuration root visit rec U7 calculus anchor seed)).erase where
 projection := (actualRawFace root visit rec U7 calculus anchor seed frame).projection
 active := (actualRawFace root visit rec U7 calculus anchor seed frame).active
 classifier_eq := (actualRawFace root visit rec U7 calculus anchor seed frame).classifier_eq
 payload_eq := rfl

def rawSource (state : (runtime root visit rec U7 calculus anchor sourceStage stage).State) :
 SourceOperationInquiry.Context.RawAt
 (PhysicalValue:=Act.LowValue root visit rec) (PhysicalVar:=Act.LowVar root visit rec) (sort:=Act.sort root rec)
 (runtime root visit rec U7 calculus anchor sourceStage stage) state := by
 rcases state with ⟨⟨count⟩,activation⟩
 exact restriction root visit rec U7 calculus anchor (sourceSeed root visit rec U7 calculus anchor sourceStage stage)
  (frameAt root visit rec U7 calculus anchor sourceStage stage count.down)

abbrev intakeAction := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake.Lower.generatedAction
 (Act.Owned.sourceFrame root visit rec U7 calculus anchor sourceStage stage)
 (Act.Owned.sourceProgramme root visit rec U7 calculus anchor sourceStage)
 (sourceConfiguration root visit rec U7 calculus anchor sourceStage stage)
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Catalogue
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
