import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Read
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Catalogue.Charge
set_option autoImplicit false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace Future.First
namespace Cat
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Catalogue.Charge (complete_query_charge)
end Cat
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance : ∀ slot,AddCommGroup (Act.PhysicalValue root visit rec slot) := inferInstance
local instance firstStageGroup (n : Nat) (slot : SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Slot root rec) :
 AddCommGroup (Lower.Value (Act.LowValue root visit rec) n slot) := Lower.groups (Act.LowValue root visit rec) n slot
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage count : Nat)
abbrev firstFrame := initial root visit rec U7 calculus anchor sourceStage stage count
abbrev cfg := firstCfg root visit rec U7 calculus anchor sourceStage stage

theorem actual_first_fee :
 2≤remaining (Future.Actual.Q.query (firstFrame root visit rec U7 calculus anchor sourceStage stage count)
  (cfg root visit rec U7 calculus anchor sourceStage stage)).raw.expression := by
 have raw := Future.Actual.raw_generated
  (firstFrame root visit rec U7 calculus anchor sourceStage stage count)
  (cfg root visit rec U7 calculus anchor sourceStage stage)
 have sourceFee := Cat.complete_query_charge root visit rec U7 calculus anchor
  (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.sourceSeed root visit rec U7 calculus anchor sourceStage stage)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (firstFrame root visit rec U7 calculus anchor sourceStage stage count))
  (Future.Q.actualOccurrence (firstFrame root visit rec U7 calculus anchor sourceStage stage count))
 exact (congrArg (fun raw => remaining raw.expression) raw).symm ▸ sourceFee

def scalar := Lower.scalarAt (firstFrame root visit rec U7 calculus anchor sourceStage stage count)
 (cfg root visit rec U7 calculus anchor sourceStage stage) (language root visit rec U7 calculus anchor sourceStage stage) 0
def pair := Lower.pairAt (firstFrame root visit rec U7 calculus anchor sourceStage stage count)
 (cfg root visit rec U7 calculus anchor sourceStage stage) (language root visit rec U7 calculus anchor sourceStage stage) 0
def seed := Lower.Stock.seed (firstFrame root visit rec U7 calculus anchor sourceStage stage count)
 (cfg root visit rec U7 calculus anchor sourceStage stage) (language root visit rec U7 calculus anchor sourceStage stage)

theorem actual_first_environment :
 (Future.Q.query (actualFrame root visit rec U7 calculus anchor sourceStage stage count 1)
  (actualCfg root visit rec U7 calculus anchor sourceStage stage count 1)).raw.environment=
 pairEnvironment (SourceGeneratedInquiryReceiptAction.afterEnvironment
  (firstFrame root visit rec U7 calculus anchor sourceStage stage count) (cfg root visit rec U7 calculus anchor sourceStage stage)) 0 := by
 have square := Future.actual_future_square (firstFrame root visit rec U7 calculus anchor sourceStage stage count)
  (cfg root visit rec U7 calculus anchor sourceStage stage)
  (scalar root visit rec U7 calculus anchor sourceStage stage count)
  (pair root visit rec U7 calculus anchor sourceStage stage count)
  (seed root visit rec U7 calculus anchor sourceStage stage count)
  (actual_first_fee root visit rec U7 calculus anchor sourceStage stage count)
 have actualRaw := Future.Actual.raw_generated (actualFrame root visit rec U7 calculus anchor sourceStage stage count 1)
  (actualCfg root visit rec U7 calculus anchor sourceStage stage count 1)
 have nativeRaw := Future.Actual.raw_generated (Future.receiver (firstFrame root visit rec U7 calculus anchor sourceStage stage count)
  (cfg root visit rec U7 calculus anchor sourceStage stage)
  (scalar root visit rec U7 calculus anchor sourceStage stage count)
  (pair root visit rec U7 calculus anchor sourceStage stage count))
  (Future.R.programme (seed root visit rec U7 calculus anchor sourceStage stage count))
 have literal := (congrArg (fun raw => raw.environment) actualRaw).trans
  (congrArg (fun raw => raw.environment) nativeRaw).symm
 exact literal.trans square

end Future.First
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
