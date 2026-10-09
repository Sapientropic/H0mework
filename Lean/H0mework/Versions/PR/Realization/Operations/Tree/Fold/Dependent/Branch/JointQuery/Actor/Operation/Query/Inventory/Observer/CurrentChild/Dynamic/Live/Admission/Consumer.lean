import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.Moving.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
namespace O
export SourceOperationInquiry.Context.Outgoing
 (currentRaw nextRaw mainResult mainTrace deltaWord deltaTerm correction scalarValue pairValue
  scalarExposure pairExposure nextSyntaxExposure main_value moving_equation correction_value pair_addition scalar_fee pair_fee next_syntax_fee)
end O
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage : Nat)
abbrev actualFrame := frameAt root visit recognition U7 calculus anchor sourceStage stage
abbrev actualProgramme := programme root visit recognition U7 calculus anchor sourceStage

theorem target_current : type_of% (LowStock.exact_current root visit recognition U7 calculus anchor sourceStage stage) :=
 LowStock.exact_current root visit recognition U7 calculus anchor sourceStage stage
theorem target_old : (lowInitial root visit recognition U7 calculus anchor sourceStage stage).old=
 (lowBareInitial root visit recognition U7 calculus anchor sourceStage stage).old := rfl
theorem target_registered : (lowInitial root visit recognition U7 calculus anchor sourceStage stage).registered=
 (lowBareInitial root visit recognition U7 calculus anchor sourceStage stage).registered := rfl
theorem target_packet : (lowInitial root visit recognition U7 calculus anchor sourceStage stage).packetAt=
 (lowBareInitial root visit recognition U7 calculus anchor sourceStage stage).packetAt := rfl
theorem target_environment : HEq
 (@RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.environment _ _ _ _ _
  (lowInitial root visit recognition U7 calculus anchor sourceStage stage))
 (@RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.environment _ _ _ _ _
  (lowBareInitial root visit recognition U7 calculus anchor sourceStage stage)) := HEq.rfl
theorem all_old_projection (projection) : type_of% (SourceGeneratedInquiryReceiptAction.all_old_projection
 (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
 (actualProgramme root visit recognition U7 calculus anchor sourceStage) projection) :=
 SourceGeneratedInquiryReceiptAction.all_old_projection _ _ projection

theorem current_raw : O.currentRaw (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
 (actualProgramme root visit recognition U7 calculus anchor sourceStage)=
 MainRaw.mainAt root visit recognition U7 calculus anchor sourceStage stage := rfl
theorem next_raw : type_of% (SourceOperationInquiry.Context.Outgoing.next_raw_at
 (actualProgramme root visit recognition U7 calculus anchor sourceStage)
 (initial root visit recognition U7 calculus anchor sourceStage) stage) :=
 SourceOperationInquiry.Context.Outgoing.next_raw_at
  (actualProgramme root visit recognition U7 calculus anchor sourceStage)
  (initial root visit recognition U7 calculus anchor sourceStage) stage
theorem delta_word : O.deltaWord (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
 (actualProgramme root visit recognition U7 calculus anchor sourceStage)=
 MainRaw.Moving.syntaxDelta root visit recognition U7 calculus anchor sourceStage stage := by
 rw [MainRaw.Moving.syntax_delta_actual]
 rfl

theorem source_equation : type_of% (O.moving_equation
 (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
 (actualProgramme root visit recognition U7 calculus anchor sourceStage)) := O.moving_equation _ _
theorem source_correction : type_of% (O.correction_value
 (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
 (actualProgramme root visit recognition U7 calculus anchor sourceStage)) := O.correction_value _ _
theorem source_pair_addition : type_of% (O.pair_addition
 (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
 (actualProgramme root visit recognition U7 calculus anchor sourceStage)) := O.pair_addition _ _
theorem scalar_fee : type_of% (O.scalar_fee
 (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
 (actualProgramme root visit recognition U7 calculus anchor sourceStage)) := O.scalar_fee _ _
theorem pair_fee : type_of% (O.pair_fee
 (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
 (actualProgramme root visit recognition U7 calculus anchor sourceStage)) := O.pair_fee _ _
theorem next_syntax_fee : type_of% (O.next_syntax_fee
 (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
 (actualProgramme root visit recognition U7 calculus anchor sourceStage)) := O.next_syntax_fee _ _

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
