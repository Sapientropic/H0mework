import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim
namespace Actual
open RootLawDependentJointStateController
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.Profile.Kernel.Actual.physicalGroups
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.Profile.Kernel.Actual.currentGroups
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
variable (anchor sourceStage stage count : Nat)
namespace Run
export Lower.SourceFamily.Foresight.Contextual.Profile.Kernel.Actual.Run (binding data actual_depth)
end Run
abbrev actualPayment (k : Nat) := payment (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)
theorem actual_claim (k : Nat) : type_of% (actual_claim_equation (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)
 (Run.actual_depth root visit rec U7 calculus anchor sourceStage stage count k)) :=
 actual_claim_equation _ _ _ (Run.actual_depth root visit rec U7 calculus anchor sourceStage stage count k)
theorem actual_debit (k : Nat) : type_of% (actualPayment root visit rec U7 calculus anchor sourceStage stage count k).strictDebit :=
 (actualPayment root visit rec U7 calculus anchor sourceStage stage count k).strictDebit
theorem actual_owner (k : Nat) : type_of% (input_owner (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)) := input_owner _ _ _
theorem actual_receiver (k : Nat) : type_of% (congrArg Prod.fst
 (Lower.SourceFamily.Foresight.Contextual.Profile.Kernel.Actual.next_packet
  root visit rec U7 calculus anchor sourceStage stage count k)) :=
 congrArg Prod.fst (Lower.SourceFamily.Foresight.Contextual.Profile.Kernel.Actual.next_packet
  root visit rec U7 calculus anchor sourceStage stage count k)
theorem actual_debt_current (k : Nat) : type_of% (debt_current (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)) := debt_current _ _ _
theorem actual_no_refill (k : Nat) : type_of% (Pay.no_refill (Wr.receiver (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k))) := Pay.no_refill _
theorem consume (k : Nat) : type_of% (And.intro
 (actual_claim root visit rec U7 calculus anchor sourceStage stage count k)
 (And.intro (actual_debit root visit rec U7 calculus anchor sourceStage stage count k)
 (Lower.SourceFamily.Replay.Activated.actual_whole_next root visit rec U7 calculus anchor sourceStage stage count (k+1)))) :=
 ⟨actual_claim _ _ _ _ _ _ _ _ _ _,actual_debit _ _ _ _ _ _ _ _ _ _,
 Lower.SourceFamily.Replay.Activated.actual_whole_next _ _ _ _ _ _ _ _ _ _⟩
end Actual
end Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
