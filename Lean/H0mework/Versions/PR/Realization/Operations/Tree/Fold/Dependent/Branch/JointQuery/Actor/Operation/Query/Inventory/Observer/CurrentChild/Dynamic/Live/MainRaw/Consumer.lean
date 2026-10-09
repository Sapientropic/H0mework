import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.Source
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Main.Consumer
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.History.Source
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Reverse.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
namespace Q
export SourceOperationInquiry.Context (raw readEnv increment pairValue pairTrace nextTrace completionPoint completionAction)
end Q
namespace Hist
export SourceOperationInquiry.Context.History (Words readPrefix sourceMap stageInventory source_stage fibre_generated stage_receipt)
end Hist
namespace Rev
export SourceOperationInquiry.Context.Faces.Reverse (reverse nextWord source_write source_trace source_original source_next source_boundary)
end Rev
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage : Nat)
abbrev Words := Hist.Words (PhysicalValue:=Value root visit recognition) (PhysicalVar:=Variable root visit recognition) (sort:=sort root recognition)
def wordAt (count : Nat) : Words root visit recognition :=
 Finsupp.single (mainAt root visit recognition U7 calculus anchor sourceStage count).expression 1

theorem main_result_value (count : Nat) : (Q.raw (engine root visit recognition U7 calculus anchor sourceStage)
 (rawSource root visit recognition U7 calculus anchor sourceStage)
 ((engine root visit recognition U7 calculus anchor sourceStage).stateAt count)).expression.eval
 (Q.readEnv (engine root visit recognition U7 calculus anchor sourceStage)
  (rawSource root visit recognition U7 calculus anchor sourceStage)
  ((engine root visit recognition U7 calculus anchor sourceStage).stateAt count)) =
 (Main.actualResult root visit recognition U7 calculus anchor
  (frameAt root visit recognition U7 calculus anchor sourceStage count)
  (sourceSeed root visit recognition U7 calculus anchor sourceStage)
  (E.Shared.actualOccurrence (frameAt root visit recognition U7 calculus anchor sourceStage count))).2.2.1 := by
 rw [raw_actual,environment_actual]
 exact ((Main.result_value root visit recognition U7 calculus anchor
  (frameAt root visit recognition U7 calculus anchor sourceStage count)
  (sourceSeed root visit recognition U7 calculus anchor sourceStage)
  (E.Shared.actualOccurrence (frameAt root visit recognition U7 calculus anchor sourceStage count))).trans
  (Live.paid_value root visit recognition U7 calculus anchor
   (E.epoch (frameAt root visit recognition U7 calculus anchor sourceStage count))
   (sourceSeed root visit recognition U7 calculus anchor sourceStage)
   (E.Shared.actualOccurrence (frameAt root visit recognition U7 calculus anchor sourceStage count)))).symm

theorem all_words_future (word : Words root visit recognition) (offset bound : Nat) (position : Fin (bound+1)) :
 Hist.readPrefix (engine root visit recognition U7 calculus anchor sourceStage)
  (rawSource root visit recognition U7 calculus anchor sourceStage) offset bound
  ((Hist.sourceMap (engine root visit recognition U7 calculus anchor sourceStage)
    (rawSource root visit recognition U7 calculus anchor sourceStage) offset).hom word) position =
 Hist.stageInventory (engine root visit recognition U7 calculus anchor sourceStage)
  (rawSource root visit recognition U7 calculus anchor sourceStage) (offset+position.val) word :=
 Hist.source_stage _ _ _ _ _ _

theorem word_at_future (sourceCount offset bound : Nat) (position : Fin (bound+1)) : type_of%
 (all_words_future root visit recognition U7 calculus anchor sourceStage
  (wordAt root visit recognition U7 calculus anchor sourceStage sourceCount) offset bound position) :=
 all_words_future root visit recognition U7 calculus anchor sourceStage
  (wordAt root visit recognition U7 calculus anchor sourceStage sourceCount) offset bound position

theorem complete_fibre_generated (offset : Nat) (left right : Words root visit recognition) : type_of%
 (Hist.fibre_generated (engine root visit recognition U7 calculus anchor sourceStage)
  (rawSource root visit recognition U7 calculus anchor sourceStage) offset left right) :=
 Hist.fibre_generated _ _ _ _ _

theorem old_effect_at (count : Nat) : Q.pairValue (engine root visit recognition U7 calculus anchor sourceStage)
 (rawSource root visit recognition U7 calculus anchor sourceStage)
 ((engine root visit recognition U7 calculus anchor sourceStage).stateAt count) =
 ((mainAt root visit recognition U7 calculus anchor sourceStage count).expression.eval
   (mainAt root visit recognition U7 calculus anchor sourceStage count).environment,
  (mainAt root visit recognition U7 calculus anchor sourceStage count).expression.effect
   (mainAt root visit recognition U7 calculus anchor sourceStage count).environment
   ((mainAt root visit recognition U7 calculus anchor sourceStage (count+1)).environment-
    (mainAt root visit recognition U7 calculus anchor sourceStage count).environment)) := by
 rw [SourceOperationInquiry.Context.pair_value,raw_actual,environment_actual,increment_actual]
 rfl

theorem full_pair_trace_fee (count : Nat) : type_of%
 (SourceOperationInquiry.Context.pair_trace_length (engine root visit recognition U7 calculus anchor sourceStage)
  (rawSource root visit recognition U7 calculus anchor sourceStage)
  ((engine root visit recognition U7 calculus anchor sourceStage).stateAt count)) :=
 SourceOperationInquiry.Context.pair_trace_length _ _ _

theorem reverse_pair (count : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Reverse.reverse_pair (engine root visit recognition U7 calculus anchor sourceStage)
  (rawSource root visit recognition U7 calculus anchor sourceStage)
  ((engine root visit recognition U7 calculus anchor sourceStage).stateAt count)) :=
 SourceOperationInquiry.Context.Faces.Reverse.reverse_pair _ _ _

theorem residual_recover_injective (count : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.recover_injective (engine root visit recognition U7 calculus anchor sourceStage)
  (rawSource root visit recognition U7 calculus anchor sourceStage)
  ((engine root visit recognition U7 calculus anchor sourceStage).stateAt count)) :=
 SourceOperationInquiry.Context.Faces.recover_injective _ _ _

theorem source_whole (count : Nat) : type_of%
 (Rev.source_write (engine root visit recognition U7 calculus anchor sourceStage)
  (rawSource root visit recognition U7 calculus anchor sourceStage)
  ((engine root visit recognition U7 calculus anchor sourceStage).stateAt count)) := Rev.source_write _ _ _
theorem source_trace (count : Nat) : type_of%
 (Rev.source_trace (engine root visit recognition U7 calculus anchor sourceStage)
  (rawSource root visit recognition U7 calculus anchor sourceStage)
  ((engine root visit recognition U7 calculus anchor sourceStage).stateAt count)) := Rev.source_trace _ _ _
theorem source_original (count : Nat) : type_of%
 (Rev.source_original (engine root visit recognition U7 calculus anchor sourceStage)
  (rawSource root visit recognition U7 calculus anchor sourceStage)
  ((engine root visit recognition U7 calculus anchor sourceStage).stateAt count)) := Rev.source_original _ _ _
theorem source_next (count : Nat) : type_of%
 (Rev.source_next (engine root visit recognition U7 calculus anchor sourceStage)
  (rawSource root visit recognition U7 calculus anchor sourceStage)
  ((engine root visit recognition U7 calculus anchor sourceStage).stateAt count)) := Rev.source_next _ _ _

theorem main_tick_receipt (count : Nat) : type_of%
 (Hist.stage_receipt (engine root visit recognition U7 calculus anchor sourceStage) count) :=
 Hist.stage_receipt _ _
theorem reverse_boundary (count : Nat) : type_of%
 (Rev.source_boundary (engine root visit recognition U7 calculus anchor sourceStage)
  (rawSource root visit recognition U7 calculus anchor sourceStage)
  ((engine root visit recognition U7 calculus anchor sourceStage).stateAt count)) := Rev.source_boundary _ _ _

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
