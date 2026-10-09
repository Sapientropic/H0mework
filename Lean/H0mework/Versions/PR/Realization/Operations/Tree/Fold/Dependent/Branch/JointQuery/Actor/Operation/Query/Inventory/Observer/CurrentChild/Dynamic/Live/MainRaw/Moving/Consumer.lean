import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.Consumer
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Syntax.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.Moving
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
namespace S
export SourceOperationInquiry.Context.Syntax
 (currentWord nextWord deltaWord deltaValue successorTrace successorRelation successor_boundary moving_equation
  deltaExecution deltaPair delta_pair delta_addition delta_whole delta_trace delta_original delta_next)
end S
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage : Nat)
local instance : AddCommGroup (CurrentChild.Value root visit recognition (CurrentChild.resultSlot root recognition)) :=
 CurrentChild.instAddCommGroupValue root visit recognition (CurrentChild.resultSlot root recognition)
abbrev actualState (count : Nat) := (engine root visit recognition U7 calculus anchor sourceStage).stateAt count
abbrev actualPaid (count : Nat) := Main.actualResult root visit recognition U7 calculus anchor
 (frameAt root visit recognition U7 calculus anchor sourceStage count)
 (sourceSeed root visit recognition U7 calculus anchor sourceStage)
 (E.Shared.actualOccurrence (frameAt root visit recognition U7 calculus anchor sourceStage count))
def syntaxDelta (count : Nat) := S.deltaWord (engine root visit recognition U7 calculus anchor sourceStage)
 (rawSource root visit recognition U7 calculus anchor sourceStage) (actualState root visit recognition U7 calculus anchor sourceStage count)
def correction (count : Nat) := S.deltaValue (engine root visit recognition U7 calculus anchor sourceStage)
 (rawSource root visit recognition U7 calculus anchor sourceStage) (actualState root visit recognition U7 calculus anchor sourceStage count)
def correctionExecution (count : Nat) := S.deltaExecution (engine root visit recognition U7 calculus anchor sourceStage)
 (rawSource root visit recognition U7 calculus anchor sourceStage) (actualState root visit recognition U7 calculus anchor sourceStage count)
def correctionPair (count : Nat) := S.deltaPair (engine root visit recognition U7 calculus anchor sourceStage)
 (rawSource root visit recognition U7 calculus anchor sourceStage) (actualState root visit recognition U7 calculus anchor sourceStage count)

theorem syntax_delta_actual (count : Nat) : syntaxDelta root visit recognition U7 calculus anchor sourceStage count =
 wordAt root visit recognition U7 calculus anchor sourceStage (count+1) -
 wordAt root visit recognition U7 calculus anchor sourceStage count := by
 unfold syntaxDelta S.deltaWord S.nextWord S.currentWord
 change Finsupp.single (Q.raw _ _ (actualState root visit recognition U7 calculus anchor sourceStage (count+1))).expression 1 -
  Finsupp.single (Q.raw _ _ (actualState root visit recognition U7 calculus anchor sourceStage count)).expression 1 = _
 rw [raw_actual,raw_actual]
 rfl

theorem correction_actual (count : Nat) : correction root visit recognition U7 calculus anchor sourceStage count =
 SourceOperationScalarRelations.evaluation (R:=ℤ)
  (mainAt root visit recognition U7 calculus anchor sourceStage (count+1)).environment
  (wordAt root visit recognition U7 calculus anchor sourceStage (count+1) -
   wordAt root visit recognition U7 calculus anchor sourceStage count) := by
 change SourceOperationScalarRelations.evaluation (R:=ℤ) (Q.readEnv _ _
  (actualState root visit recognition U7 calculus anchor sourceStage (count+1)))
  (syntaxDelta root visit recognition U7 calculus anchor sourceStage count) = _
 rw [environment_actual,syntax_delta_actual]
 rfl

private theorem paidEquation (count : Nat) : type_of% (SourceOperationInquiry.Context.Syntax.stage_result_equation
 (engine root visit recognition U7 calculus anchor sourceStage)
 (rawSource root visit recognition U7 calculus anchor sourceStage) count
 (actualPaid root visit recognition U7 calculus anchor sourceStage count).2.2.1
 (actualPaid root visit recognition U7 calculus anchor sourceStage (count+1)).2.2.1
 (main_result_value root visit recognition U7 calculus anchor sourceStage count)
 (main_result_value root visit recognition U7 calculus anchor sourceStage (count+1))) :=
 SourceOperationInquiry.Context.Syntax.stage_result_equation
 (engine root visit recognition U7 calculus anchor sourceStage)
 (rawSource root visit recognition U7 calculus anchor sourceStage) count
 (actualPaid root visit recognition U7 calculus anchor sourceStage count).2.2.1
 (actualPaid root visit recognition U7 calculus anchor sourceStage (count+1)).2.2.1
 (main_result_value root visit recognition U7 calculus anchor sourceStage count)
 (main_result_value root visit recognition U7 calculus anchor sourceStage (count+1))
theorem actual_paid_equation (count : Nat) : type_of% (paidEquation root visit recognition U7 calculus anchor sourceStage count) :=
 paidEquation root visit recognition U7 calculus anchor sourceStage count

theorem correction_addition (count : Nat) : type_of% (S.delta_addition
 (engine root visit recognition U7 calculus anchor sourceStage) (rawSource root visit recognition U7 calculus anchor sourceStage)
 (actualState root visit recognition U7 calculus anchor sourceStage count)) := S.delta_addition _ _ _
theorem correction_whole (count : Nat) : type_of% (S.delta_whole
 (engine root visit recognition U7 calculus anchor sourceStage) (rawSource root visit recognition U7 calculus anchor sourceStage)
 (actualState root visit recognition U7 calculus anchor sourceStage count)) := S.delta_whole _ _ _
theorem correction_trace (count : Nat) : type_of% (S.delta_trace
 (engine root visit recognition U7 calculus anchor sourceStage) (rawSource root visit recognition U7 calculus anchor sourceStage)
 (actualState root visit recognition U7 calculus anchor sourceStage count)) := S.delta_trace _ _ _
theorem correction_original (count : Nat) : type_of% (S.delta_original
 (engine root visit recognition U7 calculus anchor sourceStage) (rawSource root visit recognition U7 calculus anchor sourceStage)
 (actualState root visit recognition U7 calculus anchor sourceStage count)) := S.delta_original _ _ _
theorem correction_next (count : Nat) : type_of% (S.delta_next
 (engine root visit recognition U7 calculus anchor sourceStage) (rawSource root visit recognition U7 calculus anchor sourceStage)
 (actualState root visit recognition U7 calculus anchor sourceStage count)) := S.delta_next _ _ _
theorem successor_boundary (count : Nat) : type_of% (S.successor_boundary
 (engine root visit recognition U7 calculus anchor sourceStage) (rawSource root visit recognition U7 calculus anchor sourceStage)
 (actualState root visit recognition U7 calculus anchor sourceStage count)) := S.successor_boundary _ _ _

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.Moving
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
