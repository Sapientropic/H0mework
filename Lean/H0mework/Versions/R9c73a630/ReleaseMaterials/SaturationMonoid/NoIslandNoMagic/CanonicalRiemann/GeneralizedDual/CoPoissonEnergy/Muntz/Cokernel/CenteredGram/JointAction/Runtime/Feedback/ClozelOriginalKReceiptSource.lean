import H0mework.Versions.V2.Arithmetic.RiemannRuntime.PairedOmegaEffectRuntimeFacade
import H0mework.Versions.PR.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source
import H0mework.Versions.R9c73a630.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Consumer
import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Completion.Prefix
import H0mework.Versions.R9c73a630.Realization.Operations.Inquiry.Context.Native.Frame.Stock.Return

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombReceiptFeedback
open Complex MeasureTheory Set
open NoIslandNoMagic.CanonicalRiemann
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open RootInquiryCompletion
noncomputable section
namespace S
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
  (endpointState endpointInput packet residualMaterial)
end S
namespace Native
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest
  (MaterialAt input expression expression_eval budget residual_value updated_value)
end Native
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
end A
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (base actualOccurrence resultFace resultAt nextBorn frames runtime target_next)
end Shared
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory
  (programme lowResult decoder_preserved actual_query actual_value actual_trace_written born_complete_inventory)
end I
abbrev Value := OriginalKCombCalculation.Value
abbrev Var := OriginalKCombCalculation.Var
abbrev Frame := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value := Value) (Var := Var) (sort := ())

def constantEnvironment (value : BurnolL2) : Env Value Var := fun _ _ => value

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (depth : Nat) (half : OriginalKCombCalculation.Half observation)
abbrev sourceRoot := runtimeEffectRoot observation nontrivial
abbrev sourceVisit := (runtimeEffectRuntimeAt observation nontrivial depth).current.visit
abbrev sourceReader (occurrence : (sourceRoot observation nontrivial).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
    (sourceVisit observation nontrivial depth).current) :=
  OriginalKCombCalculation.reader observation nontrivial half occurrence
abbrev endpoint := S.endpointState (sourceRoot observation nontrivial) (sourceVisit observation nontrivial depth)
  emptyEffectU7 emptyEffectU7Calculus (sourceReader observation nontrivial depth half)
abbrev receipt := runtimeCombCalculationResultAt observation nontrivial depth half
abbrev nextEnvironment := constantEnvironment (receipt observation nontrivial depth half).2.2.1

def increment : Env Value Var := nextEnvironment observation nontrivial depth half -
  (receipt observation nontrivial depth half).1.environment

def material (occurrence : (endpoint observation nontrivial depth half).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
    (endpoint observation nontrivial depth half).visit.current) :
    Native.MaterialAt (Value := Value) (Var := Var) (sort := ()) occurrence where
  environment := (receipt observation nontrivial depth half).1.environment
  increment := increment observation nontrivial depth half
  raw := (receipt observation nontrivial depth half).1.expression
  state := (receipt observation nontrivial depth half).2.1
  owner := (S.residualMaterial (sourceRoot observation nontrivial) (sourceVisit observation nontrivial depth)
    emptyEffectU7 emptyEffectU7Calculus (sourceReader observation nontrivial depth half) occurrence).owner

abbrev endpointOccurrence := (endpoint observation nontrivial depth half).root.emitted
  (endpoint observation nontrivial depth half).visit.current

def registered := RootGeneratedDebtActivationJointSource.register
  (fun occurrence => Native.input (material observation nontrivial depth half occurrence))

private theorem not_settled (settled : SourceOperationExecutionDebt.Settlement
    (RootGeneratedDebtActivationJointSource.initialEvent (registered observation nontrivial depth half)).state) : False := by
  have zero := (RootGeneratedDebtActivationJointSource.Idle.law
    (registered observation nontrivial depth half).input.environment
    (registered observation nontrivial depth half).input.expression).settlement_budget_zero settled
  have positive := Native.budget (material observation nontrivial depth half (endpointOccurrence observation nontrivial depth half))
  change remaining (registered observation nontrivial depth half).input.expression = 0 at zero
  change remaining (registered observation nontrivial depth half).input.expression = _ at positive
  omega

def firstStep := match RootGeneratedDebtActivationJointSource.mathAction
    (RootGeneratedDebtActivationJointSource.initialEvent (registered observation nontrivial depth half)) with
  | .inl settled => False.elim (not_settled observation nontrivial depth half settled)
  | .inr paid => paid

theorem first_action : RootGeneratedDebtActivationJointSource.mathAction
    (RootGeneratedDebtActivationJointSource.initialEvent (registered observation nontrivial depth half)) =
    .inr (firstStep observation nontrivial depth half) := by
  cases selected : RootGeneratedDebtActivationJointSource.mathAction
    (RootGeneratedDebtActivationJointSource.initialEvent (registered observation nontrivial depth half)) with
  | inl settled => exact False.elim (not_settled observation nontrivial depth half settled)
  | inr paid => simp only [firstStep, selected]

def frame : Frame where
  N := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.World
    (sourceRoot observation nontrivial) (sourceVisit observation nontrivial depth) (sourceReader observation nontrivial depth half)
  V := RootGeneratedDebtActivationJointSource.OwnerFree.vocabulary
    (sourceRoot observation nontrivial).toAuthoritativeRoot (sourceVisit observation nontrivial depth).current
    (sourceReader observation nontrivial depth half)
  old := endpoint observation nontrivial depth half
  registered := registered observation nontrivial depth half
  packetAt := S.packet (sourceRoot observation nontrivial) (sourceVisit observation nontrivial depth)
    emptyEffectU7 emptyEffectU7Calculus (sourceReader observation nontrivial depth half)
  environment := fun {_current} _occurrence => nextEnvironment observation nontrivial depth half
  depth := 0
  inventory := some (SourceOperationPaidRelations.exposure (receipt observation nontrivial depth half).2.1.2)

def firstTarget := RootGeneratedDebtActivationJointSource.Successor.Inquiry.targetAt
  (endpoint observation nontrivial depth half)
  (S.endpointInput (sourceRoot observation nontrivial) (sourceVisit observation nontrivial depth)
    emptyEffectU7 emptyEffectU7Calculus (sourceReader observation nontrivial depth half)).query
  (registered observation nontrivial depth half)
  (S.packet (sourceRoot observation nontrivial) (sourceVisit observation nontrivial depth)
    emptyEffectU7 emptyEffectU7Calculus (sourceReader observation nontrivial depth half))
  ((endpoint observation nontrivial depth half).authorityAt
    (S.endpointInput (sourceRoot observation nontrivial) (sourceVisit observation nontrivial depth)
      emptyEffectU7 emptyEffectU7Calculus (sourceReader observation nontrivial depth half)).query)
  (firstStep observation nontrivial depth half) (first_action observation nontrivial depth half)
  ((endpoint observation nontrivial depth half).root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
    (endpoint observation nontrivial depth half).visit)

theorem first_next : (firstTarget observation nontrivial depth half).targetAnswerAndNext.nextCurrent =
    (frame observation nontrivial depth half).currentPresentation.erase.current :=
  (firstTarget observation nontrivial depth half).targetAnswerAndNext_next_eq

theorem updated_environment (occurrence) :
    (Native.input (material observation nontrivial depth half occurrence)).environment =
      nextEnvironment observation nontrivial depth half := by
  change (receipt observation nontrivial depth half).1.environment +
    (nextEnvironment observation nontrivial depth half - (receipt observation nontrivial depth half).1.environment) = _
  exact add_sub_cancel _ _

theorem completed_expression : (receipt observation nontrivial depth half).2.1.1 =
    .const (receipt observation nontrivial depth half).2.2.1 :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.target_expression OriginalKCombCalculation.Base
    (sourceVisit observation nontrivial depth).current
    (fun _ => (receipt observation nontrivial depth half).1)

theorem literal_residual (occurrence) :
    (Native.expression (material observation nontrivial depth half occurrence)).eval
      (Native.input (material observation nontrivial depth half occurrence)).environment =
    (receipt observation nontrivial depth half).1.expression.eval (nextEnvironment observation nontrivial depth half) -
      (receipt observation nontrivial depth half).2.2.1 := by
  rw [Native.expression_eval, updated_environment]
  change _ - (receipt observation nontrivial depth half).2.1.1.eval _ = _
  rw [completed_expression]
  rfl

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombReceiptFeedback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
