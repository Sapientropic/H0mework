import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKReceiptSource

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
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (depth : Nat) (half : OriginalKCombCalculation.Half observation)

-- Source programme remains original R^m with a variable input; the new seed is a prior paid receipt.
def action := burnolDirectRightResolventCLM (originalKCoordinate observation.coordinate
  (observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial).2 half.down)
abbrev count := generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
abbrev code := OriginalKCombCalculation.code (action observation nontrivial half) (count observation)

def lowRaw (current : Frame) : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value := PairValue Value) (Var := Var) (sort := ()) :=
  ⟨pairEnvironment current.rawRead.environment (current.activeEnvironment - current.rawRead.environment),
    liftExpr (code observation nontrivial half)⟩

def lowResult (current : Frame) := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
  (Shared.base current).root.toAuthoritativeRoot
  (fun {_current} _occurrence => lowRaw observation nontrivial half (A.epoch current))
  (Shared.actualOccurrence current)

def lowProgramme : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := ()) where
  LowVar := Var
  datum current := {
    component := none
    reader := fun {_current} _occurrence => lowRaw observation nontrivial half current
    nextEnvironmentReadAt := some (fun {_current} _occurrence pair => constantEnvironment (pair.1 + pair.2)) }
  nextInventory current := some (match current.inventory with
    | none => SourceOperationPaidRelations.exposure current.paidRead.state.2
    | some prior => SourceHistoryCommon.seed prior (SourceOperationPaidRelations.exposure current.paidRead.state.2))
  nextPairInventory current := some (match current.pairInventory with
    | none => SourceOperationPaidRelations.exposure (lowResult observation nontrivial half current).2.1.2
    | some prior => SourceHistoryCommon.seed prior (SourceOperationPaidRelations.exposure (lowResult observation nontrivial half current).2.1.2))

def configuration : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := ()) :=
  I.programme (lowProgramme observation nontrivial half)

namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment (At active epoch)
end E
namespace Complete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion
  (receipt atReceipt receipt_next receipt_compiles)
end Complete

theorem residual_action (occurrence) :
    (Native.expression (material observation nontrivial depth half occurrence)).eval
      (Native.input (material observation nontrivial depth half occurrence)).environment =
      ((action observation nontrivial half) ^ count observation)
        (receipt observation nontrivial depth half).2.2.1 - (receipt observation nontrivial depth half).2.2.1 := by
  exact (literal_residual observation nontrivial depth half occurrence).trans
    (congrArg (fun value => value - (receipt observation nontrivial depth half).2.2.1)
      (OriginalKCombCalculation.code_eval _ _ _))

theorem initial_environment : E.At (frame observation nontrivial depth half)
    (nextEnvironment observation nontrivial depth half) := fun _ => rfl

theorem low_value (current : Frame) :
    ((lowResult observation nontrivial half current).2.2.1).1 +
      ((lowResult observation nontrivial half current).2.2.1).2 =
    ((action observation nontrivial half) ^ count observation)
      ((A.epoch current).activeEnvironment () ()) := by
  have paid := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (Shared.base current).root.toAuthoritativeRoot
    (fun {_current} _occurrence => lowRaw observation nontrivial half (A.epoch current))
    (Shared.actualOccurrence current)
  have combined := congrArg (fun pair : PairValue Value () => pair.1 + pair.2) paid
  change _ = ((liftExpr (code observation nontrivial half)).eval
    (pairEnvironment (A.epoch current).rawRead.environment
      ((A.epoch current).activeEnvironment - (A.epoch current).rawRead.environment))).1 +
    ((liftExpr (code observation nontrivial half)).eval
    (pairEnvironment (A.epoch current).rawRead.environment
      ((A.epoch current).activeEnvironment - (A.epoch current).rawRead.environment))).2 at combined
  rw [eval_liftExpr] at combined
  change _ = (code observation nontrivial half).eval (A.epoch current).rawRead.environment +
    (code observation nontrivial half).effect (A.epoch current).rawRead.environment
      ((A.epoch current).activeEnvironment - (A.epoch current).rawRead.environment) at combined
  rw [← Expr.eval_update, add_sub_cancel] at combined
  exact combined.trans (OriginalKCombCalculation.code_eval _ _ _)

-- The decoder consumes the actual low receipt retained by the stock factory.
theorem born_environment (current : Frame) :
    E.At (Value := Value) (Var := Var) (sort := ())
      (Shared.nextBorn current (configuration observation nontrivial half))
      (constantEnvironment (((action observation nontrivial half) ^ count observation)
        ((A.epoch current).activeEnvironment () ()))) := by
  intro _ occurrence
  change constantEnvironment
    ((I.lowResult (A.epoch current) (lowProgramme observation nontrivial half)
      (Shared.actualOccurrence current)).2.2.1.1 +
     (I.lowResult (A.epoch current) (lowProgramme observation nontrivial half)
      (Shared.actualOccurrence current)).2.2.1.2) = _
  have paid := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot
      (A.epoch current) (lowProgramme observation nontrivial half)).toAuthoritativeRoot
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum
      (A.epoch current) (lowProgramme observation nontrivial half)).reader
    (Shared.actualOccurrence current)
  have combined := congrArg (fun pair : PairValue Value () => pair.1 + pair.2) paid
  change _ = ((liftExpr (code observation nontrivial half)).eval
    (pairEnvironment (A.epoch current).rawRead.environment
      ((A.epoch current).activeEnvironment - (A.epoch current).rawRead.environment))).1 +
    ((liftExpr (code observation nontrivial half)).eval
    (pairEnvironment (A.epoch current).rawRead.environment
      ((A.epoch current).activeEnvironment - (A.epoch current).rawRead.environment))).2 at combined
  rw [eval_liftExpr] at combined
  change _ = (code observation nontrivial half).eval (A.epoch current).rawRead.environment +
    (code observation nontrivial half).effect (A.epoch current).rawRead.environment
      ((A.epoch current).activeEnvironment - (A.epoch current).rawRead.environment) at combined
  rw [← Expr.eval_update, add_sub_cancel] at combined
  exact congrArg constantEnvironment (combined.trans (OriginalKCombCalculation.code_eval _ _ _))

abbrev selected := Complete.atReceipt (configuration observation nontrivial half)
  (frame observation nontrivial depth half) 0

theorem selected_environment : (selected observation nontrivial depth half).activeEnvironment =
    nextEnvironment observation nontrivial depth half :=
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix.receipt_environment
    (configuration observation nontrivial half) (frame observation nontrivial depth half)
    (initial_environment observation nontrivial depth half) 0).trans
      (E.active (initial_environment observation nontrivial depth half))

theorem actual_born_environment : E.At
    (Shared.nextBorn (selected observation nontrivial depth half) (configuration observation nontrivial half))
    (constantEnvironment (((action observation nontrivial half) ^ count observation)
      (receipt observation nontrivial depth half).2.2.1)) := by
  have all : E.At (selected observation nontrivial depth half)
      (selected observation nontrivial depth half).activeEnvironment :=
    SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.frames_constant
      (configuration observation nontrivial half) (initial_environment observation nontrivial depth half)
      (0 + (Complete.receipt (configuration observation nontrivial half) (frame observation nontrivial depth half) 0).1)
  have same := (E.epoch all).trans (selected_environment observation nontrivial depth half)
  have generated : E.At
      (Shared.nextBorn (selected observation nontrivial depth half) (configuration observation nontrivial half))
      (constantEnvironment (((action observation nontrivial half) ^ count observation)
        ((A.epoch (selected observation nontrivial depth half)).activeEnvironment () ()))) :=
    born_environment observation nontrivial half (selected observation nontrivial depth half)
  intro current occurrence
  have literal := generated (current := current) occurrence
  rw [same] at literal
  exact literal

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombReceiptFeedback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
