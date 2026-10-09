import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKReceiptFeedback

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombPhysicalAction
open Complex MeasureTheory Set
open NoIslandNoMagic.CanonicalRiemann
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open scoped InnerProductSpace
noncomputable section
namespace C
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombReceiptFeedback
  (Value Var Frame receipt frame initial_environment nextEnvironment constantEnvironment)
end C
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (base actualVisit actualOccurrence datum resultFace frames nextBorn)
end S
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory (programme lowResult)
end I
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment
  (At active epoch frames_constant born_raw)
end E
namespace Complete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion
  (receipt atReceipt receipt_next receipt_compiles)
end Complete
namespace OF
export RootGeneratedDebtActivationJointSource.OwnerFree (raw action law nextState targetOf inputNext nextState_input)
end OF

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (depth : Nat) (half : OriginalKCombCalculation.Half observation)

def value : BurnolL2 := (C.receipt observation nontrivial depth half).2.2.1
abbrev R := _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombReceiptFeedback.action observation nontrivial half
abbrev initial := C.frame observation nontrivial depth half
def physicalProjection : BurnolL2 →L[ℂ] BurnolL2 := burnolEvenAmbientProjectionEndomorphism
def physicalRemainder : BurnolL2 →L[ℂ] BurnolL2 :=
  (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ.starProjection

-- The existing pair carrier retains the one R result until its paid split.
def RPair : (BurnolL2 × BurnolL2) →L[ℂ] (BurnolL2 × BurnolL2) :=
  ((R observation nontrivial half).comp (ContinuousLinearMap.fst ℂ BurnolL2 BurnolL2)).prod 0

def splitPair : (BurnolL2 × BurnolL2) →L[ℂ] (BurnolL2 × BurnolL2) :=
  (physicalProjection.comp (ContinuousLinearMap.fst ℂ BurnolL2 BurnolL2)).prod
    (physicalRemainder.comp (ContinuousLinearMap.fst ℂ BurnolL2 BurnolL2))

def code : Expr (PairValue C.Value) C.Var () :=
  .linear (s := ()) (t := ()) splitPair.toLinearMap.toAddMonoidHom
    (.linear (s := ()) (t := ()) (RPair observation nontrivial half).toLinearMap.toAddMonoidHom (.var (s := ()) ()))

def raw (current : C.Frame) : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value := PairValue C.Value) (Var := C.Var) (sort := ()) :=
  ⟨fun _ _ => (current.activeEnvironment () (), 0), code observation nontrivial half⟩

def result (current : C.Frame) := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
  (S.base current).root.toAuthoritativeRoot
  (fun {_current} _occurrence => raw observation nontrivial half (A.epoch current))
  (S.actualOccurrence current)

def lowProgramme : A.Programme (PhysicalValue := C.Value) (PhysicalVar := C.Var) (sort := ()) where
  LowVar := C.Var
  datum current := {
    component := none
    reader := fun {_current} _occurrence => raw observation nontrivial half current
    nextEnvironmentReadAt := some (fun {_current} _occurrence paid => C.constantEnvironment paid.1) }
  nextInventory := (_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombReceiptFeedback.lowProgramme observation nontrivial half).nextInventory
  nextPairInventory current := some (match current.pairInventory with
    | none => SourceOperationPaidRelations.exposure (result observation nontrivial half current).2.1.2
    | some prior => SourceHistoryCommon.seed prior
        (SourceOperationPaidRelations.exposure (result observation nontrivial half current).2.1.2))

def configuration : A.Programme (PhysicalValue := C.Value) (PhysicalVar := C.Var) (sort := ()) :=
  I.programme (lowProgramme observation nontrivial half)

theorem result_value (current : C.Frame) : (result observation nontrivial half current).2.2.1 =
    (physicalProjection ((R observation nontrivial half) ((A.epoch current).activeEnvironment () ())),
      physicalRemainder ((R observation nontrivial half) ((A.epoch current).activeEnvironment () ()))) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (S.base current).root.toAuthoritativeRoot
    (fun {_current} _occurrence => raw observation nontrivial half (A.epoch current))
    (S.actualOccurrence current)).trans rfl

theorem complete_raw (current : C.Frame) :
    (result observation nontrivial half current).2.2.1.1 +
      (result observation nontrivial half current).2.2.1.2 =
        (R observation nontrivial half) ((A.epoch current).activeEnvironment () ()) := by
  rw [result_value]
  change (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection _ +
    (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ.starProjection _ = _
  exact Submodule.starProjection_add_starProjection_orthogonal _

theorem result_trace (current : C.Frame) : (result observation nontrivial half current).2.1.2.length = 3 :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history
    (S.base current).root.toAuthoritativeRoot
    (fun {_current} _occurrence => raw observation nontrivial half (A.epoch current))
    (S.actualOccurrence current)).trans rfl

def sourceState (current : C.Frame) (count : Nat) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Completion.state
    (S.base current).root.toAuthoritativeRoot (S.actualVisit current).current
    (fun _ => raw observation nontrivial half (A.epoch current)) count

theorem paid_R_state (current : C.Frame) : (sourceState observation nontrivial half current 2).1 =
    .linear (s := ()) (t := ()) splitPair.toLinearMap.toAddMonoidHom
      (.const (s := ()) ((R observation nontrivial half) ((A.epoch current).activeEnvironment () ()), (0 : BurnolL2))) := by
  let input := raw observation nontrivial half (A.epoch current)
  have zero : sourceState observation nontrivial half current 0 =
      SourceOperationExecutionDebt.initial input.environment input.expression :=
    RootGeneratedDebtActivationJointSource.OwnerFree.Completion.initial_state
      (S.base current).root.toAuthoritativeRoot (S.actualVisit current).current (fun _ => input)
  have one : sourceState observation nontrivial half current 1 =
      OF.inputNext input (SourceOperationExecutionDebt.initial input.environment input.expression) :=
    (RootGeneratedDebtActivationJointSource.OwnerFree.Completion.next_state
      (S.base current).root.toAuthoritativeRoot (S.actualVisit current).current (fun _ => input) 0).trans
      ((RootGeneratedDebtActivationJointSource.OwnerFree.nextState_input
        (S.base current).root.toAuthoritativeRoot (S.actualVisit current).current input
        (sourceState observation nontrivial half current 0)).trans (congrArg (OF.inputNext input) zero))
  have two : sourceState observation nontrivial half current 2 =
      OF.inputNext input (OF.inputNext input
        (SourceOperationExecutionDebt.initial input.environment input.expression)) :=
    (RootGeneratedDebtActivationJointSource.OwnerFree.Completion.next_state
      (S.base current).root.toAuthoritativeRoot (S.actualVisit current).current (fun _ => input) 1).trans
      ((RootGeneratedDebtActivationJointSource.OwnerFree.nextState_input
        (S.base current).root.toAuthoritativeRoot (S.actualVisit current).current input
        (sourceState observation nontrivial half current 1)).trans (congrArg (OF.inputNext input) one))
  exact (congrArg Sigma.fst two).trans rfl

private theorem R_unsettled (current : C.Frame)
    (settled : SourceOperationExecutionDebt.Settlement (sourceState observation nontrivial half current 1)) : False := by
  have zero := (OF.law (S.base current).root.toAuthoritativeRoot (S.actualVisit current).current
    (fun _ => raw observation nontrivial half (A.epoch current))).settlement_budget_zero settled
  have positive := RootGeneratedDebtActivationJointSource.OwnerFree.Completion.budget
    (S.base current).root.toAuthoritativeRoot (S.actualVisit current).current
    (fun _ => raw observation nontrivial half (A.epoch current)) 1
  change remaining (sourceState observation nontrivial half current 1).1 = 0 at zero
  change remaining (sourceState observation nontrivial half current 1).1 = 3 - 1 at positive
  omega

def RReceipt (current : C.Frame) := match OF.action
    (S.base current).root.toAuthoritativeRoot (S.actualVisit current).current
    (fun _ => raw observation nontrivial half (A.epoch current))
    (sourceState observation nontrivial half current 1) with
  | .inl settled => False.elim (R_unsettled observation nontrivial half current settled)
  | .inr paid => paid

theorem RReceipt_action (current : C.Frame) : OF.action
    (S.base current).root.toAuthoritativeRoot (S.actualVisit current).current
    (fun _ => raw observation nontrivial half (A.epoch current))
    (sourceState observation nontrivial half current 1) = .inr (RReceipt observation nontrivial half current) := by
  cases chosen : OF.action (S.base current).root.toAuthoritativeRoot (S.actualVisit current).current
    (fun _ => raw observation nontrivial half (A.epoch current))
    (sourceState observation nontrivial half current 1) with
  | inl settled => exact False.elim (R_unsettled observation nontrivial half current settled)
  | inr paid => simp only [RReceipt, chosen]

theorem RReceipt_target (current : C.Frame) : (RReceipt observation nontrivial half current).1 =
    sourceState observation nontrivial half current 2 := by
  have next := RootGeneratedDebtActivationJointSource.OwnerFree.Completion.next_state
    (S.base current).root.toAuthoritativeRoot (S.actualVisit current).current
    (fun _ => raw observation nontrivial half (A.epoch current)) 1
  change sourceState observation nontrivial half current 2 = OF.nextState _ _ _
    (sourceState observation nontrivial half current 1) at next
  unfold RootGeneratedDebtActivationJointSource.OwnerFree.nextState
    RootGeneratedDebtActivationJointSource.OwnerFree.targetOf at next
  rw [RReceipt_action] at next
  exact next.symm

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombPhysicalAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
