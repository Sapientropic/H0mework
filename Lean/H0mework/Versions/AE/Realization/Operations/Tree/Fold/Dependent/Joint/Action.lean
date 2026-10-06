import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.Evaluator
import H0mework.Versions.AE.Realization.Perfectification.Occurrence.Temporal.History.Common.Action.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint
open SourceOperationEffects SourceOperationExecution
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
namespace T
export SourceTemporalMaterial.Action (Result actual receipt nextCode residualRaw materialRoot materialVisit)
end T
namespace D
export SourceOperationNative.Tree.Fold.Dependent (nativeTree nativeRaw nativeReader)
end D
namespace F
export SourceOperationNative.Tree.Fold (Value Var environment program program_value program_budget budget)
end F
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (successor : StepLedgerSuccessorAt (step root visit recognition))
variable (transition : GeneratedStepJointTransitionAt (step root visit recognition) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (step root visit recognition))
  (stepTargetPairingOccurrence (step root visit recognition) successor))
open RootInquiryCompletion SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceGeneratedScalarDifferentialResidual
variable (U7' : U7ProducerCalculus N) (calculus' : U7ObstructionEvolutionCalculus N U7')
namespace A
export SourceHistoryCommon.Root.Action (Plan Measured sourceExposure targetExposure actualPlan action pairing measurement evolution residual)
end A
theorem action_raw : (sourceOutcome root visit recognition successor transition alignment).2.2.2.2 =
    A.actualPlan root visit recognition successor := by
  unfold sourceOutcome
  cases tree root visit recognition successor transition alignment
  rfl
abbrev actionPacket (count : Nat) : A.Plan root visit recognition successor :=
  ((face root visit recognition successor transition alignment U7' calculus' count).rootRead.1.fold
    (constructor root visit recognition successor transition)).2.2.2.2

theorem action_packet_generated (count : Nat) : actionPacket root visit recognition successor transition alignment U7' calculus' count =
    A.actualPlan root visit recognition successor := action_raw root visit recognition successor transition alignment

def normedAction (count : Nat) : SourceHistoryCommon.Root.Action.Joint root visit recognition successor →ₗ[ℤ] SourceHistoryCommon.Root.Action.Joint root visit recognition successor :=
  (actionPacket root visit recognition successor transition alignment U7' calculus' count).source.sourceAction.carrierAction.prodMap
    (actionPacket root visit recognition successor transition alignment U7' calculus' count).target.sourceAction.carrierAction

def normedDualAction (count : Nat) : SourceHistoryCommon.Root.Action.Joint root visit recognition successor →ₗ[ℤ] SourceHistoryCommon.Root.Action.Joint root visit recognition successor :=
  (actionPacket root visit recognition successor transition alignment U7' calculus' count).source.sourceAction.dualCarrierAction.prodMap
    (actionPacket root visit recognition successor transition alignment U7' calculus' count).target.sourceAction.dualCarrierAction

def normedPairing (count : Nat) : SourceHistoryCommon.Root.Action.Joint root visit recognition successor →ₗ[ℤ] Module.Dual ℤ (SourceHistoryCommon.Root.Action.Joint root visit recognition successor) :=
  (((actionPacket root visit recognition successor transition alignment U7' calculus' count).sourcePairing).comp (LinearMap.fst ℤ _ _)).compl₂ (LinearMap.fst ℤ _ _) +
    (((actionPacket root visit recognition successor transition alignment U7' calculus' count).targetPairing).comp (LinearMap.snd ℤ _ _)).compl₂ (LinearMap.snd ℤ _ _)

def normedMeasurement (count : Nat) : SourceHistoryCommon.Root.Action.Joint root visit recognition successor →ₗ[ℤ] A.Measured H :=
  (WithLp.linearEquiv 2 ℤ (H × H)).symm.toLinearMap.comp
    ((actionPacket root visit recognition successor transition alignment U7' calculus' count).source.measurement.prodMap
      (actionPacket root visit recognition successor transition alignment U7' calculus' count).target.measurement)

def normedEvolution (count : Nat) : A.Measured H →ₗᵢ[ℂ] A.Measured H :=
  (actionPacket root visit recognition successor transition alignment U7' calculus' count).source.hilbertEvolution.withLpProdMap 2
    (actionPacket root visit recognition successor transition alignment U7' calculus' count).target.hilbertEvolution

def normedResidual (count : Nat) (value : SourceHistoryCommon.Root.Action.Joint root visit recognition successor) : A.Measured H :=
  normedEvolution root visit recognition successor transition alignment U7' calculus' count
    (normedMeasurement root visit recognition successor transition alignment U7' calculus' count value) -
  normedMeasurement root visit recognition successor transition alignment U7' calculus' count
    (normedAction root visit recognition successor transition alignment U7' calculus' count value)

def normedObservation (count : Nat) : SourceHistoryCommon.Root.Action.Joint root visit recognition successor →ₗ[ℤ]
    (commonRead root visit recognition successor transition alignment U7' calculus' count).CompletionCarrier :=
  (CofinalHistoryTransition.GeneratedTransition.completionMap (SourceHistoryCommon.Root.sourceHistory root visit recognition)
    (commonRead root visit recognition successor transition alignment U7' calculus' count)
    (commonLeft root visit recognition successor transition alignment U7' calculus' count)).coprod
  (CofinalHistoryTransition.GeneratedTransition.completionMap (SourceHistoryCommon.Root.targetHistory root visit recognition successor)
    (commonRead root visit recognition successor transition alignment U7' calculus' count)
    (commonRight root visit recognition successor transition alignment U7' calculus' count))

abbrev normedDefect (count : Nat) := SourceGeneratedObservationAction.actionDefect
  (normedAction root visit recognition successor transition alignment U7' calculus' count)
  (normedObservation root visit recognition successor transition alignment U7' calculus' count)

theorem normed_action_read (count : Nat) : normedAction root visit recognition successor transition alignment U7' calculus' count = A.action root visit recognition successor := by
  have sourceRead := congrArg (fun packet : A.Plan root visit recognition successor => packet.source)
    (action_packet_generated root visit recognition successor transition alignment U7' calculus' count)
  have targetRead := congrArg (fun packet : A.Plan root visit recognition successor => packet.target)
    (action_packet_generated root visit recognition successor transition alignment U7' calculus' count)
  unfold normedAction
  rw [sourceRead,targetRead]
  rfl

theorem normed_pairing_read (count : Nat) : normedPairing root visit recognition successor transition alignment U7' calculus' count = A.pairing root visit recognition successor := by
  have sourceRead := congrArg (fun packet : A.Plan root visit recognition successor => packet.sourcePairing)
    (action_packet_generated root visit recognition successor transition alignment U7' calculus' count)
  have targetRead := congrArg (fun packet : A.Plan root visit recognition successor => packet.targetPairing)
    (action_packet_generated root visit recognition successor transition alignment U7' calculus' count)
  unfold normedPairing
  rw [sourceRead,targetRead]
  rfl

theorem normed_measurement_read (count : Nat) : normedMeasurement root visit recognition successor transition alignment U7' calculus' count = A.measurement root visit recognition successor := by
  exact congrArg (fun packet : A.Plan root visit recognition successor =>
    (WithLp.linearEquiv 2 ℤ (H × H)).symm.toLinearMap.comp (packet.source.measurement.prodMap packet.target.measurement))
    (action_packet_generated root visit recognition successor transition alignment U7' calculus' count)

theorem normed_evolution_read (count : Nat) : normedEvolution root visit recognition successor transition alignment U7' calculus' count = A.evolution root visit recognition successor := by
  exact congrArg (fun packet : A.Plan root visit recognition successor =>
    packet.source.hilbertEvolution.withLpProdMap 2 packet.target.hilbertEvolution)
    (action_packet_generated root visit recognition successor transition alignment U7' calculus' count)

theorem normed_residual_read (count : Nat) (value : SourceHistoryCommon.Root.Action.Joint root visit recognition successor) :
    normedResidual root visit recognition successor transition alignment U7' calculus' count value = A.residual root visit recognition successor value := by
  unfold normedResidual
  rw [normed_evolution_read, normed_measurement_read, normed_action_read]
  rfl

theorem normed_residual_norm (count : Nat) (value : SourceHistoryCommon.Root.Action.Joint root visit recognition successor) :
    ‖normedResidual root visit recognition successor transition alignment U7' calculus' count value‖ ^ 2 =
      ‖(A.residual root visit recognition successor value).fst‖ ^ 2 +
        ‖(A.residual root visit recognition successor value).snd‖ ^ 2 :=
  by
  rw [normed_residual_read]
  exact SourceHistoryCommon.Root.Action.residual_norm root visit recognition successor value

def normedActionData (count : Nat) : SourceGeneratedScalarEquivariantPerfectAction.ActionData
    (normedPairing root visit recognition successor transition alignment U7' calculus' count) where
  carrierAction := normedAction root visit recognition successor transition alignment U7' calculus' count
  dualCarrierAction := normedDualAction root visit recognition successor transition alignment U7' calculus' count
  evaluation_commutes := by
    rw [normed_pairing_read, normed_action_read]
    have dualRead : normedDualAction root visit recognition successor transition alignment U7' calculus' count =
        SourceHistoryCommon.Root.Action.dualAction root visit recognition successor :=
      congrArg (fun packet : A.Plan root visit recognition successor =>
        packet.source.sourceAction.dualCarrierAction.prodMap packet.target.sourceAction.dualCarrierAction)
        (action_packet_generated root visit recognition successor transition alignment U7' calculus' count)
    rw [dualRead]
    exact (SourceHistoryCommon.Root.Action.actionData root visit recognition successor).evaluation_commutes

def normedJointData (count : Nat) : SourceGeneratedIntegralEquivariantPerfectRealization.JointActionData (H:=A.Measured H)
    (normedPairing root visit recognition successor transition alignment U7' calculus' count) where
  sourceAction := normedActionData root visit recognition successor transition alignment U7' calculus' count
  coherentEvolution := normedEvolution root visit recognition successor transition alignment U7' calculus' count

abbrev normedRealization (count : Nat) := SourceGeneratedIntegralEquivariantPerfectRealization.generate
  (normedPairing root visit recognition successor transition alignment U7' calculus' count)
  (normedMeasurement root visit recognition successor transition alignment U7' calculus' count)
  (normedJointData root visit recognition successor transition alignment U7' calculus' count)

theorem normed_perfect_action (count : Nat) : type_of%
    (normedRealization root visit recognition successor transition alignment U7' calculus' count).perfectAction.canonicalMap_commutes :=
  (normedRealization root visit recognition successor transition alignment U7' calculus' count).perfectAction.canonicalMap_commutes

theorem normed_kernel_effect (count : Nat)
    (coordinate : LinearMap.ker (normedObservation root visit recognition successor transition alignment U7' calculus' count)) :
    normedDefect root visit recognition successor transition alignment U7' calculus' count coordinate = 0 ↔
      normedObservation root visit recognition successor transition alignment U7' calculus' count
        (normedAction root visit recognition successor transition alignment U7' calculus' count coordinate) = 0 :=
  SourceGeneratedObservationAction.actionDefect_value_zero_iff _ _ coordinate
end SourceOperationNative.Tree.Fold.Dependent.Joint
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
