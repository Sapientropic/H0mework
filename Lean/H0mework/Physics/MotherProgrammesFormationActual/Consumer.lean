import H0mework.Physics.MotherProgrammesFormationActual.Joint

set_option autoImplicit false
set_option synthInstance.maxSize 4096

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ActualFormation

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open CofinalHistorySettlement CofinalHistorySettlementFace
open SourceGeneratedIntegralCoherentJointAction
open Stage9C.Revision StageNineHolonomicField StageNineEnrichedProofFreeSource ClockBFFeedback
open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction
open StageNineDiracDualFormNativeMotherAction

noncomputable section

def linearizeEvent : PresentedRelationEventAt Generator → IntegralCarrier
  | .generator generator => event generator
  | .relation relation => relation

/-- Both the complete event tree and the computed common state are read
from one already generated occurrence. Relation labels remain explicit. -/
def commonOccurrence {current : SpinPair.Current}
    (occurrence : SpinPair.source.toRootSource.actual.OccurrenceAt current) (step : ℕ) :=
  ((historyLaw.historyAt occurrence).observation step).map fun presented =>
    (presented, jointInput.seedLift (linearizeEvent presented))

theorem whole_history_recovered {current : SpinPair.Current}
    (occurrence : SpinPair.source.toRootSource.actual.OccurrenceAt current) (step : ℕ) :
    (commonOccurrence occurrence step).map Prod.fst =
      (historyLaw.historyAt occurrence).observation step := by
  exact (RootedAccountedUnfolding.map_map Prod.fst
    (fun presented => (presented, jointInput.seedLift (linearizeEvent presented)))
    ((historyLaw.historyAt occurrence).observation step)).trans
      (RootedAccountedUnfolding.map_id _)

theorem whole_common_state_generated {current : SpinPair.Current}
    (occurrence : SpinPair.source.toRootSource.actual.OccurrenceAt current) (step : ℕ) :
    (commonOccurrence occurrence step).map Prod.snd =
      jointInput.jointOccurrence
        (((historyLaw.historyAt occurrence).observation step).map linearizeEvent) := by
  exact (RootedAccountedUnfolding.map_map Prod.snd
    (fun presented => (presented, jointInput.seedLift (linearizeEvent presented)))
    ((historyLaw.historyAt occurrence).observation step)).trans
      (RootedAccountedUnfolding.map_map jointInput.seedLift linearizeEvent
        ((historyLaw.historyAt occurrence).observation step)).symm

theorem source_common_incidence_nonzero :
    jointInput.incidenceResidual (event (0, .running sourcePrepared)) ≠ 0 := by
  intro zero
  have measured : jointInput.measurementFace
      (jointInput.incidenceResidual (event (0, .running sourcePrepared))) = 0 :=
    (congrArg jointInput.measurementFace zero).trans (map_zero _)
  have gravity := congrArg (fun value : ActualCoordinates => value.1.2.2.1 0 3 0) measured
  exact (ne_of_gt (div_pos Stage9C.Material.SpinPair.lapse_pos (by norm_num)))
    (source_incidence_gravity.symm.trans gravity)

set_option maxHeartbeats 2000000 in
/-- The source-only instance ties the complete common occurrence to the
original physical writer, complete ledger and next at every finite step. -/
theorem source_common_consumed (step : ℕ) (chart : StageNineChart) (point : BasePoint) :
    let before := NativeFamily.stateAt sourcePrepared step
    let after := NativeFamily.stateAt sourcePrepared (step + 1)
    let occurrence := NativeFamily.occurrenceAt sourcePrepared step
    let successor := NativeFamily.successorAt sourcePrepared step
    let generator : Generator := (step, .running before)
    let next : Generator := (step + 1, .running after)
    (commonOccurrence (SpinPair.emitted (.running sourcePrepared)) step).map Prod.fst =
      (historyLaw.historyAt (SpinPair.emitted (.running sourcePrepared))).observation step ∧
    ((historyLaw.historyAt (SpinPair.emitted (.running sourcePrepared))).observation step).frontier =
      [.generator generator] ∧
    SpinPair.source.toRootSource.actual.compile occurrence =
      .nativeWrite (materialActionAt (SpinPair.underlying (.running before))) ∧
    successor.ledgerEvolution = (SpinPair.generatedPatch occurrence).toLedgerWriteEvolution ∧
    successor.targetCurrent = (NativeFamily.visitAt sourcePrepared (step + 1)).current ∧
    jointEvent next = jointInput.omega (jointEvent generator) -
      jointInput.incidenceResidual (event generator) ∧
    wholeCoordinates.symm (jointInput.measurementFace (jointEvent next)).1 =
      Recognition.wholeField successor.targetCurrent ∧
    (jointInput.measurementFace (jointEvent next)).2 chart point =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity ClockBF.motherSource chart point
        (toContinuumPointField (Recognition.wholeField successor.targetCurrent) point) := by
  dsimp only
  obtain ⟨compiled, next, _, _⟩ := NativeFamily.next_consumed sourcePrepared step
  have target : Recognition.wholeField (NativeFamily.successorAt sourcePrepared step).targetCurrent =
      (NativeFamily.stateAt sourcePrepared (step + 1)).current := by
    rw [next]
    rfl
  refine ⟨whole_history_recovered _ _, ?_, compiled,
    NativeFamily.complete_patch_consumed _ _, next,
    actual_joint_next (step, .running (NativeFamily.stateAt sourcePrepared step)), ?_, ?_⟩
  · rw [frontier_generated, generated_native_family]
  · rw [complete_field_read, target]
    rfl
  · change (fieldRead (event (step + 1, .running (NativeFamily.stateAt sourcePrepared (step + 1))))).2
      chart point = _
    rw [fieldRead_event, target]
    rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ActualFormation
