import H0mework.Versions.R2.Physics.MotherProgrammesFormationActual.Consumer

set_option autoImplicit false
set_option synthInstance.maxSize 4096

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ActualFormation.Transition

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedIntegralCoherentJointAction
open CofinalHistorySettlement CofinalHistorySettlementFace
open Stage9C.Revision StageNineHolonomicField StageNineEnrichedProofFreeSource
open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction
open StageNineDiracDualFormNativeMotherAction ClockBFFeedback

noncomputable section

/-- The actual incidence is a linear calculation from the five existing maps. -/
def incidence : IntegralCarrier →ₗ[ℤ] jointInput.Carrier :=
  jointInput.omega.comp jointInput.seedLift - jointInput.seedLift.comp nativeAction

theorem incidence_apply (value : IntegralCarrier) :
    incidence value = jointInput.incidenceResidual value := rfl

def remainder : jointInput.Carrier →ₗ[ℤ] jointInput.Carrier :=
  LinearMap.id - jointInput.seedLift.comp jointInput.integralFace

/-- Feedback is applied to the whole generated carrier, not supplied as a
next event. The original native action remains the integral component. -/
def nativeLift : jointInput.Carrier →ₗ[ℤ] jointInput.Carrier :=
  jointInput.omega - incidence.comp jointInput.integralFace

theorem nativeLift_seed (value : IntegralCarrier) :
    nativeLift (jointInput.seedLift value) = jointInput.seedLift (nativeAction value) := by
  change jointInput.omega (jointInput.seedLift value) -
    (jointInput.omega (jointInput.seedLift value) - jointInput.seedLift (nativeAction value)) = _
  exact sub_sub_cancel _ _

theorem nativeLift_jointEvent (generator : Generator) :
    nativeLift (jointEvent generator) = jointEvent (nextGenerator generator) := by
  exact (nativeLift_seed (event generator)).trans
    (congrArg jointInput.seedLift (nativeAction_event generator))

theorem integral_nativeLift (value : jointInput.Carrier) :
    jointInput.integralFace (nativeLift value) = nativeAction (jointInput.integralFace value) := by
  change nativeAction value.val.1 - (nativeAction value.val.1 - nativeAction value.val.1) =
    nativeAction value.val.1
  exact sub_sub_cancel _ _

/-- This identity uses the literal passive coherent/measurement actions of
jointInput. It is not asserted for a general five-map input. -/
theorem nativeLift_decomposition (value : jointInput.Carrier) :
    nativeLift value =
      jointInput.seedLift (nativeAction (jointInput.integralFace value)) + remainder value := by
  apply Subtype.ext
  apply Prod.ext
  · change nativeAction value.val.1 - (nativeAction value.val.1 - nativeAction value.val.1) =
      nativeAction value.val.1 + (value.val.1 - value.val.1)
    simp
  · apply Prod.ext
    · change value.val.2.1 - (matterRead value.val.1 - matterRead (nativeAction value.val.1)) =
        matterRead (nativeAction value.val.1) + (value.val.2.1 - matterRead value.val.1)
      abel
    · change value.val.2.2 - (fieldRead value.val.1 - fieldRead (nativeAction value.val.1)) =
        fieldRead (nativeAction value.val.1) + (value.val.2.2 - fieldRead value.val.1)
      abel

theorem remainder_seed (value : IntegralCarrier) : remainder (jointInput.seedLift value) = 0 := by
  change jointInput.seedLift value - jointInput.seedLift value = 0
  exact sub_self _

theorem integral_remainder (value : jointInput.Carrier) :
    jointInput.integralFace (remainder value) = 0 := by
  change value.val.1 - value.val.1 = 0
  exact sub_self _

theorem remainder_nativeLift (value : jointInput.Carrier) :
    remainder (nativeLift value) = remainder value := by
  change nativeLift value - jointInput.seedLift (jointInput.integralFace (nativeLift value)) = _
  calc
    _ = nativeLift value - jointInput.seedLift (nativeAction (jointInput.integralFace value)) :=
      congrArg (fun coordinate => nativeLift value - jointInput.seedLift coordinate)
        (integral_nativeLift value)
    _ = (jointInput.seedLift (nativeAction (jointInput.integralFace value)) + remainder value) -
        jointInput.seedLift (nativeAction (jointInput.integralFace value)) :=
      congrArg (fun full => full - jointInput.seedLift (nativeAction (jointInput.integralFace value)))
        (nativeLift_decomposition value)
    _ = remainder value := add_sub_cancel_left _ _

theorem distinct_remainders_retained {left right : jointInput.Carrier}
    (different : remainder left ≠ remainder right) : nativeLift left ≠ nativeLift right := by
  intro same
  apply different
  exact (remainder_nativeLift left).symm.trans ((congrArg remainder same).trans
    (remainder_nativeLift right))

theorem zero_integral_fixed (value : jointInput.Carrier)
    (zeroIntegral : jointInput.integralFace value = 0) : nativeLift value = value := by
  have zeroSeed := (congrArg jointInput.seedLift zeroIntegral).trans jointInput.seedLift.map_zero
  have zeroNext := (congrArg jointInput.seedLift
    ((congrArg nativeAction zeroIntegral).trans nativeAction.map_zero)).trans jointInput.seedLift.map_zero
  have rest : remainder value = value :=
    (congrArg (fun seed => value - seed) zeroSeed).trans (sub_zero value)
  exact (nativeLift_decomposition value).trans
    ((congrArg (fun seed => seed + remainder value) zeroNext).trans ((zero_add _).trans rest))

/-- The already generated nonzero feedback direction survives as an actual
fixed remainder; the new action does not erase the carrier outside its seed. -/
theorem source_feedback_retained :
    let value := incidence (event (0, .running sourcePrepared))
    nativeLift value = value ∧ value ≠ 0 := by
  refine ⟨zero_integral_fixed _ ?_, ?_⟩
  · exact jointInput.incidenceResidual_integralFace _
  · exact source_common_incidence_nonzero

/-- Each new leaf keeps its generated relation label and applies the whole
operator to its current common state. Prior nodes are retained by advance. -/
def commonContinuation (current : PresentedRelationEventAt Generator × jointInput.Carrier) :
    RootedAccountedUnfolding (PresentedRelationEventAt Generator × jointInput.Carrier) :=
  (continuation current.1).map (fun next => (next, nativeLift current.2))

private theorem continuation_commutes (presented : PresentedRelationEventAt Generator) :
    (continuation presented).map (fun next => (next, jointInput.seedLift (linearizeEvent next))) =
      commonContinuation (presented, jointInput.seedLift (linearizeEvent presented)) := by
  cases presented with
  | generator generator =>
    dsimp only [commonContinuation, continuation, RootedAccountedUnfolding.map_zero,
      linearizeEvent]
    exact congrArg (fun state => RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator (nextGenerator generator), state))
      (nativeLift_jointEvent generator).symm
  | relation relation =>
    dsimp only [commonContinuation, continuation, RootedAccountedUnfolding.map_zero,
      linearizeEvent]
    exact congrArg (fun state => RootedAccountedUnfolding.zero (PresentedRelationEventAt.relation (nativeAction relation), state))
      (nativeLift_seed relation).symm

private theorem map_advance {Left Right : Type*} (read : Left → Right)
    (next : Left → RootedAccountedUnfolding Left) (nextRead : Right → RootedAccountedUnfolding Right)
    (commutes : ∀ value, (next value).map read = nextRead (read value))
    (tree : RootedAccountedUnfolding Left) :
    (tree.advance next).map read = (tree.map read).advance nextRead :=
  RootedAccountedUnfolding.rec
    (motive_1 := fun tree => (tree.advance next).map read = (tree.map read).advance nextRead)
    (motive_2 := fun branches =>
      RootedAccountedUnfolding.mapBranches read (RootedAccountedUnfolding.advanceBranches next branches) =
      RootedAccountedUnfolding.advanceBranches nextRead (RootedAccountedUnfolding.mapBranches read branches))
    (fun value branches branchesIH => by
      cases branches with
      | nil => exact congrArg (fun subtree => RootedAccountedUnfolding.occur (read value)
          (AccountedBranches.singleton subtree)) (commutes value)
      | cons head tail => exact congrArg (RootedAccountedUnfolding.occur (read value)) branchesIH)
    rfl
    (fun _ _ headIH tailIH => AccountedList.congrArgTwo AccountedBranches.cons headIH tailIH)
    tree

theorem commonOccurrence_next {current : SpinPair.Current}
    (occurrence : SpinPair.source.toRootSource.actual.OccurrenceAt current) (step : ℕ) :
    commonOccurrence occurrence (step + 1) =
      (commonOccurrence occurrence step).advance commonContinuation := by
  exact map_advance (fun presented => (presented, jointInput.seedLift (linearizeEvent presented)))
    continuation commonContinuation continuation_commutes ((historyLaw.historyAt occurrence).observation step)

set_option maxHeartbeats 2000000 in
/-- Every finite event is now advanced by the generated whole-carrier
operator itself and consumed by the same physical writer and complete patch. -/
theorem source_transition_consumed (step : ℕ) (chart : StageNineChart) (point : BasePoint) :
    let before := NativeFamily.stateAt sourcePrepared step
    let after := NativeFamily.stateAt sourcePrepared (step + 1)
    let occurrence := NativeFamily.occurrenceAt sourcePrepared step
    let successor := NativeFamily.successorAt sourcePrepared step
    let generator : Generator := (step, .running before)
    let target := nativeLift (jointEvent generator)
    commonOccurrence (SpinPair.emitted (.running sourcePrepared)) (step + 1) =
      (commonOccurrence (SpinPair.emitted (.running sourcePrepared)) step).advance commonContinuation ∧
    occurrence = SpinPair.emitted (.running before) ∧
    SpinPair.source.toRootSource.actual.compile occurrence =
      .nativeWrite (materialActionAt (SpinPair.underlying (.running before))) ∧
    successor.ledgerEvolution = (SpinPair.generatedPatch occurrence).toLedgerWriteEvolution ∧
    successor.targetCurrent = (NativeFamily.visitAt sourcePrepared (step + 1)).current ∧
    target = jointEvent (step + 1, .running after) ∧
    jointInput.integralFace target = nativeAction (event generator) ∧
    wholeCoordinates.symm (jointInput.measurementFace target).1 =
      Recognition.wholeField successor.targetCurrent ∧
    (jointInput.measurementFace target).2 chart point =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity ClockBF.motherSource chart point
        (toContinuumPointField (Recognition.wholeField successor.targetCurrent) point) := by
  obtain ⟨_, _, compiled, patch, next, _, field, action⟩ := source_common_consumed step chart point
  have lifted := nativeLift_jointEvent (step, .running (NativeFamily.stateAt sourcePrepared step))
  exact ⟨commonOccurrence_next _ _, rfl, compiled, patch, next, lifted, integral_nativeLift _,
    (congrArg (fun state => wholeCoordinates.symm (jointInput.measurementFace state).1) lifted).trans field,
    (congrArg (fun state => (jointInput.measurementFace state).2 chart point) lifted).trans action⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ActualFormation.Transition
