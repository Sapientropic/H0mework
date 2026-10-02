import H0mework.Versions.R2.Realization.Faces.ProjectionCoface
import H0mework.Versions.R2.Arithmetic.UnitArithmetic.Root
import H0mework.Versions.R2.Arithmetic.FockDynamics.OperationDerivation
import H0mework.Versions.R2.Realization.Operations.NativeState

/-!
# Canonical particle--wave Fock root runtime

The canonical unit-arithmetic occurrence exposes its exact source and target
prime fields, their second-quantized Fock states, and the induced joint
measurement/coimage equation.  The component is installed before each root
tick by a projection coface; the underlying occurrence, compiler, whole
ledger, law surface and generated next remain those of the fixed canonical
root.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFockRuntime

open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateRealization
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticRoot
open ParticleWaveFock
open ArithmeticGeneration

noncomputable section

abbrev BaseAuthoritySource :=
  CanonicalUnitArithmeticRoot.livingRoot.toAuthoritativeRoot.source

abbrev BaseLedgerSource :=
  BaseAuthoritySource.restructuringSource.toLedgerSource

def scanIndex (current : Current) : Nat :=
  current.cardinalShadow

@[simp] theorem scanIndex_next (current : Current) :
    scanIndex (CanonicalUnitArithmeticRoot.next current) =
      scanIndex current + 1 :=
  rfl

theorem factorizationRuntimeAt_current (depth : Nat) :
    (CanonicalUnitArithmeticFactorizationOccurrence.runtimeAt depth
      ).current.visit.current = UnitHistory.generate (depth + 1) := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change CanonicalUnitArithmeticRoot.next
          (CanonicalUnitArithmeticFactorizationOccurrence.runtimeAt depth
            ).current.visit.current =
        UnitHistory.generate (depth + 1 + 1)
      rw [inductionHypothesis]
      rfl

/-- Reconstruct the exact runtime owner from the emitted current itself.
At reachable nonempty currents this owner lives at that very current, rather
than reusing the stage-zero owner as a scalar shadow. -/
def liveGlobalOwner (current : Current) : GlobalParentOwner :=
  let authority :=
    CanonicalUnitArithmeticFactorizationOccurrence.runtimeAuthorityAt
      (scanIndex current - 1)
  (⟨authority, GeneratedUnitFactorizationAt.generate
      (CanonicalUnitArithmeticFactorizationOccurrence.authorityWholeHistory
        authority)⟩,
    GeneratedGlobalDeterminantCoordinateGerm.generate)

theorem liveGlobalOwner_current
    (current : Current) (active : 1 ≤ scanIndex current) :
    (liveGlobalOwner current).1.1.1.current.visit.current = current := by
  change
    (CanonicalUnitArithmeticFactorizationOccurrence.runtimeAt
      (scanIndex current - 1)).current.visit.current = current
  rw [factorizationRuntimeAt_current]
  apply UnitHistory.eq_of_cardinalShadow_eq
  rw [UnitHistory.cardinalShadow_generate]
  unfold scanIndex at active ⊢
  omega

theorem canonicalOccurrence_unique
    {current : Current}
    (left right :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current) :
    left = right := by
  rcases left with ⟨leftSupport, leftEvent⟩
  rcases right with ⟨rightSupport, rightEvent⟩
  rcases leftEvent with ⟨leftEq, leftTrace, leftTraceEq⟩
  rcases rightEvent with ⟨rightEq, rightTrace, rightTraceEq⟩
  cases leftEq
  cases rightEq
  cases leftTraceEq
  cases rightTraceEq
  rfl

theorem canonicalOccurrence_heq
    {leftCurrent rightCurrent : Current}
    (current_eq : leftCurrent = rightCurrent)
    (left :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt leftCurrent)
    (right :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt rightCurrent) :
    HEq left right := by
  subst rightCurrent
  exact heq_of_eq (canonicalOccurrence_unique left right)

theorem liveGlobalOwner_occurrence
    (current : Current)
    (occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current)
    (active : 1 ≤ scanIndex current) :
    HEq (liveGlobalOwner current).1.1.1.emittedOccurrence occurrence :=
  canonicalOccurrence_heq (liveGlobalOwner_current current active)
    (liveGlobalOwner current).1.1.1.emittedOccurrence occurrence

def sourceFieldAt (current : Current) : IntegralOneParticle :=
  ownerPrimeField (liveGlobalOwner current) (scanIndex current)

def targetFieldAt (current : Current) : IntegralOneParticle :=
  ownerPrimeField
    (liveGlobalOwner (CanonicalUnitArithmeticRoot.next current))
    (scanIndex (CanonicalUnitArithmeticRoot.next current))

def sourceStateAt (current : Current) : ParentCarrier :=
  secondQuantizedState (sourceFieldAt current)

def targetStateAt (current : Current) : ParentCarrier :=
  secondQuantizedState (targetFieldAt current)

def forcedTraceAt (current : Current) : ParentCarrier :=
  secondQuantizedEffect (sourceFieldAt current)
    (targetFieldAt current - sourceFieldAt current)

/-- Evaluate the source-fixed symbolic operation at this native write only. -/
def operationValuesAt (current : Current) : List ParentCarrier :=
  evaluateOperationTrace (sourceFieldAt current)
    (sourceFieldAt (CanonicalUnitArithmeticRoot.nativeWriteAt current).target -
      sourceFieldAt current)

theorem operationValuesAt_sum (current : Current) :
    (operationValuesAt current).sum = forcedTraceAt current :=
  evaluateOperationTrace_sum _ _

theorem targetState_eq_source_add_operationValues (current : Current) :
    targetStateAt current = sourceStateAt current + (operationValuesAt current).sum :=
  OperationDerivations.source_update _ _ (OperationDerivations.generatedProof _ _)

theorem targetState_eq_source_add_forcedTrace (current : Current) :
    targetStateAt current = sourceStateAt current + forcedTraceAt current :=
  secondQuantizedState_update _ _

theorem jointMeasurement_target_eq_source_add_forcedTrace
    (current : Current) :
    jointMeasurement (targetStateAt current) =
      jointMeasurement (sourceStateAt current) +
        jointMeasurement (forcedTraceAt current) :=
  jointMeasurement_secondQuantizedState_update _ _

theorem jointCoimage_target_eq_source_add_forcedTrace
    (current : Current) :
    jointMeasurementCoimage (targetStateAt current) =
      jointMeasurementCoimage (sourceStateAt current) +
        jointMeasurementCoimage (forcedTraceAt current) :=
  jointCoimage_secondQuantizedState_update _ _

set_option maxHeartbeats 800000 in
/-- One source-fixed update payload.  Its three equations are projections of
the canonical native write into the common Fock state and joint measurement,
not freely submitted effect laws. -/
structure RootGeneratedParticleWaveCurrentAt
    (current : Current)
    (occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current)
    (_active : 1 ≤ scanIndex current) : Type where
  private mk ::
  sourceOccurrence :
    BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current
  sourceOccurrence_eq : sourceOccurrence = occurrence
  nativeWrite : NativeWriteAt current
  nativeWrite_eq : nativeWrite = CanonicalUnitArithmeticRoot.nativeWriteAt current
  nativeWrite_source : nativeWrite = occurrence.2.write
  nativeRuntimeAction : SourceOperationNative.Carrier CanonicalUnitArithmeticRoot.process →ₗ[ℤ]
    SourceOperationNative.Carrier CanonicalUnitArithmeticRoot.process
  nativeRuntimeAction_eq : nativeRuntimeAction =
    SourceOperationNative.sourceAction CanonicalUnitArithmeticRoot.process
  nativeRuntimeAction_target :
    nativeRuntimeAction
      (SourceOperationNative.statePoint CanonicalUnitArithmeticRoot.process (scanIndex current - 1)) =
    SourceOperationNative.statePoint CanonicalUnitArithmeticRoot.process (scanIndex nativeWrite.target - 1)
  sourceOwnerCurrent :
    (liveGlobalOwner current).1.1.1.current.visit.current = current
  sourceOwnerOccurrence :
    HEq (liveGlobalOwner current).1.1.1.emittedOccurrence occurrence
  targetOwnerCurrent :
    (liveGlobalOwner (CanonicalUnitArithmeticRoot.next current)
      ).1.1.1.current.visit.current =
        CanonicalUnitArithmeticRoot.next current
  targetOwnerOccurrence :
    HEq
      (liveGlobalOwner (CanonicalUnitArithmeticRoot.next current)
        ).1.1.1.emittedOccurrence
      (CanonicalUnitArithmeticRoot.emitted
        (CanonicalUnitArithmeticRoot.next current))
  operationTrace : List OperationEffectTerm
  operationTrace_eq : operationTrace = operationEffectTrace
  operationValues : List ParentCarrier
  operationValues_eq : operationValues = evaluateEffectTerms operationTrace
    (sourceFieldAt current) (sourceFieldAt nativeWrite.target - sourceFieldAt current)
  operationRelation : OperationRelations.InventoryCarrier
    (sourceFieldAt current) (sourceFieldAt nativeWrite.target - sourceFieldAt current)
  operationRelation_eq : operationRelation = OperationRelations.generatedInventory
    (sourceFieldAt current) (sourceFieldAt nativeWrite.target - sourceFieldAt current)
  operationDerivation : OperationDerivations.OperationProof
    (sourceFieldAt current) (sourceFieldAt nativeWrite.target - sourceFieldAt current)
  sourceState : ParentCarrier
  sourceState_eq : sourceState = sourceStateAt current
  targetState : ParentCarrier
  targetState_eq : targetState = targetStateAt current
  forcedTrace : ParentCarrier
  forcedTrace_eq : forcedTrace = forcedTraceAt current
  forcedTrace_sum : forcedTrace = operationValues.sum
  stateUpdate : targetState = sourceState + forcedTrace
  measurementUpdate :
    jointMeasurement targetState =
      jointMeasurement sourceState + jointMeasurement forcedTrace
  coimageUpdate :
    jointMeasurementCoimage targetState =
      jointMeasurementCoimage sourceState +
        jointMeasurementCoimage forcedTrace
  targetFibre : JointMeasurementFibreAt (jointMeasurement targetState)
  targetFibre_eq : targetFibre.1 = targetState
  inverseFibreLaw : ∀ alternative : ParentCarrier,
    jointMeasurement alternative = jointMeasurement targetState ↔
      alternative - targetState ∈ JointMeasurementKernel

def generateParticleWaveCurrent
    (current : Current)
    (occurrence :
      BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current)
    (active : 1 ≤ scanIndex current) :
    RootGeneratedParticleWaveCurrentAt current occurrence active :=
  { sourceOccurrence := occurrence
    sourceOccurrence_eq := rfl
    nativeWrite := CanonicalUnitArithmeticRoot.nativeWriteAt current
    nativeWrite_eq := rfl
    nativeWrite_source := (occurrence.2.write_eq_nativeWriteAt).symm
    nativeRuntimeAction := SourceOperationNative.sourceAction CanonicalUnitArithmeticRoot.process
    nativeRuntimeAction_eq := rfl
    nativeRuntimeAction_target := by
      rw [SourceOperationNative.sourceAction_statePoint]
      apply congrArg (SourceOperationNative.statePoint CanonicalUnitArithmeticRoot.process)
      change scanIndex current - 1 + 1 = scanIndex (CanonicalUnitArithmeticRoot.next current) - 1
      rw [scanIndex_next]
      omega
    sourceOwnerCurrent := liveGlobalOwner_current current active
    sourceOwnerOccurrence :=
      liveGlobalOwner_occurrence current occurrence active
    targetOwnerCurrent := liveGlobalOwner_current
      (CanonicalUnitArithmeticRoot.next current) (by
        rw [scanIndex_next]
        omega)
    targetOwnerOccurrence := liveGlobalOwner_occurrence
      (CanonicalUnitArithmeticRoot.next current)
      (CanonicalUnitArithmeticRoot.emitted
        (CanonicalUnitArithmeticRoot.next current)) (by
          rw [scanIndex_next]
          omega)
    operationTrace := operationEffectTrace
    operationTrace_eq := rfl
    operationValues := operationValuesAt current
    operationValues_eq := rfl
    operationRelation := OperationRelations.generatedInventory (sourceFieldAt current)
      (sourceFieldAt (CanonicalUnitArithmeticRoot.nativeWriteAt current).target -
        sourceFieldAt current)
    operationRelation_eq := rfl
    operationDerivation := OperationDerivations.generatedProof (sourceFieldAt current)
      (sourceFieldAt (CanonicalUnitArithmeticRoot.nativeWriteAt current).target -
        sourceFieldAt current)
    sourceState := sourceStateAt current
    sourceState_eq := rfl
    targetState := targetStateAt current
    targetState_eq := rfl
    forcedTrace := (operationValuesAt current).sum
    forcedTrace_eq := operationValuesAt_sum current
    forcedTrace_sum := rfl
    stateUpdate := targetState_eq_source_add_operationValues current
    measurementUpdate := by
      simpa only [map_add] using congrArg jointMeasurement
        (targetState_eq_source_add_operationValues current)
    coimageUpdate := by
      simpa only [map_add] using congrArg jointMeasurementCoimage
        (targetState_eq_source_add_operationValues current)
    targetFibre := measuredStateFibre (targetStateAt current)
    targetFibre_eq := rfl
    inverseFibreLaw := fun alternative =>
      jointMeasurement_eq_iff_sub_mem_kernel alternative
        (targetStateAt current) }

/-- The empty history is the only inactive presentation.  Every reachable
canonical runtime current is active. -/
def projectionLaw : SourceNativeProjectionLaw BaseLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {current} _occurrence => PLift (1 ≤ scanIndex current)
  InactiveAt := fun _ {current} _occurrence => PLift (scanIndex current = 0)
  classify := by
    intro _ current _occurrence
    cases current with
    | empty => exact .inr ⟨rfl⟩
    | next prior =>
        exact .inl ⟨by
          unfold scanIndex UnitHistory.cardinalShadow
          omega⟩
  PayloadAt := fun _ {current} occurrence active =>
    RootGeneratedParticleWaveCurrentAt current occurrence active.down
  project := fun _ {current} occurrence active =>
    generateParticleWaveCurrent current occurrence active.down

def authoritySource : SourceNativeAuthoritySource N V :=
  BaseAuthoritySource.withProjectionCoface projectionLaw

def installation : SourceNativeProjectionLaw.InstallationAt
    projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    BaseAuthoritySource projectionLaw

def baseInstallation : SourceNativeProjectionLaw.InstallationAt
    BaseAuthoritySource.projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    BaseAuthoritySource projectionLaw

def authoritativeRoot : SourceNativeAuthoritativeRootClosure N V where
  source := authoritySource
  emitted := CanonicalUnitArithmeticRoot.emitted
  compiler_commutes :=
    CanonicalUnitArithmeticRoot.authoritativeRoot.compiler_commutes

def livingRoot : SourceNativeLivingRootClosure N V :=
  authoritativeRoot.toLivingWithoutFaithfulTerminal <| fun _ =>
    ⟨fun terminal => nomatch terminal⟩

def finiteVisit := CanonicalUnitArithmeticRoot.finiteVisit

def temporalVisit (depth : Nat) :
    SourceNativeTemporalVisitAt authoritativeRoot.toLedgerRoot :=
  .finite (finiteVisit depth)

def temporalDepth?
    (current : SourceNativeLivingRootCurrentAt N) : Option Nat :=
  match current.visit.history with
  | .finite history => some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

theorem temporalVisit_depth (depth : Nat) :
    temporalDepth? ⟨V, livingRoot, temporalVisit depth⟩ = some depth :=
  CanonicalUnitArithmeticRoot.temporalVisit_depth depth

abbrev process : SourceNativeLivingRootProcess N where
  State := Nat
  stateAt := fun depth => ⟨V, livingRoot, temporalVisit depth⟩
  stateAt_injective := by
    intro left right equality
    have depthEquality := congrArg temporalDepth? equality
    rw [temporalVisit_depth left, temporalVisit_depth right] at depthEquality
    exact Option.some.inj depthEquality
  initial := 0
  successorAt := fun depth => ⟨depth + 1, rfl, by rfl⟩

inductive FaceAt
  | particleWave
  deriving DecidableEq

abbrev runtimeFacade : SourceNativeLivingRuntimeFacade N where
  process := process
  FaceAt := fun _runtime => FaceAt
  componentAt := fun _runtime _face => projectionLaw
  installationAt := fun _runtime _face => installation
  projectionAt := fun _runtime _face => PUnit.unit

def runtimeSeed : LivingRuntimeState runtimeFacade.process :=
  runtimeFacade.seed

def runtimeAt (depth : Nat) : LivingRuntimeState runtimeFacade.process :=
  runtimeSeed.advance depth

theorem finiteVisit_current (depth : Nat) :
    (finiteVisit depth).current = UnitHistory.generate (depth + 1) := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change CanonicalUnitArithmeticRoot.next (finiteVisit depth).current =
        UnitHistory.generate (depth + 1 + 1)
      rw [inductionHypothesis]
      rfl

theorem runtimeAt_state (depth : Nat) :
    (runtimeAt depth).state = depth := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change (runtimeAt depth).state + 1 = depth + 1
      exact congrArg (fun value : Nat => value + 1) inductionHypothesis

theorem runtimeAt_current (depth : Nat) :
    (runtimeAt depth).current.visit.current =
      UnitHistory.generate (depth + 1) := by
  change (finiteVisit (runtimeAt depth).state).current = _
  rw [runtimeAt_state, finiteVisit_current]

theorem runtimeAt_scanIndex (depth : Nat) :
    scanIndex (runtimeAt depth).current.visit.current = depth + 1 := by
  rw [runtimeAt_current]
  exact UnitHistory.cardinalShadow_generate (depth + 1)

def runtimeActive (depth : Nat) :
    projectionLaw.ActiveAt PUnit.unit
      (runtimeAt depth).emittedOccurrence :=
  ⟨by rw [runtimeAt_scanIndex]; omega⟩

def runtimePayload (depth : Nat) :
    RootGeneratedParticleWaveCurrentAt
      (runtimeAt depth).current.visit.current
      (runtimeAt depth).emittedOccurrence
      (runtimeActive depth).down :=
  projectionLaw.project PUnit.unit
    (runtimeAt depth).emittedOccurrence (runtimeActive depth)

theorem runtimeReadout_is_particleWave (depth : Nat) :
    runtimeFacade.readoutAt (runtimeAt depth) .particleWave =
      .inl ⟨runtimeActive depth, runtimePayload depth⟩ := by
  change projectionLaw.outcomeAt PUnit.unit
      (runtimeAt depth).emittedOccurrence = _
  unfold SourceNativeProjectionLaw.outcomeAt
  generalize classifierEq :
    projectionLaw.classify PUnit.unit
      (runtimeAt depth).emittedOccurrence = classification
  cases classification with
  | inl active =>
      have activeEq : active = runtimeActive depth := by
        apply PLift.down_injective
        exact Subsingleton.elim _ _
      cases activeEq
      rfl
  | inr inactive =>
      have impossible := inactive.down
      rw [runtimeAt_scanIndex] at impossible
      omega

theorem coversAt_factorizes
    (runtime : LivingRuntimeState runtimeFacade.process)
    (face : runtimeFacade.FaceAt runtime) :
    runtimeFacade.process.toAnswerNextCausalWorld.emitted
          (ULift.up runtime.state) = ULift.up runtime.tick.generated ∧
      runtime.tick.generated.occurrence =
        runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          runtime.current.visit.current ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          runtime.current.visit.current) ∧
      HEq (runtimeFacade.readoutAt runtime face)
        (runtime.tick.generated.projectionOutcome
          ((runtimeFacade.installationAt runtime face).embed
            (runtimeFacade.projectionAt runtime face))) ∧
      runtime.tick.nextCurrent =
        runtimeFacade.process.stateAt
          (runtimeFacade.process.successor runtime.state) :=
  runtimeFacade.readoutAt_factorizes runtime face

/-- The original Fock face reads its native target from the emitted unit
action, then spends that target in the state equation and the same tick. -/
theorem runtimeSourceAction_fockLedgerNext (depth : Nat) :
    (runtimePayload depth).nativeWrite.target =
        nativeActionTarget
          (runtimeAt depth).emittedOccurrence.2.actionTrace ∧
      (runtimePayload depth).targetState =
        (runtimePayload depth).sourceState +
          (runtimePayload depth).forcedTrace ∧
      HEq (runtimeAt depth).tick.generated.wholeLedgerWriteBack
        ((runtimeAt depth).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (runtimeAt depth).current.visit.current) ∧
      (runtimeAt depth).tick.nextCurrent =
        runtimeFacade.process.stateAt
          (runtimeFacade.process.successor (runtimeAt depth).state) := by
  obtain ⟨_, _, ledger, _, next⟩ :=
    coversAt_factorizes (runtimeAt depth) .particleWave
  refine ⟨?_, (runtimePayload depth).stateUpdate, ledger, next⟩
  rw [(runtimePayload depth).nativeWrite_source]
  exact (runtimeAt depth).emittedOccurrence.2.write.target_action_eq

end


end ParticleWaveFockRuntime
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
