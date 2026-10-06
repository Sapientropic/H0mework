import H0mework.Versions.R2.Physics.Bell.Runtime
import H0mework.Versions.R2.Physics.MotherProgrammesFormationActual.Consumer
import H0mework.Realization.Operations.ObservationModel
import H0mework.Realization.Operations.Action

/-!
# Complete source history and action at the original Bell occurrence

The original visit 10 generates its complete history and joint action field.  The observer
retains the source constructor and all nine physical fields, before restricting to the Born
readout.  The existing autonomous observation model consumes the original physical action;
its complete fibre recovers native current, writer, ledger and installed projections.  The
macro reads remain tick 16 and 17.  CEM and Rabi parameter semantics are not supplied by a
callback or inferred from the static Bell probability fibre.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace SaturationMonoid.PhysicsCore.Stage10.Bell.SourceHistory

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedActionObservationHistory
open SourceGeneratedObservationAction SourceGeneratedScalarDifferentialResidual
open Stage9C.Revision StageNineHolonomicField Stage9CU.Fields
open ProofFreeRicherAnholonomicSource

noncomputable section

open SourceUniqueness

/-- Canonical successors of the exact original Bell visit, with no alternate root seed. -/
def visitAt : Nat → Recognition.Visit
  | 0 => Runtime.visit
  | stage + 1 => (visitAt stage).next rfl

def currentAt (stage : Nat) : SpinPair.Current := (visitAt stage).current

def eventAt (stage : Nat) := Recognition.generated (visitAt stage)

def generatorAt (stage : Nat) : ActualFormation.Generator := (stage, currentAt stage)

def commonAt (stage : Nat) := ActualFormation.commonOccurrence Runtime.event.occurrence stage

theorem original_visit : visitAt 0 = Runtime.visit := rfl

theorem original_event : eventAt 0 = Runtime.event := rfl

theorem current_next (stage : Nat) : currentAt (stage + 1) = SpinPair.next (currentAt stage) := rfl

theorem current_is_generated (stage : Nat) :
    currentAt stage = ActualFormation.generated Runtime.visit.current stage := by
  induction stage with
  | zero => rfl
  | succ stage previous =>
    change SpinPair.next (currentAt stage) =
      SpinPair.next (ActualFormation.generated Runtime.visit.current stage)
    rw [previous]

theorem next_generator (stage : Nat) :
    ActualFormation.nextGenerator (generatorAt stage) = generatorAt (stage + 1) := rfl

/-- The full original event tree is retained alongside the common action carrier. -/
theorem whole_history_read (stage : Nat) :
    (commonAt stage).map Prod.fst =
      (ActualFormation.historyLaw.historyAt Runtime.event.occurrence).observation stage :=
  ActualFormation.whole_history_recovered Runtime.event.occurrence stage

theorem history_frontier (stage : Nat) :
    ((ActualFormation.historyLaw.historyAt Runtime.event.occurrence).observation stage).frontier =
      [.generator (generatorAt stage)] := by
  simpa only [generatorAt, current_is_generated] using
    ActualFormation.frontier_generated Runtime.event.occurrence stage

theorem whole_common_read (stage : Nat) :
    (commonAt stage).map Prod.snd = ActualFormation.jointInput.jointOccurrence
      (((ActualFormation.historyLaw.historyAt Runtime.event.occurrence).observation stage).map
        ActualFormation.linearizeEvent) :=
  ActualFormation.whole_common_state_generated Runtime.event.occurrence stage

/-- A linear coordinate of the original constructor, preserving ingress/running identity. -/
def constructorCode (current : SpinPair.Current) : ℤ :=
  if Recognition.isRunning current then 1 else 0

def constructorRead : ActualFormation.IntegralCarrier →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun generator => constructorCode generator.2)

def fullObservation : ActualFormation.IntegralCarrier →ₗ[ℤ] ℤ × ActualFormation.ActualCoordinates :=
  constructorRead.prod ActualFormation.fieldRead

theorem full_observation_event (generator : ActualFormation.Generator) :
    fullObservation (ActualFormation.event generator) =
      (constructorCode generator.2, ActualFormation.actualCoordinates generator.2) := by
  apply Prod.ext
  · change constructorRead (ActualFormation.event generator) = constructorCode generator.2
    simp only [constructorRead, ActualFormation.event, Finsupp.linearCombination_single, one_smul]
  · change ActualFormation.fieldRead (ActualFormation.event generator) =
      ActualFormation.actualCoordinates generator.2
    exact ActualFormation.fieldRead_event generator

theorem constructor_code_faithful (left right : SpinPair.Current)
    (same : constructorCode left = constructorCode right) :
    Recognition.isRunning left = Recognition.isRunning right := by
  cases first : Recognition.isRunning left <;> cases last : Recognition.isRunning right <;>
    simp [constructorCode, first, last] at same ⊢

/-- The autonomous history model uses the existing actual physical action. -/
abbrev FullModel := Model ActualFormation.nativeAction fullObservation

def modelAt (stage : Nat) : FullModel :=
  projection ActualFormation.nativeAction fullObservation (ActualFormation.event (generatorAt stage))

def readAt (stage : Nat) : ℤ × ActualFormation.ActualCoordinates :=
  modelReadout ActualFormation.nativeAction fullObservation (modelAt stage)

def fieldAt (stage : Nat) : StageNineHolonomicConfiguration :=
  ActualFormation.wholeCoordinates.symm (readAt stage).2.1

theorem full_model_read (stage : Nat) :
    readAt stage = (constructorCode (currentAt stage), ActualFormation.actualCoordinates (currentAt stage)) := by
  rw [readAt, modelAt, modelReadout_projection, full_observation_event]
  rfl

/-- Complete field recovery consumes the original joint-carrier recovery theorem. -/
theorem full_field_read (stage : Nat) : fieldAt stage = Recognition.wholeField (currentAt stage) := by
  have source := ActualFormation.complete_field_read (generatorAt stage)
  change ActualFormation.wholeCoordinates.symm (ActualFormation.fieldRead (ActualFormation.event (generatorAt stage))).1 = _ at source
  rw [ActualFormation.fieldRead_event] at source
  simp only [fieldAt, full_model_read]
  exact source

theorem constructor_read (stage : Nat) : (readAt stage).1 = constructorCode (currentAt stage) :=
  congrArg Prod.fst (full_model_read stage)

theorem model_action_next (stage : Nat) :
    modelAction ActualFormation.nativeAction fullObservation (modelAt stage) = modelAt (stage + 1) := by
  rw [modelAt, modelAction_source, ActualFormation.nativeAction_event, next_generator]
  rfl

theorem complete_history_fibre (left right : ActualFormation.IntegralCarrier) :
    projection ActualFormation.nativeAction fullObservation left =
      projection ActualFormation.nativeAction fullObservation right ↔
      ∀ stage : Nat,
        fullObservation ((ActualFormation.nativeAction ^ stage) left) =
          fullObservation ((ActualFormation.nativeAction ^ stage) right) :=
  model_fibre_iff ActualFormation.nativeAction fullObservation left right

theorem full_observation_determines_step {left right : SpinPair.Current}
    (same : fullObservation (ActualFormation.event (0, left)) =
      fullObservation (ActualFormation.event (0, right))) :
    left = right ∧ SpinPair.next left = SpinPair.next right ∧
      HEq (SpinPair.generatedEvolution (SpinPair.emitted left))
        (SpinPair.generatedEvolution (SpinPair.emitted right)) ∧
      ∀ projection : SpinPair.Projection,
        HEq (SpinPair.authoritativeRoot.projectionOutcomeAt projection left)
          (SpinPair.authoritativeRoot.projectionOutcomeAt projection right) := by
  have observed := same
  rw [full_observation_event, full_observation_event] at observed
  have constructor := constructor_code_faithful left right (congrArg Prod.fst observed)
  have coordinates := congrArg (fun value : ℤ × ActualFormation.ActualCoordinates =>
    ActualFormation.wholeCoordinates.symm value.2.1) observed
  change Recognition.wholeField left = Recognition.wholeField right at coordinates
  exact Recognition.completeInput_determines_entireStep constructor (by
    intro coordinate point
    exact congrArg (fun field => realCoordinate field coordinate point) coordinates)

/-- The complete autonomous model determines the native writer and all installed outputs. -/
theorem complete_model_determines_step {left right : SpinPair.Current}
    (same : projection ActualFormation.nativeAction fullObservation (ActualFormation.event (0, left)) =
      projection ActualFormation.nativeAction fullObservation (ActualFormation.event (0, right))) :
    left = right ∧ SpinPair.next left = SpinPair.next right ∧
      HEq (SpinPair.generatedEvolution (SpinPair.emitted left))
        (SpinPair.generatedEvolution (SpinPair.emitted right)) ∧
      ∀ projection : SpinPair.Projection,
        HEq (SpinPair.authoritativeRoot.projectionOutcomeAt projection left)
          (SpinPair.authoritativeRoot.projectionOutcomeAt projection right) := by
  apply full_observation_determines_step
  have observed := congrArg (modelReadout ActualFormation.nativeAction fullObservation) same
  rw [modelReadout_projection, modelReadout_projection] at observed
  exact observed

/-- The existing action/observation mechanism retains current and literal next observations. -/
def currentNextObservation := jointObservation ActualFormation.nativeAction fullObservation

def jointModelAt (stage : Nat) :=
  canonicalResidual currentNextObservation (ActualFormation.event (generatorAt stage))

theorem current_next_observation_read (stage : Nat) :
    currentNextObservation (ActualFormation.event (generatorAt stage)) =
      (readAt stage, readAt (stage + 1)) := by
  simp only [currentNextObservation, jointObservation, LinearMap.prod_apply, Function.prod_apply,
    LinearMap.comp_apply, ActualFormation.nativeAction_event, next_generator,
    full_observation_event, full_model_read]
  rfl

theorem joint_observation_fibre (left right : ActualFormation.IntegralCarrier) :
    canonicalResidual currentNextObservation left = canonicalResidual currentNextObservation right ↔
      fullObservation left = fullObservation right ∧
        fullObservation (ActualFormation.nativeAction left) =
          fullObservation (ActualFormation.nativeAction right) :=
  joint_fibre_iff ActualFormation.nativeAction fullObservation left right

/-- The current/next joint fibre determines the same complete native step on native points. -/
theorem joint_model_determines_step {left right : SpinPair.Current}
    (same : canonicalResidual currentNextObservation (ActualFormation.event (0, left)) =
      canonicalResidual currentNextObservation (ActualFormation.event (0, right))) :
    left = right ∧ SpinPair.next left = SpinPair.next right ∧
      HEq (SpinPair.generatedEvolution (SpinPair.emitted left))
        (SpinPair.generatedEvolution (SpinPair.emitted right)) ∧
      ∀ projection : SpinPair.Projection,
        HEq (SpinPair.authoritativeRoot.projectionOutcomeAt projection left)
          (SpinPair.authoritativeRoot.projectionOutcomeAt projection right) :=
  full_observation_determines_step ((joint_observation_fibre _ _).mp same).1

/-- Joint next retains the original action and its computed incidence on the same event. -/
theorem joint_action_next (stage : Nat) :
    ActualFormation.jointEvent (generatorAt (stage + 1)) =
      ActualFormation.jointInput.omega (ActualFormation.jointEvent (generatorAt stage)) -
        ActualFormation.jointInput.incidenceResidual (ActualFormation.event (generatorAt stage)) := by
  rw [← next_generator]
  exact ActualFormation.actual_joint_next (generatorAt stage)

theorem original_writer (stage : Nat) :
    SpinPair.source.toRootSource.actual.compile (eventAt stage).occurrence =
      .nativeWrite (materialActionAt (SpinPair.underlying (currentAt stage))) :=
  Recognition.rawEvent_compiles_native (eventAt stage).occurrence

theorem original_whole_ledger (stage : Nat) :
    HEq (eventAt stage).wholeLedgerWriteBack
      (SpinPair.generatedEvolution (SpinPair.emitted (currentAt stage))) :=
  Recognition.rawEvent_wholeLedger (visitAt stage) (SpinPair.emitted (currentAt stage))

theorem original_installed_projection (stage : Nat) (projection : SpinPair.Projection) :
    HEq ((eventAt stage).projectionOutcome projection)
      (SpinPair.authoritativeRoot.projectionOutcomeAt projection (currentAt stage)) :=
  Recognition.allInstalledAuthority_factorizes (visitAt stage) projection

theorem original_entry :
    (SpinPair.generatedRows (eventAt 0).occurrence).sourceEntryAt ⟨0, Nat.zero_lt_one⟩ =
      Runtime.entry := rfl

theorem original_successor_entry :
    (SpinPair.generatedRows (eventAt 0).occurrence).targetEntryAt ⟨0, Nat.zero_lt_one⟩ =
      materialEntry (SpinPair.support (currentAt 1)) := rfl

theorem current_field_is_original_configuration : fieldAt 0 = Runtime.configuration := by
  rw [full_field_read]
  rfl

theorem next_field_is_original_configuration :
    fieldAt 1 = Stage9DEF.Runtime.configurationAt 10 := by
  rw [full_field_read]
  rfl

def occupiedAt (stage : Nat) : Stage9DEF.Source.OccupiedField := Stage9DEF.Source.restrict (fieldAt stage)

def bornAt (stage : Nat) (plus : Bool) (point : BasePoint) (a b : Axis) (x y : Bool) : ℝ :=
  (Stage9DEF.State.vectorEvaluation (rawPreparedVector plus (occupiedAt stage) point)
    (outcomeEffect a b x y).matrix).re

theorem original_tick_restriction : occupiedAt 0 = Runtime.tick.answer := by
  rw [occupiedAt, current_field_is_original_configuration, Runtime.tick_answer]

theorem original_next_tick_restriction : occupiedAt 1 = Runtime.nextTick.answer := by
  rw [occupiedAt, next_field_is_original_configuration]
  rfl

/-- Complete source history restricts to the same tick-16 Born readout. -/
theorem current_born_commutes (plus : Bool) (point : BasePoint) (a b : Axis) (x y : Bool) :
    bornAt 0 plus point a b x y = runtimeProbability plus point a b x y := by
  simp only [bornAt, original_tick_restriction, runtimeProbability]

/-- The literal source successor restricts to the same tick-17 Born readout. -/
theorem next_born_commutes (plus : Bool) (point : BasePoint) (a b : Axis) (x y : Bool) :
    bornAt 1 plus point a b x y = nextProbability plus point a b x y := by
  simp only [bornAt, original_next_tick_restriction, nextProbability]

theorem original_macro_next : Runtime.tick.next.node.erase =
    ⟨MaterialN, SpinPair.livingRoot.generatedNextCurrentAt Runtime.visit⟩ := by
  rw [Runtime.sameOccurrenceActivation.macroAnswerNext, Runtime.sameOccurrenceActivation.answerNext]

end
end SaturationMonoid.PhysicsCore.Stage10.Bell.SourceHistory
