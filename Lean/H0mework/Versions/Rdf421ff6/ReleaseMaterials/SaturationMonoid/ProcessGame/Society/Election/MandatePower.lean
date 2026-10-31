import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Election.SourceGeneratedElection
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Power.GeneratedPower

/-!
# Source-generated mandate power

The current election event generates an office--controller relation, dynamic
mandate role, exact action controller, and genuine actionable-freedom change.
The continuation fibre is calculated from the current event's disposition;
no next election, voter, preference, or completed future is stored.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Election

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power

universe u

inductive MandateRole (_Scale : Type u) : Type u where
  | vacant
  | held
  | exited
  deriving Repr

instance {Scale : Type u} : DecidableEq (MandateRole Scale)
  | .vacant, .vacant | .held, .held | .exited, .exited => isTrue rfl
  | .vacant, .held | .vacant, .exited | .held, .vacant
  | .held, .exited | .exited, .vacant | .exited, .held =>
      isFalse (by intro impossible; cases impossible)

inductive MandatePhase (_Scale : Type u) : Type u where
  | idle
  | renew
  | exit
  deriving Repr

instance {Scale : Type u} : DecidableEq (MandatePhase Scale)
  | .idle, .idle | .renew, .renew | .exit, .exit => isTrue rfl
  | .idle, .renew | .idle, .exit | .renew, .idle
  | .renew, .exit | .exit, .idle | .exit, .renew =>
      isFalse (by intro impossible; cases impossible)

instance {Scale : Type u} : Zero (MandatePhase Scale) :=
  ⟨MandatePhase.idle⟩

inductive MandateAction (_Scale : Type u) : Type u where
  | exercise
  deriving Repr

instance {Scale : Type u} : DecidableEq (MandateAction Scale)
  | .exercise, .exercise => isTrue rfl

def mandateExercise (Scale : Type u) : MandateAction Scale :=
  .exercise

inductive MandateContinuationWitness (_Scale : Type u) : Type u where
  | generated

inductive NoMandateContinuation (_Scale : Type u) : Type u

structure OfficeControllerLineage (Office Controller : Type u) where
  office : Office
  controller : Controller
  disposition : MandateDisposition

def phaseOfDisposition {Scale : Type u} :
    MandateDisposition → MandatePhase Scale
  | .continue => .renew
  | .exit => .exit

def advanceMandateRole {Scale : Type u} :
    MandatePhase Scale → MandateRole Scale → MandateRole Scale
  | .idle, role => role
  | .renew, _ => .held
  | .exit, _ => .exited

def MandateContinuationAt
    {Scale Office Controller : Type u}
    (lineage : OfficeControllerLineage Office Controller)
    (side : EdgeSide) (_action : MandateAction Scale) : Type u :=
  match lineage.disposition, side with
  | .continue, .target => MandateContinuationWitness Scale
  | .exit, .source => MandateContinuationWitness Scale
  | _, _ => NoMandateContinuation Scale

variable {Period OfficeSeed ControllerSeed Office Controller : Type u}

variable
  (source : Source (Period := Period) (OfficeSeed := OfficeSeed)
    (ControllerSeed := ControllerSeed))
  (lineageCompiler : ElectionLineageCompiler
    (Period := Period) (OfficeSeed := OfficeSeed)
    (ControllerSeed := ControllerSeed)
    (Office := Office) (Controller := Controller))

def officeControllerRelationCompiler :
    SourceOwnedRelationRoleCompiler
      (electionOccurrenceOf (Period := Period) (OfficeSeed := OfficeSeed)
        (ControllerSeed := ControllerSeed))
      (electionGame source) (officeFace lineageCompiler) where
  RelationSeed := OfficeSeed
  RelationLineage := fun _ => OfficeControllerLineage Office Controller
  relationSeedAt := officeSeedAt
  relationLineageOf := fun actualSource seed =>
    { office := lineageCompiler.officeOf seed.1
      controller := lineageCompiler.controllerOf
        actualSource.current.controllerSeed
      disposition := actualSource.current.disposition }
  beneficiaryActorSeed := id
  beneficiaryActor_active := by
    intro actualSource state seed active
    exact active
  Role := fun _ => MandateRole Period
  Phase := fun _ => MandatePhase Period
  sourceRoleOf := fun _ _ => .vacant
  phaseStepOf := fun _ lineage => phaseOfDisposition lineage.disposition
  advanceRole := fun _ phase role => advanceMandateRole phase role
  FutureCode := MandateAction Period
  futureCodeDecidableEq := inferInstance
  futureCodeCarrier := {mandateExercise Period}
  futureIdle := fun _ => False
  FutureContinuationAt := MandateContinuationAt
  futureBoundaryState := fun _ _ => source.current
  futureBoundaryState_mem := by
    intro _ _
    exact source.current_mem_occurrence_trace
  FutureContinuationWitnessAt := fun _ _ _ _ => True
  futureContinuation_witnessed := fun _ _ _ _ => trivial

def electionActionController :
    SourceOwnedActionControllerCompiler (electionGame source)
      (controllerFace lineageCompiler) where
  ActionSeed := Event (Period := Period) (OfficeSeed := OfficeSeed)
    (ControllerSeed := ControllerSeed)
  actionAdmittedAt := fun event => event = source.current
  actionState := fun actualSource => actualSource.current
  actionState_mem := source.current_mem_occurrence_trace
  actorState_mem := source.current_mem_occurrence_trace
  actorSeed := fun event => event.controllerSeed
  actorSeed_active := by
    intro event admitted
    change source.current = source.current ∧
      event.controllerSeed = source.current.controllerSeed
    exact ⟨rfl, congrArg MandateEvent.controllerSeed admitted⟩

def exactElectionAction :
    (electionActionController source lineageCompiler).ExactActionSeed :=
  exactCurrentEventSeed source

def exactOfficeRelationSeed :
    (officeControllerRelationCompiler source lineageCompiler).ExactRelationSeed :=
  ⟨source.current.officeSeed, source.current,
    source.current_mem_occurrence_trace, rfl, rfl⟩

instance electionMandatePhaseZero :
    Zero ((officeControllerRelationCompiler source lineageCompiler).Phase
      (electionGame source).source) := by
  change Zero (MandatePhase Period)
  infer_instance

def mandateController :=
  (exactElectionAction source lineageCompiler).actor
    (electionActionController source lineageCompiler)

def mandateOffice :=
  (exactOfficeRelationSeed source lineageCompiler).actor
    (officeControllerRelationCompiler source lineageCompiler)

def generatedOfficeControllerRelation :=
  (officeControllerRelationCompiler source lineageCompiler).relationOf
    (exactOfficeRelationSeed source lineageCompiler)

@[simp] theorem generatedOfficeControllerRelation_disposition :
    (generatedOfficeControllerRelation source lineageCompiler).1.disposition =
      source.current.disposition :=
  rfl

noncomputable abbrev MandateSourceCodes :=
  (officeControllerRelationCompiler source lineageCompiler).futureCodesAt
    (generatedOfficeControllerRelation source lineageCompiler) .source

noncomputable abbrev MandateTargetCodes :=
  (officeControllerRelationCompiler source lineageCompiler).futureCodesAt
    (generatedOfficeControllerRelation source lineageCompiler) .target

theorem mandateExercise_in_carrier :
    mandateExercise Period ∈
      (officeControllerRelationCompiler source lineageCompiler).futureCodeCarrier := by
  exact Finset.mem_singleton_self _

theorem mandateExercise_not_idle :
    ¬ (officeControllerRelationCompiler source lineageCompiler).futureIdle
      (mandateExercise Period) := by
  simp [officeControllerRelationCompiler]

theorem mandateExercise_absent_source_of_continue
    (continued : source.current.disposition = .continue) :
    mandateExercise Period ∉ MandateSourceCodes source lineageCompiler := by
  intro member
  have continuation :=
    ((officeControllerRelationCompiler source lineageCompiler)
      |>.mem_futureCodesAt_iff
        (generatedOfficeControllerRelation source lineageCompiler)
        .source (mandateExercise Period)).mp member |>.2
  rcases continuation with ⟨continuation⟩
  change (match source.current.disposition, EdgeSide.source with
    | .continue, .target => MandateContinuationWitness Period
    | .exit, .source => MandateContinuationWitness Period
    | _, _ => NoMandateContinuation Period) at continuation
  rw [continued] at continuation
  exact nomatch continuation

theorem mandateExercise_mem_target_of_continue
    (continued : source.current.disposition = .continue) :
    mandateExercise Period ∈ MandateTargetCodes source lineageCompiler := by
  apply ((officeControllerRelationCompiler source lineageCompiler)
    |>.mem_futureCodesAt_iff
      (generatedOfficeControllerRelation source lineageCompiler)
      .target (mandateExercise Period)).mpr
  refine ⟨mandateExercise_in_carrier source lineageCompiler, ?_⟩
  refine ⟨?_⟩
  change (match source.current.disposition, EdgeSide.target with
    | .continue, .target => MandateContinuationWitness Period
    | .exit, .source => MandateContinuationWitness Period
    | _, _ => NoMandateContinuation Period)
  rw [continued]
  exact MandateContinuationWitness.generated

theorem mandateExercise_mem_source_of_exit
    (exited : source.current.disposition = .exit) :
    mandateExercise Period ∈ MandateSourceCodes source lineageCompiler := by
  apply ((officeControllerRelationCompiler source lineageCompiler)
    |>.mem_futureCodesAt_iff
      (generatedOfficeControllerRelation source lineageCompiler)
      .source (mandateExercise Period)).mpr
  refine ⟨mandateExercise_in_carrier source lineageCompiler, ?_⟩
  refine ⟨?_⟩
  change (match source.current.disposition, EdgeSide.source with
    | .continue, .target => MandateContinuationWitness Period
    | .exit, .source => MandateContinuationWitness Period
    | _, _ => NoMandateContinuation Period)
  rw [exited]
  exact MandateContinuationWitness.generated

theorem mandateExercise_absent_target_of_exit
    (exited : source.current.disposition = .exit) :
    mandateExercise Period ∉ MandateTargetCodes source lineageCompiler := by
  intro member
  have continuation :=
    ((officeControllerRelationCompiler source lineageCompiler)
      |>.mem_futureCodesAt_iff
        (generatedOfficeControllerRelation source lineageCompiler)
        .target (mandateExercise Period)).mp member |>.2
  rcases continuation with ⟨continuation⟩
  change (match source.current.disposition, EdgeSide.target with
    | .continue, .target => MandateContinuationWitness Period
    | .exit, .source => MandateContinuationWitness Period
    | _, _ => NoMandateContinuation Period) at continuation
  rw [exited] at continuation
  exact nomatch continuation

noncomputable def mandateFreedomChange :
    ActionableFreedomChange
      (officeControllerRelationCompiler source lineageCompiler).futureIdle
      (MandateSourceCodes source lineageCompiler)
      (MandateTargetCodes source lineageCompiler) := by
  cases dispositionEq : source.current.disposition
  ·
      apply ActionableFreedomChange.restored (mandateExercise Period)
      · exact mandateExercise_absent_source_of_continue
          source lineageCompiler dispositionEq
      · constructor
        · exact mandateExercise_mem_target_of_continue
            source lineageCompiler dispositionEq
        · exact mandateExercise_not_idle source lineageCompiler
  ·
      apply ActionableFreedomChange.lost (mandateExercise Period)
      · constructor
        · exact mandateExercise_mem_source_of_exit
            source lineageCompiler dispositionEq
        · exact mandateExercise_not_idle source lineageCompiler
      · exact mandateExercise_absent_target_of_exit
          source lineageCompiler dispositionEq

theorem mandatePhase_nonzero :
    (officeControllerRelationCompiler source lineageCompiler).phaseStep
        (generatedOfficeControllerRelation source lineageCompiler) ≠ 0 := by
  change phaseOfDisposition (Scale := Period) source.current.disposition ≠
    (0 : MandatePhase Period)
  cases source.current.disposition <;>
    intro impossible <;> cases impossible

/-- Exact M2 power handoff generated for every current election event. -/
noncomputable def mandateActionPower :
    ActionPowerOverAt
      (officeControllerRelationCompiler source lineageCompiler)
      (electionActionController source lineageCompiler)
      (mandateController source lineageCompiler)
      (mandateOffice source lineageCompiler)
      (generatedOfficeControllerRelation source lineageCompiler) where
  action := exactElectionAction source lineageCompiler
  controller_exact := rfl
  constraint :=
    { interest := ⟨exactOfficeRelationSeed source lineageCompiler, rfl, rfl⟩
      phase_nonzero := mandatePhase_nonzero source lineageCompiler }
  freedomChange := mandateFreedomChange source lineageCompiler

theorem mandate_power_changes_future :
    MandateSourceCodes source lineageCompiler ≠
      MandateTargetCodes source lineageCompiler :=
  (mandateActionPower source lineageCompiler).freedom_ne

theorem mandate_target_role_generated :
    (officeControllerRelationCompiler source lineageCompiler).RelationRoleAt
      (mandateOffice source lineageCompiler)
      (generatedOfficeControllerRelation source lineageCompiler) .target
      ((officeControllerRelationCompiler source lineageCompiler).roleAt
        (generatedOfficeControllerRelation source lineageCompiler) .target) :=
  ⟨(mandateActionPower source lineageCompiler).constraint.interest, rfl⟩

end Election
end Society
end ProcessGame
end SaturationMonoid
