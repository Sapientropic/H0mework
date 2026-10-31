import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Election.ElectionRenewalFace

/-!
# M8 actual election mandate renewal regression

This consumer instantiates the unrestricted producer with natural-number term,
office-seed, and controller-seed carriers.  The small continue/exit examples
are controls only; the public certificate quantifies every inductive history.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M8ActualElectionMandateRenewalRegression

noncomputable section

open ResponsibilityLifecycle
open Election Relations Power Renewal

abbrev ActualEvent :=
  Election.Event (Period := Nat) (OfficeSeed := Nat)
    (ControllerSeed := Nat)

abbrev ActualHistory :=
  Election.Source (Period := Nat) (OfficeSeed := Nat)
    (ControllerSeed := Nat)

def lineageCompiler :
    ElectionLineageCompiler (Period := Nat)
      (OfficeSeed := Nat) (ControllerSeed := Nat)
      (Office := Nat) (Controller := Nat) where
  officeOf := id
  controllerOf := id

def continuingEvent (period : Nat) : ActualEvent :=
  { period := period
    officeSeed := 7
    controllerSeed := 11
    disposition := .continue }

def exitingEvent (period : Nat) : ActualEvent :=
  { period := period
    officeSeed := 7
    controllerSeed := 13
    disposition := .exit }

def continuingHistory (period : Nat) : ActualHistory :=
  .first (continuingEvent period)

def exitingHistory (period : Nat) : ActualHistory :=
  .next (continuingHistory period) (exitingEvent (period + 1))

theorem every_history_generates_actual_election_renewal :
    ∀ history : ActualHistory,
      Nonempty (ActualElectionRenewalFace history lineageCompiler) :=
  fun history => everyActualElectionSource_generatesMandateRenewal
    history lineageCompiler

theorem every_period_generates_continuing_mandate (period : Nat) :
    Nonempty
      (ActualElectionRenewalFace (continuingHistory period)
        lineageCompiler) :=
  everyActualElectionSource_generatesMandateRenewal
    (continuingHistory period) lineageCompiler

theorem continuing_event_is_exact_trace_event (period : Nat) :
    ∃ state ∈
        (electionGame (continuingHistory period)).occurrence.trace,
      (electionActionController (continuingHistory period) lineageCompiler)
        |>.actionSeedAt (electionGame (continuingHistory period)).source
          state
          (sourceGeneratedElectionRenewal (continuingHistory period)
            lineageCompiler).event :=
  electionRenewal_event_mem_actual_trace
    (continuingHistory period) lineageCompiler

def OfficeRelationTraceAt (history : ActualHistory) : Prop :=
  ∃ seed : (officeControllerRelationCompiler history lineageCompiler).ExactRelationSeed,
    (∃ state ∈ (electionGame history).occurrence.trace,
      state = (officeFace lineageCompiler).state (electionGame history).source ∧
      (officeControllerRelationCompiler history lineageCompiler).relationSeedAt
          (electionGame history).source state seed.1 ∧
      (officeFace lineageCompiler).SeedAt
        (electionGame history).source state
        ((officeControllerRelationCompiler history lineageCompiler).beneficiaryActorSeed
          seed.1)) ∧
    seed.actor (officeControllerRelationCompiler history lineageCompiler) =
      mandateOffice history lineageCompiler ∧
    (officeControllerRelationCompiler history lineageCompiler).relationOf seed =
      generatedOfficeControllerRelation history lineageCompiler

theorem continuing_office_relation_has_exact_trace_provenance (period : Nat) :
    OfficeRelationTraceAt (continuingHistory period) :=
  electionRenewal_relation_exact_trace_provenance
    (continuingHistory period) lineageCompiler

theorem continuing_lineages_and_relation_exact (period : Nat) :
    (sourceGeneratedElectionRenewal (continuingHistory period)
        lineageCompiler).actor.1 = 11 ∧
      (mandateOffice (continuingHistory period) lineageCompiler).1 =
        lineageCompiler.officeOf
          (continuingHistory period).current.officeSeed ∧
      (generatedOfficeControllerRelation (continuingHistory period)
          lineageCompiler).1.office = 7 ∧
      (generatedOfficeControllerRelation (continuingHistory period)
          lineageCompiler).1.controller = 11 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem continuing_target_role_is_held (period : Nat) :
    (officeControllerRelationCompiler (continuingHistory period)
        lineageCompiler).roleAt
        (generatedOfficeControllerRelation (continuingHistory period)
          lineageCompiler) .target =
      MandateRole.held :=
  rfl

theorem continuing_exact_M2_power (period : Nat) :
    Nonempty
      (ExactMandatePower (continuingHistory period) lineageCompiler) :=
  ⟨mandateActionPower (continuingHistory period) lineageCompiler⟩

theorem continuing_power_is_restored (period : Nat) :
    (mandateActionPower (continuingHistory period)
      lineageCompiler).freedomChange.kind = FreedomChangeKind.restored :=
  rfl

/-- A later exit event cannot be replayed as the admitted current action of
the earlier continuing occurrence. -/
theorem wrong_current_event_is_rejected (period : Nat) :
    ¬ ((electionActionController (continuingHistory period) lineageCompiler)
      |>.actionAdmittedAt (exitingEvent (period + 1))) := by
  intro event_eq
  have controller_eq := congrArg MandateEvent.controllerSeed event_eq
  change (13 : Nat) = 11 at controller_eq
  exact (by decide : (13 : Nat) ≠ 11) controller_eq

theorem continuing_has_M1_source_consumer (period : Nat) :
    Nonempty (SourceOwnsResponsibilityIncidence
      (mandateVocabulary lineageCompiler)
      (continuingHistory period).current
      (mandateObligation lineageCompiler
        (continuingHistory period).current)) :=
  ⟨electionRenewal_M1_sourceOwnership
    (continuingHistory period) lineageCompiler⟩

theorem continuing_disposition_stays_live (period : Nat) :
    (sourceGeneratedElectionRenewal (continuingHistory period)
        lineageCompiler).exactDisposition.1.target.slots[(mandateSlot lineageCompiler
          (continuingHistory period).current).val]? =
      some (.live (mandateObligation lineageCompiler
        (continuingHistory period).current)) :=
  electionRenewal_continues_live (continuingHistory period)
    lineageCompiler rfl

theorem exit_event_retains_prior_actual_history (period : Nat) :
    (continuingHistory period).current ∈
      (exitingHistory period).occurrence.trace :=
  MandateHistory.prior_current_mem_next_trace
    (continuingHistory period) (exitingEvent (period + 1))

theorem exit_lineage_handoff_exact (period : Nat) :
    (sourceGeneratedElectionRenewal (exitingHistory period)
        lineageCompiler).actor.1 = 13 ∧
      (mandateOffice (exitingHistory period) lineageCompiler).1 =
        lineageCompiler.officeOf (exitingHistory period).current.officeSeed ∧
      (generatedOfficeControllerRelation (exitingHistory period)
          lineageCompiler).1.controller = 13 :=
  ⟨rfl, rfl, rfl⟩

theorem exit_target_role_is_exited (period : Nat) :
    (officeControllerRelationCompiler (exitingHistory period)
        lineageCompiler).roleAt
        (generatedOfficeControllerRelation (exitingHistory period)
          lineageCompiler) .target =
      MandateRole.exited :=
  rfl

theorem exit_power_is_lost (period : Nat) :
    (mandateActionPower (exitingHistory period)
      lineageCompiler).freedomChange.kind = FreedomChangeKind.lost :=
  rfl

theorem exit_disposition_is_terminal (period : Nat) :
    ∃ archive,
      (sourceGeneratedElectionRenewal (exitingHistory period)
          lineageCompiler).exactDisposition.1.target.slots[(mandateSlot lineageCompiler
            (exitingHistory period).current).val]? = some (.terminal archive) :=
  electionRenewal_exits_terminal (exitingHistory period)
    lineageCompiler rfl

structure ActualElectionMandateRenewalCertificate : Prop where
  arbitraryHistoryProducer : ∀ history : ActualHistory,
    Nonempty (ActualElectionRenewalFace history lineageCompiler)
  arbitraryPeriodProducer : ∀ period : Nat,
    Nonempty (ActualElectionRenewalFace (continuingHistory period)
      lineageCompiler)
  continuingExactTrace : ∀ period,
    ∃ state ∈ (electionGame (continuingHistory period)).occurrence.trace,
      (electionActionController (continuingHistory period) lineageCompiler)
        |>.actionSeedAt (electionGame (continuingHistory period)).source
          state
          (sourceGeneratedElectionRenewal (continuingHistory period)
            lineageCompiler).event
  continuingExactLineages : ∀ period,
    (sourceGeneratedElectionRenewal (continuingHistory period)
        lineageCompiler).actor.1 = 11 ∧
      (mandateOffice (continuingHistory period) lineageCompiler).1 =
        lineageCompiler.officeOf
          (continuingHistory period).current.officeSeed
  continuingRelationTrace : ∀ period,
    OfficeRelationTraceAt (continuingHistory period)
  continuingRole : ∀ period,
    (officeControllerRelationCompiler (continuingHistory period)
        lineageCompiler).roleAt
        (generatedOfficeControllerRelation (continuingHistory period)
          lineageCompiler) .target = MandateRole.held
  continuingPower : ∀ period,
    Nonempty (ExactMandatePower (continuingHistory period) lineageCompiler)
  continuingPowerRestored : ∀ period,
    (mandateActionPower (continuingHistory period)
      lineageCompiler).freedomChange.kind = FreedomChangeKind.restored
  wrongCurrentRejected : ∀ period,
    ¬ ((electionActionController (continuingHistory period) lineageCompiler)
      |>.actionAdmittedAt (exitingEvent (period + 1)))
  continuingM1Consumer : ∀ period,
    Nonempty (SourceOwnsResponsibilityIncidence
      (mandateVocabulary lineageCompiler) (continuingHistory period).current
      (mandateObligation lineageCompiler (continuingHistory period).current))
  continuingLive : ∀ period,
    (sourceGeneratedElectionRenewal (continuingHistory period)
        lineageCompiler).exactDisposition.1.target.slots[(mandateSlot lineageCompiler
          (continuingHistory period).current).val]? =
      some (.live (mandateObligation lineageCompiler
        (continuingHistory period).current))
  exitRetainsPriorHistory : ∀ period,
    (continuingHistory period).current ∈
      (exitingHistory period).occurrence.trace
  exitRole : ∀ period,
    (officeControllerRelationCompiler (exitingHistory period)
        lineageCompiler).roleAt
        (generatedOfficeControllerRelation (exitingHistory period)
          lineageCompiler) .target = MandateRole.exited
  exitPowerLost : ∀ period,
    (mandateActionPower (exitingHistory period)
      lineageCompiler).freedomChange.kind = FreedomChangeKind.lost
  exitTerminal : ∀ period,
    ∃ archive,
      (sourceGeneratedElectionRenewal (exitingHistory period)
          lineageCompiler).exactDisposition.1.target.slots[(mandateSlot lineageCompiler
            (exitingHistory period).current).val]? = some (.terminal archive)

theorem actualElectionMandateRenewalDirectConsumer :
    ActualElectionMandateRenewalCertificate where
  arbitraryHistoryProducer := every_history_generates_actual_election_renewal
  arbitraryPeriodProducer := every_period_generates_continuing_mandate
  continuingExactTrace := continuing_event_is_exact_trace_event
  continuingExactLineages := fun period =>
    (continuing_lineages_and_relation_exact period).1
      |> fun controller =>
        ⟨controller, (continuing_lineages_and_relation_exact period).2.1⟩
  continuingRelationTrace :=
    continuing_office_relation_has_exact_trace_provenance
  continuingRole := continuing_target_role_is_held
  continuingPower := continuing_exact_M2_power
  continuingPowerRestored := continuing_power_is_restored
  wrongCurrentRejected := wrong_current_event_is_rejected
  continuingM1Consumer := continuing_has_M1_source_consumer
  continuingLive := continuing_disposition_stays_live
  exitRetainsPriorHistory := exit_event_retains_prior_actual_history
  exitRole := exit_target_role_is_exited
  exitPowerLost := exit_power_is_lost
  exitTerminal := exit_disposition_is_terminal

end
end M8ActualElectionMandateRenewalRegression
end Society
end ProcessGame
end SaturationMonoid
