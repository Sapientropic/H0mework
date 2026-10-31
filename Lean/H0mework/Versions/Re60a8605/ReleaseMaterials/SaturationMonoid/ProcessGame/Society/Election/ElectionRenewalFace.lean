import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Election.MandateResponsibility
import H0mework.Society.Renewal.RenewalFaceSource

/-!
# Actual source-generated election renewal

For every actual election history and current event, one exact source seed
generates the controller lineage, office--controller relation, M2 action-power
handoff, M1 responsibility consumer, and source-owned continuation/exit edge.
This is a local ProcessGame face, not a living-law root or operational root
installation.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Election

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power Renewal

universe u

variable {Period OfficeSeed ControllerSeed Office Controller : Type u}

variable
  (source : Source (Period := Period) (OfficeSeed := OfficeSeed)
    (ControllerSeed := ControllerSeed))
  (lineageCompiler : ElectionLineageCompiler
    (Period := Period) (OfficeSeed := OfficeSeed)
    (ControllerSeed := ControllerSeed)
    (Office := Office) (Controller := Controller))

structure MandateStandingProjection where
  period : Period
  controller : (electionActionController source lineageCompiler).Actor
  office : (officeControllerRelationCompiler source lineageCompiler).Actor
  relation :
    (officeControllerRelationCompiler source lineageCompiler).GeneratedRelation
  targetRole :
    (officeControllerRelationCompiler source lineageCompiler).Role
      (electionGame source).source
  obligation : AdmittedObligation (mandateVocabulary lineageCompiler)

def mandateStandingOf
    (_seed : (electionActionController source lineageCompiler).ExactActionSeed) :
    MandateStandingProjection source lineageCompiler where
  period := source.current.period
  controller := mandateController source lineageCompiler
  office := mandateOffice source lineageCompiler
  relation := generatedOfficeControllerRelation source lineageCompiler
  targetRole :=
    (officeControllerRelationCompiler source lineageCompiler).roleAt
      (generatedOfficeControllerRelation source lineageCompiler) .target
  obligation := mandateObligation lineageCompiler source.current

abbrev ExactMandatePower :=
  ActionPowerOverAt
    (officeControllerRelationCompiler source lineageCompiler)
    (electionActionController source lineageCompiler)
    (mandateController source lineageCompiler)
    (mandateOffice source lineageCompiler)
    (generatedOfficeControllerRelation source lineageCompiler)

def ElectionRenewalConsumerAt
    (seed : (electionActionController source lineageCompiler).ExactActionSeed) :
    Type u :=
  { power : ExactMandatePower source lineageCompiler // power.action = seed } ×
    SourceOwnsResponsibilityIncidence (mandateVocabulary lineageCompiler)
      source.current (mandateObligation lineageCompiler source.current)

def ElectionRenewalDispositionAt
    (seed : (electionActionController source lineageCompiler).ExactActionSeed) :
    Type u :=
  { edge : (mandateProcess lineageCompiler).Edge
      (admittedMandateState lineageCompiler source.current) //
      edge = mandateReviewEdge lineageCompiler source.current ∧
        seed.1 = source.current }

abbrev ActualElectionRenewalFace :=
  SourceGeneratedRenewalFace
    (electionGame source)
    (electionActionController source lineageCompiler).ActionSeed
    (electionActionController source lineageCompiler).actionSeedAt
    (fun _ => Controller)
    (fun _ exactSeed => lineageCompiler.controllerOf
      exactSeed.1.controllerSeed)
    (MandateStandingProjection source lineageCompiler)
    (mandateStandingOf source lineageCompiler)
    (ElectionRenewalConsumerAt source lineageCompiler)
    (ElectionRenewalDispositionAt source lineageCompiler)

/-- Universal actual-election producer.  `source` ranges over arbitrary
inductive histories and `Period` over an arbitrary carrier. -/
noncomputable def sourceGeneratedElectionRenewal :
    ActualElectionRenewalFace source lineageCompiler :=
  SourceGeneratedRenewalFace.generate
    (exactElectionAction source lineageCompiler)
    (⟨mandateActionPower source lineageCompiler, rfl⟩,
      mandateSourceOwnership lineageCompiler source.current)
    ⟨mandateReviewEdge lineageCompiler source.current, rfl, rfl⟩

theorem electionRenewal_event_mem_actual_trace :
    ∃ state ∈ (electionGame source).occurrence.trace,
      (electionActionController source lineageCompiler).actionSeedAt
        (electionGame source).source state
        (sourceGeneratedElectionRenewal source lineageCompiler).event :=
  (sourceGeneratedElectionRenewal source lineageCompiler)
    |>.event_mem_source_trace

@[simp] theorem electionRenewal_event_eq_current :
    (sourceGeneratedElectionRenewal source lineageCompiler).event =
      source.current :=
  rfl

@[simp] theorem electionRenewal_controller_lineage :
    (sourceGeneratedElectionRenewal source lineageCompiler).actor.1 =
      lineageCompiler.controllerOf source.current.controllerSeed :=
  rfl

@[simp] theorem electionRenewal_standing_exact :
    (sourceGeneratedElectionRenewal source lineageCompiler).standing =
      mandateStandingOf source lineageCompiler
        (exactElectionAction source lineageCompiler) :=
  rfl

@[simp] theorem electionRenewal_power_consumer_exact :
    (sourceGeneratedElectionRenewal source lineageCompiler)
        |>.responsibilityConsumer.1.1 =
      mandateActionPower source lineageCompiler :=
  rfl

theorem electionRenewal_controller_exact_trace_provenance :
    ∃ state ∈ (electionGame source).occurrence.trace,
      state = (electionActionController source lineageCompiler).actionState
          (electionGame source).source ∧
        (electionActionController source lineageCompiler).actionAdmittedAt
          ((sourceGeneratedElectionRenewal source lineageCompiler)
            |>.responsibilityConsumer.1.1.action.1) :=
  (sourceGeneratedElectionRenewal source lineageCompiler)
    |>.responsibilityConsumer.1.1.controller_exact_state_provenance

theorem electionRenewal_relation_exact_trace_provenance :
    ∃ seed : (officeControllerRelationCompiler source lineageCompiler).ExactRelationSeed,
      (∃ state ∈ (electionGame source).occurrence.trace,
        state = (officeFace lineageCompiler).state
          (electionGame source).source ∧
        (officeControllerRelationCompiler source lineageCompiler).relationSeedAt
          (electionGame source).source state seed.1 ∧
        (officeFace lineageCompiler).SeedAt
          (electionGame source).source state
          ((officeControllerRelationCompiler source lineageCompiler).beneficiaryActorSeed
            seed.1)) ∧
      seed.actor (officeControllerRelationCompiler source lineageCompiler) =
        mandateOffice source lineageCompiler ∧
      (officeControllerRelationCompiler source lineageCompiler).relationOf seed =
        generatedOfficeControllerRelation source lineageCompiler :=
  (sourceGeneratedElectionRenewal source lineageCompiler)
    |>.responsibilityConsumer.1.1.interest_exact_state_provenance

noncomputable def electionRenewal_M1_sourceOwnership :
    SourceOwnsResponsibilityIncidence (mandateVocabulary lineageCompiler)
      source.current (mandateObligation lineageCompiler source.current) :=
  (sourceGeneratedElectionRenewal source lineageCompiler)
    |>.responsibilityConsumer.2

@[simp] theorem electionRenewal_disposition_edge_exact :
    (sourceGeneratedElectionRenewal source lineageCompiler)
        |>.exactDisposition.1 =
      mandateReviewEdge lineageCompiler source.current :=
  rfl

theorem electionRenewal_continues_live
    (continued : source.current.disposition = .continue) :
    (sourceGeneratedElectionRenewal source lineageCompiler)
        |>.exactDisposition.1.target.slots[(mandateSlot lineageCompiler
          source.current).val]? =
      some (.live (mandateObligation lineageCompiler source.current)) := by
  rw [electionRenewal_disposition_edge_exact]
  exact continued_mandate_is_live lineageCompiler source.current continued

theorem electionRenewal_exits_terminal
    (exited : source.current.disposition = .exit) :
    ∃ archive,
      (sourceGeneratedElectionRenewal source lineageCompiler)
          |>.exactDisposition.1.target.slots[(mandateSlot lineageCompiler
            source.current).val]? = some (.terminal archive) := by
  rw [electionRenewal_disposition_edge_exact]
  exact exited_mandate_is_terminal lineageCompiler source.current exited

theorem electionRenewal_power_changes_future :
    MandateSourceCodes source lineageCompiler ≠
      MandateTargetCodes source lineageCompiler :=
  (sourceGeneratedElectionRenewal source lineageCompiler)
    |>.responsibilityConsumer.1.1.freedom_ne

/-- Compact universal mouth.  No electorate, voter, preference, truth,
finite-term bound, or target outcome is an argument. -/
theorem everyActualElectionSource_generatesMandateRenewal :
    Nonempty (ActualElectionRenewalFace source lineageCompiler) :=
  ⟨sourceGeneratedElectionRenewal source lineageCompiler⟩

end Election
end Society
end ProcessGame
end SaturationMonoid
