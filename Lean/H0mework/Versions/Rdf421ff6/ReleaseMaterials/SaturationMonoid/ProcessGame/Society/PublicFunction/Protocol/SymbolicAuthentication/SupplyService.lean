import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalSupply

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SupplyService

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (observed : List (EventHistory.Stage (code := model.source.code))) (retainedAt : Nat)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
  (target : Fin model.source.code.sites) (rival : Opponent model.source.code)

abbrev entry := observed.take retainedAt

abbrev stages := LocalSupply.produce vocabulary encoding law start observed (entry model observed retainedAt) rival

def supplyRows := (StageTrace.records (EventHistory.execute start observed)
  (LocalSupply.supplyStages vocabulary law start observed rival)).filter
    (fun row => row.submitted != [] && (StageTrace.activation row).isSome)

def toTarget (row : StageTrace.Record (code := model.source.code)) : Bool :=
  match row.submitted.head? with
  | none => false
  | some request => match request.operation with
    | .transfer sender recipient _ => decide (recipient = model.source.code.siteParty target ∧ sender ≠ recipient) &&
        (model.source.code.law.rawItems (EventStep.seed (EventHistory.execute start observed)).current
          (RetainedIntent.intent vocabulary encoding law start (entry model observed retainedAt) target)).any
          (fun needed => (model.source.code.law.debit needed.before needed.request).any fun debt => decide
            (debt.1.1 = model.source.code.siteParty target ∧
              needed.before.stock debt.1.1 debt.1.2 < flowAt (model.source.code.law.debit needed.before needed.request) debt.1.1 debt.1.2 ∧
              row.before.current.stock debt.1.1 debt.1.2 <
                (model.source.code.law.step row.before.current request).stock debt.1.1 debt.1.2))
    | _ => false

def servedAfter : Prop :=
  ∃ index ∈ List.range (stages model start observed retainedAt vocabulary encoding law rival).length,
    (LocalSupply.middle vocabulary law start observed rival).length ≤ index ∧ ∃ row,
      (StageTrace.records start (stages model start observed retainedAt vocabulary encoding law rival))[index]? = some row ∧
      StageTrace.activation row = some target ∧
      row.submitted = RetainedIntent.intent vocabulary encoding law start (entry model observed retainedAt) target ∧
      (∀ item ∈ StageTrace.items row, model.source.code.law.Valid item.before item.request) ∧
      ∃ stage, (stages model start observed retainedAt vocabulary encoding law rival)[index]? = some stage ∧
        IncidentResponse.sameRule model stage.1
          (RetainedIntent.protocol vocabulary encoding law start (entry model observed retainedAt)) = true
instance : Decidable (servedAfter model start observed retainedAt vocabulary encoding law target rival) := by
  unfold servedAfter; infer_instance

def Goal : Prop :=
  retainedAt ≤ observed.length ∧ RetainedIntent.intent vocabulary encoding law start (entry model observed retainedAt) target ≠ [] ∧
    ¬ (∀ item ∈ model.source.code.law.rawItems (EventStep.seed (EventHistory.execute start observed)).current
      (RetainedIntent.intent vocabulary encoding law start (entry model observed retainedAt) target),
        model.source.code.law.Valid item.before item.request) ∧
    servedAfter model start observed retainedAt vocabulary encoding law target rival ∧
    (supplyRows model start observed vocabulary law rival).isEmpty = false ∧
    ∀ row ∈ supplyRows model start observed vocabulary law rival,
      toTarget model start observed retainedAt vocabulary encoding law target row = true ∧
      ∀ item ∈ StageTrace.items row, model.source.code.law.Valid item.before item.request
instance : Decidable (Goal model start observed retainedAt vocabulary encoding law target rival) := by
  unfold Goal; infer_instance

def fulfilled : Bool := decide (Goal model start observed retainedAt vocabulary encoding law target rival)

theorem successful_recovery_has_paid_supply_and_the_exact_original_service
    (accepted : fulfilled model start observed retainedAt vocabulary encoding law target rival = true) :
    Goal model start observed retainedAt vocabulary encoding law target rival := of_decide_eq_true accepted

theorem blocked_recovery_keeps_the_actual_failed_obligation
    (rejected : fulfilled model start observed retainedAt vocabulary encoding law target rival = false) :
    ¬ Goal model start observed retainedAt vocabulary encoding law target rival := by
  simpa only [fulfilled, decide_eq_false_iff_not] using rejected

theorem the_generated_response_keeps_the_whole_prefix_and_its_source_clock :
    observed <+: stages model start observed retainedAt vocabulary encoding law rival ∧
      (stages model start observed retainedAt vocabulary encoding law rival).length ≤ observed.length + 4 * model.source.code.sites :=
  LocalSupply.exact_source_service_clock vocabulary encoding law start observed (entry model observed retainedAt) rival

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SupplyService
