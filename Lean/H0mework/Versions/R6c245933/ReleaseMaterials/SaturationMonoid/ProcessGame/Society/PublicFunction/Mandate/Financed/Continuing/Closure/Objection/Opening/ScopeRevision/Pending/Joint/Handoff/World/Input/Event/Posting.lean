import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Costs
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Response
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Posting.Visit

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Posting

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Financial.Family.Migration.Posting

noncomputable section

private theorem submit_matched {epoch : Epoch} (inventory : Inventory epoch) (word : List Action) :
    Financial.Family.ledgerClaims sources inventory.finance.current =
      (PublicFunction.Costs.Visits.rawAt sources (World.I epoch (inventory.inputs ++ [word]))
        (inventory.inputs.length + 2)).claims :=
  inventory.matrix.trans (congrArg RawCurrent.claims
    (Mandate.Challenge.Cross.emitted_word_uses_actual_cut epoch.bound inventory.inputs word).symm)

private def submission {epoch : Epoch} (inventory : Inventory epoch) (word : List Action) : VisitReceipt sources :=
  receive sources (World.I epoch (inventory.inputs ++ [word])) (inventory.inputs.length + 2)
    inventory.finance (inventory.compatible epoch _) (submit_matched inventory word)

private def crossing {epoch : Epoch} (inventory : Inventory epoch)
    (fresh : Handoff.Ready epoch.bound inventory.inputs) : List (VisitReceipt sources) :=
  intervalReceipts sources (Handoff.I fresh) 0 4 inventory.finance
    (inventory.compatible (Epoch.ofFresh fresh) (epochInputs fresh)) inventory.matrix

private def crossingAt {epoch : Epoch} (inventory : Inventory epoch)
    (fresh : Handoff.Ready epoch.bound inventory.inputs) (actualInputs : List (List Action)) : List (VisitReceipt sources) :=
  intervalReceipts sources (OutstandingSource.History.input (Handoff.source fresh) actualInputs) 0
    (actualInputs.length+2) inventory.finance
    (inventory.compatible (Epoch.ofFresh fresh) actualInputs) inventory.matrix

def receipts {first last : Packet} : Evolution first last → List (VisitReceipt sources)
  | .same _ => []
  | .submit inventory word => [submission inventory word]
  | .handoff inventory fresh => crossing inventory fresh
  | .handoffAt inventory fresh actualInputs => crossingAt inventory fresh actualInputs
  | .append earlier later => receipts earlier ++ receipts later

theorem keys {first last : Packet} (path : Evolution first last) :
    (receipts path).map (VisitReceipt.window sources) = Costs.records path := by
  induction path with
  | same packet => rfl
  | submit inventory word => rfl
  | handoff inventory fresh => exact intervalReceipts_keys sources (Handoff.I fresh) 0 4 inventory.finance _ _
  | handoffAt inventory fresh actualInputs =>
      exact intervalReceipts_keys sources
        (OutstandingSource.History.input (Handoff.source fresh) actualInputs) 0 (actualInputs.length+2) inventory.finance _ _
  | append earlier later ih₁ ih₂ => simp only [receipts, List.map_append, ih₁, ih₂, Costs.records]

theorem events {first last : Packet} (path : Evolution first last) :
    ((receipts path).map (fun receipt => (receipt.native sources).events)).flatten =
      (Future.Expiry.Progress.Response.financeAlong path).events := by
  induction path with
  | same packet => rfl
  | submit inventory word =>
      change (World.financialRun inventory word).events ++ [] = _
      exact List.append_nil _
  | handoff inventory fresh => exact intervalReceipts_events sources (Handoff.I fresh) 0 4 inventory.finance _ _
  | handoffAt inventory fresh actualInputs =>
      exact intervalReceipts_events sources
        (OutstandingSource.History.input (Handoff.source fresh) actualInputs) 0 (actualInputs.length+2) inventory.finance _ _
  | append earlier later ih₁ ih₂ =>
      change ((receipts earlier ++ receipts later).map (fun receipt => (receipt.native sources).events)).flatten =
        ((Future.Expiry.Progress.Response.financeAlong earlier).concatRuns _
          (Future.Expiry.Progress.Response.financeAlong later)).events
      rw [List.map_append, List.flatten_append, ih₁, ih₂, NativeResponsibilityProcess.Run.events_concatRuns]

def actual {first last : Packet} (path : Evolution first last) (side : Side) (party : Bool) (good : Good) :=
  runAmount sources (Future.Expiry.Progress.Response.financeAlong path) side party good

theorem exact_amount {first last : Packet} (path : Evolution first last) (side : Side) (party : Bool) (good : Good) :
    actual path side party good = Financial.Family.Migration.Posting.total sources (Costs.records path) side party good := by
  unfold actual runAmount
  rw [← events path]
  have fold (entries : List (VisitReceipt sources)) :
      ((entries.map (fun receipt => (receipt.native sources).events)).flatten.map
        (fun event => amount sources (Financial.Family.Migration.sourceEvent sources event) side party good)).sum =
      Financial.Family.Migration.Posting.total sources (entries.map (VisitReceipt.window sources)) side party good := by
    induction entries with
    | nil => rfl
    | cons receipt rest ih =>
        simp only [List.map_cons, List.flatten_cons, List.map_append, List.sum_append]
        change runAmount sources (receipt.native sources) side party good + _ = _
        rw [VisitReceipt.exact_amount, ih]
        rfl
  rw [fold, keys]

theorem debit_is_the_same_material_payment {first last : Packet}
    (path : Evolution first last) (party : Bool) (good : Good) :
    actual path .debit party good = Costs.cost path party (.debtPayment good) := by
  rw [exact_amount, total_debit]
  rfl

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Posting
