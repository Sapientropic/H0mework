import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Replay
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.Accounting

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle Followup
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Computation.Search.Segmented.Publication.Learning.Paid
open PublicFunction.Protocol.SymbolicAuthentication
noncomputable section

variable {epoch : Epoch} (inventory : Inventory epoch) (pending : List Action)

def Offered (index : Fin (code inventory pending).actions.length) : Prop :=
  (code inventory pending).actions[index] ∈ rates inventory ∧
    Native.Future.Recovery.Search.Billing.IsFee
      (Input.Recovery.Tariff.context epoch (prepared inventory).inputs)
      (code inventory pending).actions[index].signer (code inventory pending).actions[index]

instance (index : Fin (code inventory pending).actions.length) : Decidable (Offered inventory pending index) := by
  unfold Offered;infer_instance

/-- A total quote and a per-unit rate are distinct source offers. Their actual
payment and the complete workload remain subject to the original covers gate. -/
def quoteRate? : Option (Fin (code inventory pending).actions.length) :=
  (List.finRange (code inventory pending).actions.length).find? fun index =>
    decide (Offered inventory pending index)

def quotedActions (feeRates : List Action) : List Action :=
  (received inventory ++ [pending,Input.Event.Future.ownWord (prepared inventory)] ++
    futureWords inventory pending ++ feeRates.map (fun request => [request])).flatten

theorem quoted_actions_are_the_original_alphabet :
    quotedActions inventory pending (rates inventory) = (code inventory pending).actions := rfl

/-- Share the same source code, offers, and billing context across the original
finite quote search; no source predicate or candidate position changes. -/
def quoteRateCached : Option (Fin (code inventory pending).actions.length) :=
  let offers := rates inventory
  let actions := quotedActions inventory pending offers
  let context := {Input.Recovery.Projection.context epoch (prepared inventory).inputs with actions := offers}
  (List.finRange actions.length).find? fun index =>
    decide (actions[index] ∈ offers ∧ Native.Future.Recovery.Search.Billing.IsFee
      context actions[index].signer actions[index])

@[csimp] theorem quoteRate_eq_cached : @quoteRate? = @quoteRateCached := by
  funext epoch inventory pending
  unfold quoteRate? quoteRateCached Offered
  rfl

def UnitOffer (quote index : Fin (code inventory pending).actions.length) : Prop :=
  Offered inventory pending index ∧
    (code inventory pending).actions[index].signer = (code inventory pending).actions[quote].signer ∧
    (∀ good ∈ [Good.feedstock,Good.service],
      Owned.PublicTask.Local.Inquiry.Planning.Accounting.quantity (code inventory pending).actions[index] good ≤
      Owned.PublicTask.Local.Inquiry.Planning.Accounting.quantity (code inventory pending).actions[quote] good)

instance (quote index : Fin (code inventory pending).actions.length) : Decidable (UnitOffer inventory pending quote index) := by
  unfold UnitOffer;infer_instance

-- A later compatible declaration can price the unit independently of the total.
def rate? : Option (Fin (code inventory pending).actions.length) :=
  (quoteRate? inventory pending).bind fun quote =>
    (List.finRange (code inventory pending).actions.length).reverse.find? fun index =>
      decide (UnitOffer inventory pending quote index)

def rateCached : Option (Fin (code inventory pending).actions.length) :=
  let offers := rates inventory
  let actions := quotedActions inventory pending offers
  let context := {Input.Recovery.Projection.context epoch (prepared inventory).inputs with actions := offers}
  (quoteRateCached inventory pending).bind fun quote =>
    (List.finRange actions.length).reverse.find? fun index =>
      decide ((actions[index] ∈ offers ∧ Native.Future.Recovery.Search.Billing.IsFee
          context actions[index].signer actions[index]) ∧
        actions[index].signer = actions[quote].signer ∧
        (∀ good ∈ [Good.feedstock,Good.service],
          Owned.PublicTask.Local.Inquiry.Planning.Accounting.quantity actions[index] good ≤
          Owned.PublicTask.Local.Inquiry.Planning.Accounting.quantity actions[quote] good))

@[csimp] theorem rate_eq_cached : @rate? = @rateCached := by
  funext epoch inventory pending
  unfold rate? rateCached
  rw [show quoteRate? inventory pending = quoteRateCached inventory pending from congrFun (congrFun (congrFun quoteRate_eq_cached epoch) inventory) pending]
  unfold UnitOffer Offered
  rfl

theorem selected_quote_is_an_actual_source_offer
    (quote : Fin (code inventory pending).actions.length) (selected : quoteRate? inventory pending = some quote) :
    Offered inventory pending quote := by
  unfold quoteRate? at selected
  exact of_decide_eq_true (List.find?_some (p := fun index : Fin (code inventory pending).actions.length =>
    decide (Offered inventory pending index)) selected)

theorem selected_unit_is_compatible
    (quote rate : Fin (code inventory pending).actions.length)
    (quoted : quoteRate? inventory pending = some quote) (selected : rate? inventory pending = some rate) :
    UnitOffer inventory pending quote rate := by
  unfold rate? at selected
  rw [quoted] at selected
  exact of_decide_eq_true (List.find?_some (p := fun index : Fin (code inventory pending).actions.length =>
    decide (UnitOffer inventory pending quote index)) selected)

theorem selected_rate_is_an_actual_source_offer
    (rate : Fin (code inventory pending).actions.length) (selected : rate? inventory pending = some rate) :
    Offered inventory pending rate := by
  cases quoted : quoteRate? inventory pending with
  | none => simp only [rate?,quoted,Option.bind_none] at selected;cases selected
  | some quote => exact (selected_unit_is_compatible inventory pending quote rate quoted selected).1

def quoteWord := (quoteRate? inventory pending).toList.map fun quote => (code inventory pending).actions[quote]
def payer := ((quoteRate? inventory pending).map fun quote => (code inventory pending).actions[quote].signer).getD (Input.sponsor epoch)
def reader : Fin (code inventory pending).sites :=
  ⟨if payer inventory pending then 1 else 0,by change (if payer inventory pending then 1 else 0) < 2;split <;> decide⟩

def sourceWord := Input.Event.Future.ownWord (prepared inventory)

theorem source_word_is_supported :
    sourceWord inventory ∈ words (code inventory pending).actions (code inventory pending).actionLimit := by
  apply every_language_word_is_a_native_policy_word
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_cons_of_mem _ List.mem_cons_self

theorem quote_word_is_supported :
    quoteWord inventory pending ∈ words (code inventory pending).actions (code inventory pending).actionLimit := by
  cases selected : quoteRate? inventory pending with
  | none =>
      have empty : quoteWord inventory pending = [] := by
        simp only [quoteWord,selected,Option.toList_none,List.map_nil]
      rw [empty]
      apply (mem_words_iff _ _ _).mpr
      exact ⟨Nat.zero_le _,fun _ member => (List.not_mem_nil member).elim⟩
  | some rate =>
      rw [quoteWord,selected]
      change [(code inventory pending).actions[rate]] ∈ _
      exact every_actual_rate_is_supported inventory pending _
        (selected_quote_is_an_actual_source_offer inventory pending rate selected).1

def originalRule : Rule (code inventory pending) :=
  Budget.Programme.Debt.Information.Inquiry.Replay.protocol
    (reader inventory pending) (sourceWord inventory) (source_word_is_supported inventory pending)

def feeRule : Rule (code inventory pending) :=
  Budget.Programme.Debt.Information.Inquiry.Replay.protocol
    (reader inventory pending) (quoteWord inventory pending) (quote_word_is_supported inventory pending)

/-- No feasibility witness is supplied. The original source admission decides
the source-word reference and retains its typed refusal when it cannot run. -/
def task : Owned.Task (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit) where
  model := model inventory pending
  domain := [cursor inventory pending]
  original := originalRule inventory pending
  baseline := (show Whole.Program (code inventory pending) (horizon [cursor inventory pending]) from
    ⟨[feeRule inventory pending,originalRule inventory pending].take (horizon [cursor inventory pending]),by
      simp only [List.length_take];exact Nat.min_le_left _ _⟩)
  point := Owned.PublicTask.currentView (cursor inventory pending)
  rival := continuingOpponent inventory pending
  reader := reader inventory pending
  quote := ⟨[],quoteWord inventory pending⟩
  recoveryRate := rate? inventory pending
  accountingRate := rate? inventory pending
  futureRequests := futureWords inventory pending
  worldInput := some (worldInput inventory)
  worldPending := pending
  worldCurrent := some ⟨by
    intro input supplied
    cases (Option.some.inj supplied).symm
    exact ⟨rfl,native_current_is_the_same_actual_cut inventory pending⟩⟩
  vocabulary := ⟨fun _ => none,fun before => before.round,.service⟩
  encoding := fun _ => none
  law := ⟨fun site before => ⟨before.round,site.val,0⟩,0⟩
  continueUnreserved := true


theorem the_original_planning_input_is_the_actual_prepared_world :
    (task inventory pending).worldInput = some (.actual (prepared inventory)) ∧
    (task inventory pending).futureRequests = ports.map (fun intent => pending ++ Input.emit (prepared inventory) intent) :=
  ⟨rfl,rfl⟩

theorem the_original_planning_cut_uses_the_exact_source_current :
    Native.Authority.currentAt (task inventory pending).model
      (Budget.Programme.Debt.depth (task inventory pending).point.point) = current epoch (prepared inventory).inputs :=
  native_current_is_the_same_actual_cut inventory pending

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource
