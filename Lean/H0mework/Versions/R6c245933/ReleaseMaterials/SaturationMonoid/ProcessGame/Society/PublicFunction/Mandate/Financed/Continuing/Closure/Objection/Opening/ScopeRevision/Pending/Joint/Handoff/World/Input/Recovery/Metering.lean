import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Runtime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Tariff
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Search.Counting
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Replay.Repeated

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Distributed.Reaction.Native.Future.Recovery
noncomputable section
variable {epoch : Epoch} {inventory : Inventory epoch} {word : List Action}


variable (cursor : Recovery.Cursor inventory word) (actor : Bool)

abbrev IsFee (request : Action) := Search.Billing.IsFee cursor.model actor request

def feeContext := Tariff.context epoch cursor.saved.inputs

/-- Every rate keeps its primitive source occurrence or its accepted declaration. -/
structure Fee where
  private mk ::
  request : Action
  registered : Tariff.Origin epoch cursor.saved.inputs request
  appropriate : IsFee cursor actor request

def fees : List (Fee cursor actor) :=
  (Tariff.directory epoch cursor.saved.inputs).filterMap fun offer =>
    if suitable : IsFee cursor actor offer.request then some ⟨offer.request,offer.origin,suitable⟩ else none

theorem fee_projection_is_the_complete_source_tariff_list :
    (fees cursor actor).map Fee.request = Search.Billing.tariffs (feeContext cursor) actor := by
  unfold fees Search.Billing.tariffs feeContext Tariff.context Tariff.actions
  rw [List.map_filterMap]
  let select := fun request : Action =>
    if IsFee cursor actor request then some request else none
  have erase : (fun offer : Tariff.Offer epoch cursor.saved.inputs =>
      ((if suitable : IsFee cursor actor offer.request
        then some (⟨offer.request,offer.origin,suitable⟩ : Fee cursor actor) else none).map Fee.request)) =
      (fun offer => select offer.request) := by
    funext offer
    dsimp only [select]
    split_ifs <;> rfl
  rw [erase]
  have mapped : (Tariff.directory epoch cursor.saved.inputs).filterMap (fun offer => select offer.request) =
      List.filterMap select ((Tariff.directory epoch cursor.saved.inputs).map Tariff.Offer.request) :=
    (List.filterMap_map (l := Tariff.directory epoch cursor.saved.inputs) (f := Tariff.Offer.request) (g := select)).symm
  rw [mapped]
  have same : select = Option.guard (fun request => decide (IsFee cursor actor request)) := by
    funext request
    simp only [select,Option.guard]
    split_ifs <;> simp_all
  rw [same,List.filterMap_eq_filter]
  rfl

def quote := (fees cursor actor).head?

theorem unpriced_rejects_every_offered_rate (absent : quote cursor actor = none)
    (request : Action) (member : request ∈ (feeContext cursor).actions) : ¬ IsFee cursor actor request := by
  have empty : fees cursor actor = [] := by
    cases same : fees cursor actor with
    | nil => rfl
    | cons head tail => simp only [quote,same,List.head?_cons,reduceCtorEq] at absent
  have noRates : Search.Billing.tariffs (feeContext cursor) actor = [] := by
    rw [←fee_projection_is_the_complete_source_tariff_list,empty,List.map_nil]
  intro suitable
  have listed : request ∈ Search.Billing.tariffs (feeContext cursor) actor :=
    List.mem_filter.mpr ⟨member,decide_eq_true suitable⟩
  rw [noRates] at listed
  exact List.not_mem_nil listed

theorem unpriced_rejects_every_registered_rate (absent : quote cursor actor = none)
    (request : Action) (member : request ∈ cursor.model.actions) : ¬ IsFee cursor actor request :=
  unpriced_rejects_every_offered_rate cursor actor absent request
    (Tariff.primitive_is_offered epoch cursor.saved.inputs request member)

variable {cursor actor}
variable (fee : Action) (count : Nat)
abbrev attempt (cursor : Recovery.Cursor inventory word) :=
  Mandate.Replay.Repeated.generate base epoch.scope cursor.before fee count
abbrev charged (cursor : Recovery.Cursor inventory word) := cursor.appendActual (attempt fee count cursor).output

theorem invoice_is_submitted_at_its_actual_cut (cursor : Recovery.Cursor inventory word) :
    (World.actual cursor.saved (attempt fee count cursor).output).submitted = (attempt fee count cursor).output ∧
    (World.actual cursor.saved (attempt fee count cursor).output).before = cursor.before :=
  World.actual_word_and_cut _ _

theorem refused_invoice_has_its_actual_failure (cursor : Recovery.Cursor inventory word)
    (refused : (attempt fee count cursor).succeeded = false) :
    ∃ item ∈ (Mandate.law base epoch.scope).rawItems cursor.before (attempt fee count cursor).output,
      item.index = (attempt fee count cursor).consumed.length ∧
      ¬ (Mandate.law base epoch.scope).Valid item.before item.request :=
  (attempt fee count cursor).failure_is_an_actual_raw_item refused

variable (cursor)
def catalogue (actor : Bool) := Search.catalogue cursor.model cursor.before actor cursor.residual
abbrev construction (fee : Action) := charged fee 1 cursor
abbrev units (actor : Bool) (fee : Action) :=
  let built := construction cursor fee
  Search.Counting.comparisonUnits built.model built.before actor cursor.residual

theorem units_is_original (actor : Bool) (fee : Action) : units cursor actor fee =
    Search.Billing.comparisonUnits cursor.residual (catalogue (construction cursor fee) actor) :=
  Search.Counting.comparisonUnits_is_original _ _ _ _
abbrev compared (actor : Bool) (fee : Action) :=
  charged fee (units cursor actor fee) (construction cursor fee)

def restored (actor : Bool) (fee : Action) : Recovery.Cursor inventory word :=
  let staged := compared cursor actor fee
  staged.replayPreparation (Search.Billing.choose staged.model staged.before staged.residual
    (catalogue (construction cursor fee) actor)).preparation

inductive Result (cursor : Recovery.Cursor inventory word) where
  | finished (empty : cursor.residual = [])
  | unpriced (head : Action) (tail : List Action) (pending : cursor.residual = head::tail)
      (absent : quote cursor head.signer = none)
  | constructionRefused (head : Action) (tail : List Action) (pending : cursor.residual = head::tail)
      (fee : Fee cursor head.signer) (quoted : quote cursor head.signer = some fee)
      (refused : (attempt fee.request 1 cursor).succeeded = false)
  | comparisonRefused (head : Action) (tail : List Action) (pending : cursor.residual = head::tail)
      (fee : Fee cursor head.signer) (quoted : quote cursor head.signer = some fee)
      (constructionPaid : (attempt fee.request 1 cursor).succeeded = true)
      (refused : (attempt fee.request (units cursor head.signer fee.request)
        (construction cursor fee.request)).succeeded = false)
  | searched (head : Action) (tail : List Action) (pending : cursor.residual = head::tail)
      (fee : Fee cursor head.signer) (quoted : quote cursor head.signer = some fee)
      (constructionPaid : (attempt fee.request 1 cursor).succeeded = true)
      (comparisonPaid : (attempt fee.request (units cursor head.signer fee.request)
        (construction cursor fee.request)).succeeded = true)

/-- Catalogue construction follows its own payment; its quality fold follows the second payment. -/
def run (cursor : Recovery.Cursor inventory word) : Result cursor :=
  match pending : cursor.residual with
  | [] => .finished pending
  | head::tail => match quoted : quote cursor head.signer with
    | none => .unpriced head tail pending quoted
    | some fee =>
      if paid : (attempt fee.request 1 cursor).succeeded = true then
        if compared : (attempt fee.request (units cursor head.signer fee.request)
            (construction cursor fee.request)).succeeded = true then
          .searched head tail pending fee quoted paid compared
        else .comparisonRefused head tail pending fee quoted paid (Bool.eq_false_iff.mpr compared)
      else .constructionRefused head tail pending fee quoted (Bool.eq_false_iff.mpr paid)

namespace Result
variable {cursor}
def finish : Result cursor → Recovery.Cursor inventory word
  | .finished _ | .unpriced .. => cursor
  | .constructionRefused _ _ _ fee _ _ => construction cursor fee.request
  | .comparisonRefused head _ _ fee _ _ _ => compared cursor head.signer fee.request
  | .searched head _ _ fee _ _ _ => restored cursor head.signer fee.request

def Released : Result cursor → Prop
  | .searched .. => True
  | _ => False

instance (made : Result cursor) : Decidable made.Released := by
  cases made <;> unfold Released <;> infer_instance

theorem every_released_search_has_its_two_actual_prior_payments (made : Result cursor) (released : made.Released) :
    ∃ (head : Action) (tail : List Action) (fee : Fee cursor head.signer),cursor.residual = head::tail ∧
      quote cursor head.signer = some fee ∧
      (attempt fee.request 1 cursor).succeeded = true ∧
      (attempt fee.request (units cursor head.signer fee.request) (construction cursor fee.request)).succeeded = true := by
  cases made <;> try cases released
  next head tail pending fee quoted paid compared => exact ⟨head,tail,fee,pending,quoted,paid,compared⟩

theorem no_original_request_is_credited_for_paying_a_bill (made : Result cursor) (unreleased : ¬ made.Released) :
    made.finish.consumed = cursor.consumed ∧ made.finish.residual = cursor.residual := by
  cases made <;> try exact ⟨rfl,rfl⟩
  exact False.elim (unreleased trivial)

theorem all_original_refusals_and_finance_are_retained (made : Result cursor) :
    made.finish.consumed ++ made.finish.residual = pending inventory word ∧
    Nonempty (Event.Evolution ⟨epoch,inventory⟩ ⟨epoch,made.finish.saved⟩) ∧
    Nonempty ((Financial.Family.process sources).Run inventory.finance.current made.finish.saved.finance.current) :=
  ⟨made.finish.split,⟨made.finish.native⟩,⟨made.finish.finance⟩⟩
end Result

structure Stage (cursor : Recovery.Cursor inventory word) where
  private mk ::
  result : Result cursor
  generated : result = run cursor
  endpoint : Recovery.Cursor inventory word
  exact : endpoint = result.finish

def stage (cursor : Recovery.Cursor inventory word) : Stage cursor :=
  let result := run cursor
  let endpoint := result.finish
  ⟨result,rfl,endpoint,rfl⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering
