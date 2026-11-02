import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Projection
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Search.Billing

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Tariff
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Distributed.Reaction.Native.Future.Recovery

/-- Only this exact, personally signed two-item word declares a rate.
An ordinary external use remains a consumption, not a standing quotation. -/
def marker (actor : Bool) : Action := ⟨actor,[actor],.resource,[.resource],.present⟩
def fee (actor : Bool) (bundle : Bundle Good) : Action :=
  ⟨actor,[actor],.resource,[.resource],.use actor bundle .external⟩
def declaration (actor : Bool) (bundle : Bundle Good) := [marker actor,fee actor bundle]

variable (epoch : Epoch) (inputs : List (List Action))

def before (position : Nat) := OutstandingSource.History.currentAt epoch.source inputs (position+2)

structure Entry where
  private mk ::
  position : Nat
  request : Action
  actual : inputs[position]? = some [marker request.signer,request]
  appropriate : Search.Billing.IsFee (Projection.context epoch inputs) request.signer request
  markerAccepted : (Mandate.law base epoch.scope).Valid (before epoch inputs position) (marker request.signer)
  feeAccepted : (Mandate.law base epoch.scope).Valid
    ((Mandate.law base epoch.scope).step (before epoch inputs position) (marker request.signer)) request

def decode (position : Nat) : Option (Entry epoch inputs) :=
  match inputs[position]? with
  | some [_,request] =>
      if actual : inputs[position]? = some [marker request.signer,request] then
        if appropriate : Search.Billing.IsFee (Projection.context epoch inputs) request.signer request then
          if admitted : (Mandate.law base epoch.scope).Valid (before epoch inputs position) (marker request.signer) then
            if paid : (Mandate.law base epoch.scope).Valid
                ((Mandate.law base epoch.scope).step (before epoch inputs position) (marker request.signer)) request then
              some ⟨position,request,actual,appropriate,admitted,paid⟩
            else none
          else none
        else none
      else none
  | _ => none

def read : List (Entry epoch inputs) := (List.range inputs.length).filterMap (decode epoch inputs)
def requests := (read epoch inputs).map Entry.request

namespace Entry
variable {epoch inputs} (entry : Entry epoch inputs)
theorem position_is_actual : entry.position < inputs.length := by
  by_contra outside
  have absent := List.getElem?_eq_none (Nat.le_of_not_gt outside)
  have actual := entry.actual
  rw [absent] at actual
  cases actual

def execution := OutstandingSource.History.actualExecution epoch.source inputs (entry.position+1)

theorem the_declaration_is_its_original_source_event :
    entry.execution.submitted = [marker entry.request.signer,entry.request] ∧
    entry.execution.before = before epoch inputs entry.position := by
  constructor
  · have actual := OutstandingSource.History.scheduled_input_is_actual epoch.source inputs entry.position entry.position_is_actual
    have exact := entry.actual
    rw [List.getElem?_eq_getElem entry.position_is_actual] at exact
    exact actual.trans (Option.some.inj exact)
  · rfl

theorem decode_exact : decode epoch inputs entry.position = some entry := by
  simp only [decode,entry.actual,dite_true,dif_pos entry.appropriate,
    dif_pos entry.markerAccepted,dif_pos entry.feeAccepted]

theorem is_enumerated : entry ∈ read epoch inputs :=
  List.mem_filterMap.mpr ⟨entry.position,List.mem_range.mpr entry.position_is_actual,entry.decode_exact⟩
end Entry

/-- A rate retains either the primitive source-menu occurrence or its actual declaration. -/
inductive Origin (request : Action) where
  | primitive (member : request ∈ (Projection.context epoch inputs).actions)
  | declared (entry : Entry epoch inputs) (same : entry.request = request)

structure Offer where
  request : Action
  origin : Origin epoch inputs request

def directory : List (Offer epoch inputs) :=
  (Projection.context epoch inputs).actions.attach.map (fun request =>
    ⟨request.val,.primitive request.property⟩) ++
  (read epoch inputs).map (fun entry => ⟨entry.request,.declared entry rfl⟩)

def actions := (directory epoch inputs).map Offer.request

/-- The fee catalogue is source-generated from actual declarations. The planner's
preparation alphabet remains the original source menu. -/
def context := { Projection.context epoch inputs with actions := actions epoch inputs }

theorem primitive_is_offered (request : Action)
    (member : request ∈ (Projection.context epoch inputs).actions) : request ∈ actions epoch inputs := by
  apply List.mem_map.mpr
  exact ⟨⟨request,.primitive member⟩,List.mem_append_left _
    (List.mem_map.mpr ⟨⟨request,member⟩,List.mem_attach _ _,rfl⟩),rfl⟩

theorem declaration_is_offered (entry : Entry epoch inputs) : entry.request ∈ actions epoch inputs := by
  apply List.mem_map.mpr
  exact ⟨⟨entry.request,.declared entry rfl⟩,List.mem_append_right _
    (List.mem_map.mpr ⟨entry,entry.is_enumerated,rfl⟩),rfl⟩

section Prefix
variable {epoch inputs}

theorem before_append (later : List (List Action)) (position : Nat) (inside : position ≤ inputs.length) :
    before epoch (inputs ++ later) position = before epoch inputs position := by
  unfold before
  rw [(OutstandingSource.History.actual_frame _ _ _).1,(OutstandingSource.History.actual_frame _ inputs _).1]
  exact congrArg (fun past : OutstandingSource.ExecutionPrefix epoch.source => past.frame.raw)
    (OutstandingSource.History.extending_inputs_preserves_its_executed_prefix epoch.source inputs later _ (by omega))

/-- A later input or bill keeps the original declaration position and its actual admission cut. -/
def Entry.extend (entry : Entry epoch inputs) (later : List (List Action)) : Entry epoch (inputs ++ later) where
  position := entry.position
  request := entry.request
  actual := (List.getElem?_append_left entry.position_is_actual).trans entry.actual
  appropriate := by
    -- Compare the fee predicate instead of the history-dependent planner menus.
    simpa only [Search.Billing.IsFee,Projection.context] using entry.appropriate
  markerAccepted := by rw [before_append later _ (Nat.le_of_lt entry.position_is_actual)];exact entry.markerAccepted
  feeAccepted := by rw [before_append later _ (Nat.le_of_lt entry.position_is_actual)];exact entry.feeAccepted

theorem Entry.the_original_registration_survives_every_actual_suffix
    (entry : Entry epoch inputs) (later : List (List Action)) :
    (entry.extend later).position = entry.position ∧
    (entry.extend later).request = entry.request ∧
    (entry.extend later).execution.before = entry.execution.before ∧
    (entry.extend later).execution.submitted = entry.execution.submitted ∧
    (entry.extend later).request ∈ actions epoch (inputs ++ later) := by
  refine ⟨rfl,rfl,?_,?_,declaration_is_offered _ _ _⟩
  · change before epoch (inputs ++ later) entry.position = before epoch inputs entry.position
    exact before_append later _ (Nat.le_of_lt entry.position_is_actual)
  · rw [(entry.extend later).the_declaration_is_its_original_source_event.1,
      entry.the_declaration_is_its_original_source_event.1]
    rfl
end Prefix

section Submission
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch) (actor : Bool) (bundle : Bundle Good)

def submit := World.submit inventory (declaration actor bundle)
def admission := decode epoch (submit inventory actor bundle).inputs inventory.inputs.length

def evolution : Event.Evolution ⟨epoch,inventory⟩ ⟨epoch,submit inventory actor bundle⟩ :=
  .submit inventory (declaration actor bundle)
def financialRun : (Financial.Family.process sources).Run inventory.finance.current
    (submit inventory actor bundle).finance.current := World.financialRun _ _

theorem registration_is_really_submitted_at_the_saved_cut :
    (World.actual inventory (declaration actor bundle)).submitted = declaration actor bundle ∧
    (World.actual inventory (declaration actor bundle)).before = current epoch inventory.inputs :=
  World.actual_word_and_cut _ _

private theorem marker_preserves (state : Current) :
    ((Mandate.law base epoch.scope).step state (marker actor)).technology = state.technology ∧
    ((Mandate.law base epoch.scope).step state (marker actor)).claims = state.claims := by
  unfold RawLaw.step
  split <;> exact ⟨rfl,rfl⟩

private theorem fee_preserves (state : Current) :
    ((Mandate.law base epoch.scope).step state (fee actor bundle)).technology = state.technology ∧
    ((Mandate.law base epoch.scope).step state (fee actor bundle)).claims = state.claims := by
  unfold RawLaw.step
  split <;> exact ⟨rfl,rfl⟩

theorem registration_does_not_grant_a_seat_or_clear_a_claim :
    (current epoch (submit inventory actor bundle).inputs).technology = (current epoch inventory.inputs).technology ∧
    (current epoch (submit inventory actor bundle).inputs).claims = (current epoch inventory.inputs).claims := by
  have next := Event.observed_current_is_raw_next inventory (declaration actor bundle)
  change current epoch (submit inventory actor bundle).inputs = _ at next
  rw [next]
  change ((Mandate.law base epoch.scope).step
    ((Mandate.law base epoch.scope).step (current epoch inventory.inputs) (marker actor)) (fee actor bundle)).technology = _ ∧ _
  exact ⟨(fee_preserves actor bundle _).1.trans (marker_preserves actor _).1,
    (fee_preserves actor bundle _).2.trans (marker_preserves actor _).2⟩
end
end Submission
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Tariff
