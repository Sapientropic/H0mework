import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Source

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint

open Institutions.Capitalism.Universal.Source.Program ResponsibilityLifecycle
open Followup
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (ready : Ready old) {originInputs : List (List Action)} (inventory : Inventory ready originInputs)

structure Request where
  private mk ::
  resident : Mandate.Challenge.Cross.Resident (B ready) inventory.inputs
  recorded : resident ∈ inventory.objections
  pending : resident.history.isPending (Mandate.Challenge.fromHistory (B ready)) = true

def Request.target (request : Request ready inventory) :
    Mandate.Challenge.Cross.Target (Mandate.Challenge.fromHistory (B ready)) request.resident.original inventory.inputs := by
  cases history : request.resident.history with
  | pending target state slots => exact target
  | closed state archive slots => have impossible := request.pending; rw [history] at impossible; cases impossible

def request? : Option (Request ready inventory) :=
  match selected : inventory.objections.find? (fun resident : Mandate.Challenge.Cross.Resident (B ready) inventory.inputs => resident.history.isPending (Mandate.Challenge.fromHistory (B ready))) with
  | some resident => some ⟨resident, List.mem_of_find?_eq_some selected,
      List.find?_some (p := fun resident : Mandate.Challenge.Cross.Resident (B ready) inventory.inputs => resident.history.isPending (Mandate.Challenge.fromHistory (B ready))) selected⟩
  | none => none

def preamble (request : Request ready inventory) : List Action :=
  if (current ready inventory.inputs).technology = (request.target ready inventory).snapshot (Mandate.Challenge.fromHistory (B ready)) then []
  else [⟨(request.target ready inventory).claim.signer (Mandate.Challenge.fromHistory (B ready)) inventory.inputs, [], ready.scope.challenge, [ready.scope.challenge], .present⟩]

def attempt (request : Request ready inventory) (candidate : Candidate) : List Action :=
  let first := preamble ready inventory request
  first ++ candidate.word ready ((epochLaw ready).execute (current ready inventory.inputs) 0 first).final

def Legal (request : Request ready inventory) (candidate : Candidate) : Prop :=
  Mandate.Response.Active (current ready inventory.inputs) ∧
  (∀ item ∈ (epochLaw ready).rawItems (current ready inventory.inputs) (attempt ready inventory request candidate),
    (epochLaw ready).Valid item.before item.request) ∧
  (((epochLaw ready).execute (current ready inventory.inputs) 0 (attempt ready inventory request candidate)).final.technology.holder = none ∧
   ((epochLaw ready).execute (current ready inventory.inputs) 0 (attempt ready inventory request candidate)).final.technology.offered = none)

instance (request : Request ready inventory) (candidate : Candidate) : Decidable (Legal ready inventory request candidate) := by
  unfold Legal Mandate.Response.Active; infer_instance

structure Paid (request : Request ready inventory) where
  private mk ::
  candidate : Candidate
  listed : candidate ∈ Pending.menu ready inventory.inputs
  legal : Legal ready inventory request candidate

def choose (request : Request ready inventory) : Option (Paid ready inventory request) :=
  match selected : (Pending.menu ready inventory.inputs).find? (fun candidate => decide (Legal ready inventory request candidate)) with
  | some candidate => some ⟨candidate, List.mem_of_find?_eq_some selected,
      of_decide_eq_true (List.find?_some (p := fun candidate => decide (Legal ready inventory request candidate)) selected)⟩
  | none => none

def word (request : Request ready inventory) :=
  attempt ready inventory request ((choose ready inventory request).map Paid.candidate |>.getD (Pending.fallback ready))

def emit := match request? ready inventory with | some request => word ready inventory request | none => []

theorem selected_word_is_actually_legal (request : Request ready inventory) (paid : Paid ready inventory request)
    (selected : choose ready inventory request = some paid) :
    Mandate.Response.Active (current ready inventory.inputs) ∧
    (∀ item ∈ (epochLaw ready).rawItems (current ready inventory.inputs) (word ready inventory request),
      (epochLaw ready).Valid item.before item.request) ∧
    (((epochLaw ready).execute (current ready inventory.inputs) 0 (word ready inventory request)).final.technology.holder = none ∧
     ((epochLaw ready).execute (current ready inventory.inputs) 0 (word ready inventory request)).final.technology.offered = none) := by
  simpa only [word, selected, Option.map_some, Option.getD_some, Legal] using paid.legal

theorem blocked_menu_has_actual_failed_checks (request : Request ready inventory) (blocked : choose ready inventory request = none) :
    ∀ candidate ∈ Pending.menu ready inventory.inputs, ¬ Legal ready inventory request candidate := by
  unfold choose at blocked
  split at blocked
  · cases blocked
  · rename_i absent
    intro candidate inside legal
    have denied := List.find?_eq_none.mp absent candidate inside
    rw [decide_eq_true legal] at denied
    exact denied rfl

inductive Outcome where
  | private absent (noPending : request? ready inventory = none)
  | private paid (request : Request ready inventory) (selected : request? ready inventory = some request)
      (payment : Paid ready inventory request) (paid : choose ready inventory request = some payment)
  | private refused (request : Request ready inventory) (selected : request? ready inventory = some request)
      (unpaid : choose ready inventory request = none)
      (failed : ∀ candidate ∈ Pending.menu ready inventory.inputs, ¬ Legal ready inventory request candidate)

def outcome : Outcome ready inventory :=
  match selected : request? ready inventory with
  | none => .absent selected
  | some request => match paid : choose ready inventory request with
    | some payment => .paid request selected payment paid
    | none => .refused request selected paid (blocked_menu_has_actual_failed_checks ready inventory request paid)

noncomputable def advance := submit ready inventory (emit ready inventory)

noncomputable def run : Nat → Inventory ready originInputs
  | 0 => inventory
  | count + 1 => advance ready (run count)

noncomputable def alternate (inventory : Inventory ready originInputs) : List (List Action) → Inventory ready originInputs
  | [] => inventory
  | word :: tail => alternate (submit ready (advance ready inventory) word) tail

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint
