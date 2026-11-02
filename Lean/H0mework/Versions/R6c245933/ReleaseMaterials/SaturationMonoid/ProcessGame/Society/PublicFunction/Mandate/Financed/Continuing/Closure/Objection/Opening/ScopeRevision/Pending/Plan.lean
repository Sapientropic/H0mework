import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Source
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cuts

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Followup

variable {fuel : ℚ} {inventory : Joint.Inventory fuel} (ready : Ready inventory) (inputs : List (List Action))

abbrev B := epochBound ready
abbrev current := OutstandingSource.History.currentAt (epochSource ready) inputs (inputs.length + 2)
abbrev Row := Sigma fun original : Mandate.Challenge.Claim (Mandate.Challenge.fromHistory (B ready)) inputs => Mandate.Challenge.History (Mandate.Challenge.fromHistory (B ready)) inputs original
def rows := Mandate.Challenge.recordsAt (Mandate.Challenge.fromHistory (B ready)) inputs (inputs.length + 2)

structure Request where
  private mk ::
  original : Mandate.Challenge.Claim (Mandate.Challenge.fromHistory (B ready)) inputs
  history : Mandate.Challenge.History (Mandate.Challenge.fromHistory (B ready)) inputs original
  recorded : (⟨original, history⟩ : Sigma fun claim => Mandate.Challenge.History (Mandate.Challenge.fromHistory (B ready)) inputs claim) ∈ rows ready inputs
  pending : history.isPending (Mandate.Challenge.fromHistory (B ready)) inputs = true

def Request.target (request : Request ready inputs) : Mandate.Challenge.Target (Mandate.Challenge.fromHistory (B ready)) inputs request.original := by
  cases history : request.history with
  | pending target state slots => exact target
  | closed state archive slots => have impossible := request.pending; rw [history] at impossible; cases impossible

def request? : Option (Request ready inputs) :=
  match selected : (rows ready inputs).find? (fun row : Row ready inputs => row.2.isPending (Mandate.Challenge.fromHistory (B ready)) inputs) with
  | some row => some ⟨row.1, row.2, List.mem_of_find?_eq_some selected,
      List.find?_some (p := fun row : Row ready inputs => row.2.isPending (Mandate.Challenge.fromHistory (B ready)) inputs) selected⟩
  | none => none

def preamble (request : Request ready inputs) : List Action :=
  if (current ready inputs).technology = (request.target ready inputs).claim.snapshot (Mandate.Challenge.fromHistory (B ready)) inputs then []
  else [⟨request.original.signer (Mandate.Challenge.fromHistory (B ready)) inputs, [], ready.scope.challenge, [ready.scope.challenge], .present⟩]

inductive Method where
  | direct | productive | supplied
  deriving DecidableEq

structure Candidate where
  actor : Bool
  command : Command Bool
  method : Method

variable {inputs}

def Candidate.front (candidate : Candidate) (before : Current) : List Action :=
  match candidate.method with
  | .direct => []
  | .productive => [Exit.production candidate.actor]
  | .supplied =>
      let missing := 1 - before.stock candidate.actor .feedstock
      (if 0 < missing then
        [⟨!candidate.actor, [], .resource, [], .transfer (!candidate.actor) candidate.actor [(.feedstock, missing)]⟩] else []) ++
        [Exit.production candidate.actor]

def Candidate.word (candidate : Candidate) (before : Current) : List Action :=
  let front := candidate.front before
  front ++ [Mandate.request ready.scope ((epochLaw ready).execute before 0 front).final candidate.actor candidate.command]

variable (inputs)

def methods : List Method := [.direct, .productive, .supplied]

def menu : List Candidate :=
  (methods.flatMap fun method => (Delegation.members ready.scope.task).eraseDups.flatMap fun actor =>
    [⟨actor, .revoke, method⟩] ++ if ready.task.deadline < (current ready inputs).clock then [⟨actor, .review, method⟩] else []) ++
  ((current ready inputs).technology.holder.toList.flatMap fun holder => methods.map fun method => ⟨holder, .exit, method⟩)

def attempt (request : Request ready inputs) (candidate : Candidate) : List Action :=
  let first := preamble ready inputs request
  first ++ candidate.word ready ((epochLaw ready).execute (current ready inputs) 0 first).final

def Legal (request : Request ready inputs) (candidate : Candidate) : Prop :=
  Mandate.Response.Active (current ready inputs) ∧
  (∀ item ∈ (epochLaw ready).rawItems (current ready inputs) (attempt ready inputs request candidate),
    (epochLaw ready).Valid item.before item.request) ∧
  (((epochLaw ready).execute (current ready inputs) 0 (attempt ready inputs request candidate)).final.technology.holder = none ∧
   ((epochLaw ready).execute (current ready inputs) 0 (attempt ready inputs request candidate)).final.technology.offered = none)

instance (request : Request ready inputs) (candidate : Candidate) : Decidable (Legal ready inputs request candidate) := by
  unfold Legal Mandate.Response.Active; infer_instance

structure Paid (request : Request ready inputs) where
  private mk ::
  candidate : Candidate
  listed : candidate ∈ menu ready inputs
  legal : Legal ready inputs request candidate

def choose (request : Request ready inputs) : Option (Paid ready inputs request) :=
  match selected : (menu ready inputs).find? (fun candidate => decide (Legal ready inputs request candidate)) with
  | some candidate => some ⟨candidate, List.mem_of_find?_eq_some selected,
      of_decide_eq_true (List.find?_some (p := fun candidate => decide (Legal ready inputs request candidate)) selected)⟩
  | none => none

def fallback : Candidate := ⟨(Mandate.Response.firstMember ready.scope).val, .revoke, .supplied⟩

def word (request : Request ready inputs) : List Action :=
  attempt ready inputs request ((choose ready inputs request).map Paid.candidate |>.getD (fallback ready))

def emit := match request? ready inputs with | some request => word ready inputs request | none => []

theorem selected_word_is_actually_legal (request : Request ready inputs) (paid : Paid ready inputs request)
    (selected : choose ready inputs request = some paid) :
    Mandate.Response.Active (current ready inputs) ∧
    (∀ item ∈ (epochLaw ready).rawItems (current ready inputs) (word ready inputs request), (epochLaw ready).Valid item.before item.request) ∧
    (((epochLaw ready).execute (current ready inputs) 0 (word ready inputs request)).final.technology.holder = none ∧
      ((epochLaw ready).execute (current ready inputs) 0 (word ready inputs request)).final.technology.offered = none) := by
  simpa only [word, selected, Option.map_some, Option.getD_some, Legal] using paid.legal

theorem blocked_menu_has_actual_failed_checks (request : Request ready inputs) (blocked : choose ready inputs request = none) :
    ∀ candidate ∈ menu ready inputs, ¬ Legal ready inputs request candidate := by
  unfold choose at blocked
  split at blocked
  · cases blocked
  · rename_i absent
    intro candidate inside legal
    have denied := List.find?_eq_none.mp absent candidate inside
    rw [decide_eq_true legal] at denied
    exact denied rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending
