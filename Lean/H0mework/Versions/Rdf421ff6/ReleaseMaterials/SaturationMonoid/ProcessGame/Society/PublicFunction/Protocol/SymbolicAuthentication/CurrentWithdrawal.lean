import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JournalWindow

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CurrentWithdrawal

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (past : List (EventHistory.Stage (code := model.source.code)))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

abbrev current := EventHistory.execute start past
abbrev journal := IncidentResponse.journal model start past vocabulary encoding law
abbrev Candidate := {answer // answer ∈ journal model start past vocabulary encoding law}

def delay (answer : IncidentResponse.Answer model start vocabulary encoding law) :=
  SilentWindow.delay (current model start past) answer.response.incident.receiver

def waiting (answer : IncidentResponse.Answer model start vocabulary encoding law) :=
  if delay model start past vocabulary encoding law answer < (EventStep.seed (current model start past)).remaining then
    past ++ SilentWindow.stages (delay model start past vocabulary encoding law answer)
  else past

-- Each candidate is checked at its own source-generated arrival, never at the head's owner.
def check (candidate : Candidate model start past vocabulary encoding law) :
    IncidentWithdrawal.Plan model start (waiting model start past vocabulary encoding law candidate.val) vocabulary encoding law :=
  if enough : delay model start past vocabulary encoding law candidate.val < (EventStep.seed (current model start past)).remaining then
    IncidentWithdrawal.Candidates.inspect model start (waiting model start past vocabulary encoding law candidate.val)
      vocabulary encoding law candidate.val (by
        rw [waiting, if_pos enough]
        exact (IncidentResponse.Prefix.journal_is_an_actual_prefix model start vocabulary encoding law past _).subset candidate.property)
  else .blocked .exhausted

abbrev Checked := Sigma fun candidate : Candidate model start past vocabulary encoding law =>
  IncidentWithdrawal.Plan model start (waiting model start past vocabulary encoding law candidate.val) vocabulary encoding law

def reports : List (Checked model start past vocabulary encoding law) :=
  (journal model start past vocabulary encoding law).attach.map fun candidate => ⟨candidate, check model start past vocabulary encoding law candidate⟩

def isPaid (entry : Checked model start past vocabulary encoding law) : Bool := match entry.2 with
  | .paid _ _ => true
  | _ => false

def isRefused (entry : Checked model start past vocabulary encoding law) : Bool := match entry.2 with
  | .refused _ _ => true
  | _ => false

-- A stale or refused earlier response cannot conceal a reachable paid response.
def produce : Option (Checked model start past vocabulary encoding law) :=
  match (reports model start past vocabulary encoding law).find? (isPaid model start past vocabulary encoding law) with
  | some paid => some paid
  | none => match (reports model start past vocabulary encoding law).find? (isRefused model start past vocabulary encoding law) with
    | some refused => some refused
    | none => (reports model start past vocabulary encoding law).head?

def stages (rival : Opponent model.source.code) :=
  match produce model start past vocabulary encoding law with
  | none => past
  | some ⟨candidate, plan⟩ =>
    let arrival := waiting model start past vocabulary encoding law candidate.val
    match plan with
    | .paid ready _ | .refused ready _ => arrival ++ [(IncidentWithdrawal.protocol model start arrival vocabulary encoding law ready, rival)]
    | _ => arrival

theorem no_journal_entry_is_discarded :
    (reports model start past vocabulary encoding law).length = (journal model start past vocabulary encoding law).length := by
  simp [reports]

theorem every_original_response_has_its_own_report (candidate : Candidate model start past vocabulary encoding law) :
    ⟨candidate, check model start past vocabulary encoding law candidate⟩ ∈ reports model start past vocabulary encoding law := by
  apply List.mem_map.mpr
  exact ⟨candidate, List.mem_attach _ _, rfl⟩

theorem a_paid_candidate_cannot_be_hidden
    (entry : Checked model start past vocabulary encoding law)
    (actual : entry ∈ reports model start past vocabulary encoding law)
    (paid : isPaid model start past vocabulary encoding law entry = true) :
    ∃ selected, produce model start past vocabulary encoding law = some selected ∧
      selected ∈ reports model start past vocabulary encoding law ∧
      isPaid model start past vocabulary encoding law selected = true := by
  unfold produce
  split
  · rename_i selected found
    exact ⟨selected, rfl, List.mem_of_find?_eq_some found, List.find?_some found⟩
  · rename_i absent
    have denied := List.find?_eq_none.mp absent entry actual
    rw [paid] at denied
    contradiction

variable (candidate : Candidate model start past vocabulary encoding law)
  (ready : IncidentWithdrawal.Ready model start (waiting model start past vocabulary encoding law candidate.val) vocabulary encoding law)

theorem paid_appends_the_selected_actual_attempt (rival : Opponent model.source.code)
    (accepted : model.source.code.law.Valid
      (EventStep.seed (EventHistory.execute start (waiting model start past vocabulary encoding law candidate.val))).current
      (IncidentWithdrawal.action model start (waiting model start past vocabulary encoding law candidate.val) vocabulary encoding law ready.answer))
    (selected : produce model start past vocabulary encoding law = some ⟨candidate, .paid ready accepted⟩) :
    stages model start past vocabulary encoding law rival =
      waiting model start past vocabulary encoding law candidate.val ++
        [(IncidentWithdrawal.protocol model start (waiting model start past vocabulary encoding law candidate.val) vocabulary encoding law ready, rival)] := by
  simp only [stages, selected]

theorem refused_appends_the_selected_actual_attempt (rival : Opponent model.source.code)
    (denied : ¬model.source.code.law.Valid
      (EventStep.seed (EventHistory.execute start (waiting model start past vocabulary encoding law candidate.val))).current
      (IncidentWithdrawal.action model start (waiting model start past vocabulary encoding law candidate.val) vocabulary encoding law ready.answer))
    (selected : produce model start past vocabulary encoding law = some ⟨candidate, .refused ready denied⟩) :
    stages model start past vocabulary encoding law rival =
      waiting model start past vocabulary encoding law candidate.val ++
        [(IncidentWithdrawal.protocol model start (waiting model start past vocabulary encoding law candidate.val) vocabulary encoding law ready, rival)] := by
  simp only [stages, selected]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CurrentWithdrawal
