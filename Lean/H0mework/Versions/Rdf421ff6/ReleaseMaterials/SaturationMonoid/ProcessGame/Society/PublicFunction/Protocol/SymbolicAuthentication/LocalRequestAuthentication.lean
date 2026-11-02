import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestLocalDomain

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalRequestAuthentication

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (law : StageReception.Law code) (start : Cursor code) (installed : List (Rule code))

abbrev reading (entry : RequestLocalDomain.Entry (code := code)) (site : Fin code.sites) :=
  (EventStep.seed entry.cursor).frame.inbox site

def fibre (site : Fin code.sites) (signal : Fin code.signals) :=
  (RequestLocalDomain.domain vocabulary start installed).filter fun entry => reading entry site == signal

def claims (site : Fin code.sites) (entry : RequestLocalDomain.Entry (code := code)) :=
  entry.ledger.filter fun body => decide
    (RequestReadback.localRead (code := code) (reading entry site) = some body.request ∧
      body.ballot.scope = law.scope site (EventStep.seed entry.cursor).current)

def shared (site : Fin code.sites) : List (RequestLocalDomain.Entry (code := code)) →
    List (RequestAttestation.Statement (code := code))
  | [] => []
  | first :: rest => (claims law site first).eraseDups.filter fun body =>
      rest.all fun entry => decide (body ∈ claims law site entry)

inductive Status where
  | unseen | unauthenticated | authenticated
  deriving DecidableEq

structure ResultData (Body : Type) where
  status : Status
  possibilities : Nat
  statements : List Body
  deriving DecidableEq

abbrev Result := ResultData (RequestAttestation.Statement (code := code))

-- Only the fixed public source/rule prefix and the receiving site's signal enter
-- this compiler. Actual external choices and an actual-source certificate do not.
def generate (site : Fin code.sites) (signal : Fin code.signals) : Result (code := code) :=
  let compatible := fibre vocabulary start installed site signal
  let statements := shared law site compatible
  ⟨if compatible = [] then .unseen else if statements = [] then .unauthenticated else .authenticated,
    compatible.length, statements⟩

theorem shared_statements_hold_in_every_compatible_history
    (site : Fin code.sites) (entries : List (RequestLocalDomain.Entry (code := code)))
    (body : RequestAttestation.Statement (code := code)) (known : body ∈ shared law site entries)
    (entry : RequestLocalDomain.Entry (code := code)) (inside : entry ∈ entries) :
    body ∈ claims law site entry := by
  cases entries with
  | nil => simp only [shared, List.not_mem_nil] at known
  | cons first rest =>
    obtain ⟨initial, uniform⟩ := List.mem_filter.mp known
    rcases List.mem_cons.mp inside with same | later
    · exact same ▸ List.mem_eraseDups.mp initial
    · exact of_decide_eq_true ((List.all_eq_true.mp uniform) entry later)

theorem local_authentication_recovers_the_complete_actual_source_statement
    (stages : List (EventHistory.Stage (code := code))) (site : Fin code.sites)
    (body : RequestAttestation.Statement (code := code))
    (known : body ∈ (generate vocabulary law start (stages.map Prod.fst) site
      ((EventStep.seed (EventHistory.execute start stages)).frame.inbox site)).statements) :
    body ∈ RequestAttestation.ledger vocabulary start stages ∧
      RequestReadback.localRead (code := code) ((EventStep.seed (EventHistory.execute start stages)).frame.inbox site) = some body.request ∧
      body.ballot.scope = law.scope site (EventStep.seed (EventHistory.execute start stages)).current := by
  obtain ⟨entry, inside, matched, ledger⟩ := RequestLocalDomain.actual_prefix_coverage vocabulary start stages
  have member : entry ∈ fibre vocabulary start (stages.map Prod.fst) site
      ((EventStep.seed (EventHistory.execute start stages)).frame.inbox site) :=
    List.mem_filter.mpr ⟨inside, by simp only [reading, matched.state, beq_self_eq_true]⟩
  have received := shared_statements_hold_in_every_compatible_history law site _ body known entry member
  obtain ⟨valid, property⟩ := List.mem_filter.mp received
  rw [ledger] at valid
  obtain ⟨read, scope⟩ := of_decide_eq_true property
  exact ⟨valid, by simpa only [reading, matched.state] using read,
    by simpa only [matched.state] using scope⟩

def work (site : Fin code.sites) (signal : Fin code.signals) :=
  if (generate vocabulary law start installed site signal).statements = [] then []
  else RequestResponse.work site signal

theorem work_supported (site : Fin code.sites) (signal : Fin code.signals) :
    work vocabulary law start installed site signal ∈ words code.actions code.actionLimit := by
  unfold work
  split
  · exact (mem_words_iff _ _ _).mpr (by simp)
  · exact RequestResponse.work_supported _ _

def policy : code.Policy := fun key _ => work vocabulary law start installed key.1 key.2

theorem policy_generated : policy vocabulary law start installed ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key _
  exact work_supported vocabulary law start installed key.1 key.2

def protocol : Rule code where
  work := ⟨policy vocabulary law start installed, policy_generated vocabulary law start installed⟩
  events := fun key _ => if work vocabulary law start installed key.1 key.2 = [] then
    ⟨none, List.mem_cons_self⟩ else RequestResponse.activation key.1

theorem an_owned_activation_submits_the_locally_authenticated_word
    (past : List (EventHistory.Stage (code := code))) (rival : Opponent code) (site : Fin code.sites)
    (owned : StageTrace.activation (StageTrace.material (EventHistory.execute start past)
      (protocol vocabulary law start (past.map Prod.fst)) rival) = some site) :
    (StageTrace.material (EventHistory.execute start past) (protocol vocabulary law start (past.map Prod.fst)) rival).submitted =
      work vocabulary law start (past.map Prod.fst) site
        ((EventStep.seed (EventHistory.execute start past)).frame.inbox site) := by
  rw [(StageTrace.an_owned_activation_submits_its_selected_work _ _ rival site owned).2]
  change (if code.memoryReady _ then work vocabulary law start _ site _ else []) = _
  split
  · rfl
  · rename_i unreadable
    unfold work
    split
    · rfl
    · exact (RequestResponse.missing_local_content_produces_no_work site _ (by
        simp [RequestReadback.localRead, unreadable])).symm

theorem nonempty_work_requires_an_actual_owned_paid_source_statement
    (stages : List (EventHistory.Stage (code := code))) (site : Fin code.sites)
    (needed : work vocabulary law start (stages.map Prod.fst) site
      ((EventStep.seed (EventHistory.execute start stages)).frame.inbox site) ≠ []) :
    ∃ body ∈ RequestAttestation.ledger vocabulary start stages,
      RequestReadback.localRead (code := code) ((EventStep.seed (EventHistory.execute start stages)).frame.inbox site) = some body.request ∧
      body.ballot.scope = law.scope site (EventStep.seed (EventHistory.execute start stages)).current := by
  unfold work at needed
  split at needed
  · contradiction
  · rename_i present
    obtain ⟨body, inside⟩ := List.exists_mem_of_ne_nil _ present
    exact ⟨body, local_authentication_recovers_the_complete_actual_source_statement vocabulary law start stages site body inside⟩

def run (rival : Opponent code) : Nat → List (EventHistory.Stage (code := code)) → List (EventHistory.Stage (code := code))
  | 0, past => past
  | rounds + 1, past =>
    if (EventStep.seed (EventHistory.execute start past)).remaining = 0 then past
    else run rival rounds (past ++ [(protocol vocabulary law start (past.map Prod.fst), rival)])

def produce (past : List (EventHistory.Stage (code := code))) (rival : Opponent code) :=
  run vocabulary law start rival (EventStep.seed (EventHistory.execute start past)).remaining past

theorem the_actual_local_authentication_run_preserves_every_original_stage
    (rival : Opponent code) (rounds : Nat) (past : List (EventHistory.Stage (code := code))) :
    past <+: run vocabulary law start rival rounds past := by
  induction rounds generalizing past with
  | zero => exact List.prefix_refl _
  | succ rounds ih =>
    simp only [run]
    split
    · exact List.prefix_refl _
    · exact (List.prefix_append _ _).trans (ih _)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalRequestAuthentication
