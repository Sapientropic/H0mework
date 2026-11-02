import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceivedLocalDomain

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalReceiptAuthentication

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code) (start : Cursor code) (installed : List (Rule code))

abbrev reading (trace : List (EventHistory.Stage (code := code))) (site : Fin code.sites) :=
  (EventStep.seed (EventHistory.execute start trace)).frame.inbox site

def fibre (site : Fin code.sites) (signal : Fin code.signals) :=
  (ReceivedLocalDomain.domain start installed).filter fun trace => reading start trace site == signal

def claims (count : Nat) (site : Fin code.sites) (trace : List (EventHistory.Stage (code := code))) :=
  (RequestReadback.produce vocabulary encoding law start trace site count).receipts.filter fun receipt => decide
    (RequestReadback.localRead (code := code) (reading start trace site) = some receipt.statement.request ∧
      receipt.statement.ballot.scope = law.scope site (EventStep.seed (EventHistory.execute start trace)).current)

def shared (count : Nat) (site : Fin code.sites) : List (List (EventHistory.Stage (code := code))) →
    List (RequestReadback.Receipt (code := code))
  | [] => []
  | first :: rest => (claims vocabulary encoding law start count site first).eraseDups.filter fun receipt =>
      rest.all fun trace => decide (receipt ∈ claims vocabulary encoding law start count site trace)

structure ResultData (Body : Type) where
  status : LocalRequestAuthentication.Status
  possibilities : Nat
  receipts : List Body
  deriving DecidableEq

abbrev Result := ResultData (RequestReadback.Receipt (code := code))

-- Public configuration and the current local signal are the entire query input.
-- Complete receipt metadata must survive every compatible communication history.
def generate (site : Fin code.sites) (signal : Fin code.signals) : Result (code := code) :=
  let compatible := fibre start installed site signal
  let receipts := shared vocabulary encoding law start installed.length site compatible
  ⟨if compatible = [] then .unseen else if receipts = [] then .unauthenticated else .authenticated,
    compatible.length, receipts⟩

theorem shared_receipts_hold_in_every_compatible_history
    (count : Nat) (site : Fin code.sites) (traces : List (List (EventHistory.Stage (code := code))))
    (receipt : RequestReadback.Receipt (code := code)) (known : receipt ∈ shared vocabulary encoding law start count site traces)
    (trace : List (EventHistory.Stage (code := code))) (inside : trace ∈ traces) :
    receipt ∈ claims vocabulary encoding law start count site trace := by
  cases traces with
  | nil => simp only [shared, List.not_mem_nil] at known
  | cons first rest =>
    obtain ⟨initial, uniform⟩ := List.mem_filter.mp known
    rcases List.mem_cons.mp inside with same | later
    · exact same ▸ List.mem_eraseDups.mp initial
    · exact of_decide_eq_true ((List.all_eq_true.mp uniform) trace later)

theorem local_receipt_authentication_recovers_the_actual_paid_delivery
    (stages : List (EventHistory.Stage (code := code))) (site : Fin code.sites)
    (receipt : RequestReadback.Receipt (code := code))
    (known : receipt ∈ (generate vocabulary encoding law start (stages.map Prod.fst) site
      ((EventStep.seed (EventHistory.execute start stages)).frame.inbox site)).receipts) :
    receipt ∈ (RequestReadback.produce vocabulary encoding law start stages site stages.length).receipts ∧
      RequestReadback.localRead (code := code) ((EventStep.seed (EventHistory.execute start stages)).frame.inbox site) = some receipt.statement.request ∧
      receipt.statement.ballot.scope = law.scope site (EventStep.seed (EventHistory.execute start stages)).current := by
  obtain ⟨trace, inside, matched, receipts⟩ := ReceivedLocalDomain.generated_representative_preserves_every_real_receipt
    start vocabulary encoding law stages
  have member : trace ∈ fibre start (stages.map Prod.fst) site
      ((EventStep.seed (EventHistory.execute start stages)).frame.inbox site) :=
    List.mem_filter.mpr ⟨inside, by simp only [reading, matched.state, beq_self_eq_true]⟩
  have received := shared_receipts_hold_in_every_compatible_history vocabulary encoding law start
    (stages.map Prod.fst).length site _ receipt known trace member
  obtain ⟨valid, property⟩ := List.mem_filter.mp received
  simp only [List.length_map, receipts] at valid
  obtain ⟨read, scope⟩ := of_decide_eq_true property
  exact ⟨valid, by simpa only [reading, matched.state] using read,
    by simpa only [matched.state] using scope⟩

def work (site : Fin code.sites) (signal : Fin code.signals) :=
  if (generate vocabulary encoding law start installed site signal).receipts = [] then []
  else RequestResponse.work site signal

theorem work_supported (site : Fin code.sites) (signal : Fin code.signals) :
    work vocabulary encoding law start installed site signal ∈ words code.actions code.actionLimit := by
  unfold work
  split
  · exact (mem_words_iff _ _ _).mpr (by simp)
  · exact RequestResponse.work_supported _ _

def policy : code.Policy := fun key _ => work vocabulary encoding law start installed key.1 key.2

theorem policy_generated : policy vocabulary encoding law start installed ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key _
  exact work_supported vocabulary encoding law start installed key.1 key.2

def protocol : Rule code where
  work := ⟨policy vocabulary encoding law start installed, policy_generated vocabulary encoding law start installed⟩
  events := fun key _ => if work vocabulary encoding law start installed key.1 key.2 = [] then
    ⟨none, List.mem_cons_self⟩ else RequestResponse.activation key.1

theorem an_owned_activation_submits_the_locally_authenticated_word
    (past : List (EventHistory.Stage (code := code))) (rival : Opponent code) (site : Fin code.sites)
    (owned : StageTrace.activation (StageTrace.material (EventHistory.execute start past)
      (protocol vocabulary encoding law start (past.map Prod.fst)) rival) = some site) :
    (StageTrace.material (EventHistory.execute start past) (protocol vocabulary encoding law start (past.map Prod.fst)) rival).submitted =
      work vocabulary encoding law start (past.map Prod.fst) site
        ((EventStep.seed (EventHistory.execute start past)).frame.inbox site) := by
  rw [(StageTrace.an_owned_activation_submits_its_selected_work _ _ rival site owned).2]
  change (if code.memoryReady _ then work vocabulary encoding law start _ site _ else []) = _
  split
  · rfl
  · rename_i unreadable
    unfold work
    split
    · rfl
    · exact (RequestResponse.missing_local_content_produces_no_work site _ (by
        simp [RequestReadback.localRead, unreadable])).symm

theorem nonempty_work_requires_an_actual_paid_communication_receipt
    (stages : List (EventHistory.Stage (code := code))) (site : Fin code.sites)
    (needed : work vocabulary encoding law start (stages.map Prod.fst) site
      ((EventStep.seed (EventHistory.execute start stages)).frame.inbox site) ≠ []) :
    ∃ receipt ∈ (RequestReadback.produce vocabulary encoding law start stages site stages.length).receipts,
      RequestReadback.localRead (code := code) ((EventStep.seed (EventHistory.execute start stages)).frame.inbox site) = some receipt.statement.request ∧
      receipt.statement.ballot.scope = law.scope site (EventStep.seed (EventHistory.execute start stages)).current := by
  unfold work at needed
  split at needed
  · contradiction
  · rename_i present
    obtain ⟨receipt, inside⟩ := List.exists_mem_of_ne_nil _ present
    exact ⟨receipt, local_receipt_authentication_recovers_the_actual_paid_delivery vocabulary encoding law start stages site receipt inside⟩

def run (rival : Opponent code) : Nat → List (EventHistory.Stage (code := code)) → List (EventHistory.Stage (code := code))
  | 0, past => past
  | rounds + 1, past =>
    if (EventStep.seed (EventHistory.execute start past)).remaining = 0 then past
    else run rival rounds (past ++ [(protocol vocabulary encoding law start (past.map Prod.fst), rival)])

def produce (past : List (EventHistory.Stage (code := code))) (rival : Opponent code) :=
  run vocabulary encoding law start rival (EventStep.seed (EventHistory.execute start past)).remaining past

theorem the_actual_local_authentication_run_preserves_every_original_stage
    (rival : Opponent code) (rounds : Nat) (past : List (EventHistory.Stage (code := code))) :
    past <+: run vocabulary encoding law start rival rounds past := by
  induction rounds generalizing past with
  | zero => exact List.prefix_refl _
  | succ rounds ih =>
    simp only [run]
    split
    · exact List.prefix_refl _
    · exact (List.prefix_append _ _).trans (ih _)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalReceiptAuthentication
