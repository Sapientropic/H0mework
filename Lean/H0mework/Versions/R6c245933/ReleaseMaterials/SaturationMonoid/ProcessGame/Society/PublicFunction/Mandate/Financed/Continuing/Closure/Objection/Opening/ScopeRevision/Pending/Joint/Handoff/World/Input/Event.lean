import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Trace
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Replacement.Runtime.Readback

/-! A real primitive event updates the whole inventory before its autonomous
response. Every decision retains a replayable native evolution and original finance. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch) (word : List Action)
def observed := World.submit inventory word

theorem observed_current_is_raw_next : current epoch (observed inventory word).inputs =
 (Mandate.law base epoch.scope).next (current epoch inventory.inputs) word := by
 have after := (World.actual inventory word).after_exact
 change current epoch (observed inventory word).inputs = _
 have same : (World.actual inventory word).after = current epoch (observed inventory word).inputs := by
  simpa only [World.actual,observed,World.submit,current,List.length_append,List.length_singleton,Nat.add_assoc,Nat.reduceAdd] using
   OutstandingSource.History.actual_next epoch.source (World.submit inventory word).inputs (inventory.inputs.length+1)
 rw [same] at after
 change current epoch (observed inventory word).inputs = (Mandate.law base epoch.scope).next (World.actual inventory word).before (World.actual inventory word).submitted at after
 rw [(World.actual_word_and_cut inventory word).1,(World.actual_word_and_cut inventory word).2] at after
 exact after
def response := Replacement.Runtime.fromRoot (observed inventory word)
def packet := (response inventory word).packet

def evolution : Evolution ⟨epoch,inventory⟩ (packet inventory word) :=
  .append (.submit inventory word) (completionEvolution (response inventory word).original.decision)

def financialRun : (Financial.Family.process sources).Run inventory.finance.current (packet inventory word).2.finance.current :=
  (World.financialRun inventory word).concatRuns _ (response inventory word).financialRun

def incomingInResponse := OutstandingSource.History.actualExecution epoch.source
  (Programme.produce (observed inventory word)).finalInventory.inputs (inventory.inputs.length+1)

theorem incoming_event_is_in_the_actual_response_source :
    (incomingInResponse inventory word).submitted = word ∧
    (incomingInResponse inventory word).before = current epoch inventory.inputs := by
  obtain ⟨suffix,same⟩ := (Programme.produce (observed inventory word)).inputs_extend_the_saved_history (observed inventory word)
  unfold incomingInResponse
  rw [← same]
  change (OutstandingSource.History.actualExecution epoch.source ((inventory.inputs ++ [word]) ++ suffix)
    (inventory.inputs.length+1)).submitted = word ∧ _
  constructor
  · rw [OutstandingSource.History.scheduled_input_is_actual epoch.source _ inventory.inputs.length (by simp)]
    simp
  · change OutstandingSource.History.currentAt epoch.source ((inventory.inputs ++ [word]) ++ suffix) (inventory.inputs.length+2) = _
    rw [(OutstandingSource.History.actual_frame _ _ _).1,List.append_assoc,
      OutstandingSource.History.extending_inputs_preserves_its_executed_prefix epoch.source inventory.inputs ([word] ++ suffix) _ (Nat.le_refl _)]
    exact (OutstandingSource.History.actual_frame epoch.source inventory.inputs _).1.symm

structure Disposition where
  private mk ::
  original : Replacement.Disposition (observed inventory word)
  original_exact : original = response inventory word
  native : Evolution ⟨epoch,inventory⟩ original.packet
  finance : (Financial.Family.process sources).Run inventory.finance.current original.packet.2.finance.current

def produce : Disposition inventory word := ⟨response inventory word,rfl,evolution inventory word,financialRun inventory word⟩

variable {inventory word}
def Disposition.packet (result : Disposition inventory word) := result.original.packet

theorem Disposition.paid_response_has_one_actual_four_port_path (result : Disposition inventory word)
    (paid : result.original.original.decision.kind = .paid) :
    ∃ next : Programme.Completion.PaidNext (Programme.produce (observed inventory word)),
      result.packet = next.packet ∧
      Nonempty (Handoff.PaidOpening next.fresh (Handoff.actual next.fresh 1).before (Handoff.actual next.fresh 1).submitted) := by
  dsimp only [Disposition.packet,Replacement.Disposition.packet,Programme.Completion.Disposition.packet]
  generalize actual : result.original.original.decision = decision at paid ⊢
  cases decision
  next next => exact ⟨next,rfl,⟨next.opening⟩⟩
  next absent reason => cases paid
  next fresh chosen absent failure methods => cases paid

def Disposition.grant (result : Disposition inventory word) (entry : GrantCohort)
    (member : entry ∈ inventory.pastGrants) : GrantTransport entry result.packet := result.native.grant entry member

def Disposition.challenge (result : Disposition inventory word) (entry : ChallengeCohort epoch.scope)
    (member : entry ∈ inventory.pastChallenges) : ChallengeTransport entry result.packet := result.native.challenge entry member

def Disposition.service (result : Disposition inventory word) (entry : ServiceCohort epoch.source.seed.initial.clock)
    (member : entry ∈ inventory.pastServices) : ServiceTransport entry result.packet := result.native.service entry member

def Disposition.originalGrants (result : Disposition inventory word) (entry : GrantCohort) (member : entry ∈ inventory.pastGrants) :=
  (result.grant entry member).extension.complete

def Disposition.originalChallenges (result : Disposition inventory word) (entry : ChallengeCohort epoch.scope)
    (member : entry ∈ inventory.pastChallenges) := (result.challenge entry member).extension.complete

def Disposition.originalServices (result : Disposition inventory word) (entry : ServiceCohort epoch.source.seed.initial.clock)
    (member : entry ∈ inventory.pastServices) := (result.service entry member).extension.complete

variable (inventory word)
def next := (produce inventory word).packet

def run (packet : Packet) : List (List Action) → Packet
  | [] => packet
  | word :: tail => run (next packet.2 word) tail

def runEvolution (packet : Packet) : (history : List (List Action)) → Evolution packet (run packet history)
  | [] => .same _
  | word :: tail => .append (produce packet.2 word).native (runEvolution (next packet.2 word) tail)

def runFinance (packet : Packet) : (history : List (List Action)) →
    (Financial.Family.process sources).Run packet.2.finance.current (run packet history).2.finance.current
  | [] => .nil
  | word :: tail => (produce packet.2 word).finance.concatRuns _ (runFinance (next packet.2 word) tail)

theorem run_append (packet : Packet) (earlier later : List (List Action)) :
    run packet (earlier ++ later) = run (run packet earlier) later := by
  induction earlier generalizing packet with
  | nil => rfl
  | cons word tail ih => exact ih (next packet.2 word)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event


namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section

/-- The response and its actual evolution consume one generated disposition. -/
def produceShared {epoch : Epoch} (inventory : Inventory epoch) (word : List Action) : Disposition inventory word :=
  let actual := response inventory word
  ⟨actual,rfl,
    .append (.submit inventory word) (completionEvolution actual.original.decision),
    (World.financialRun inventory word).concatRuns _ actual.financialRun⟩

@[csimp] theorem produce_eq_shared : @produce = @produceShared := by
  funext epoch inventory word
  rfl

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event
