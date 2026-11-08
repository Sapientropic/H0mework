import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelReentryCongruence

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 240000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelReentryConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open FuelControlSource FuelControlDomain

structure Result (control : Controller) (rivals : Nat → Opponent code) : Type where
  private mk ::
  first : Node
  first_exact : first = FuelControlConsumer.finished control rivals
  next : MaterialRoundConsumer.Result (FuelReentrySource.bound first.cursor) first.cursor.cut (FuelReentrySource.incoming first.cursor)
  next_exact : next = FuelReentrySource.produce first.cursor

def produce (control : Controller) (rivals : Nat → Opponent code) : Result control rivals :=
  ⟨FuelControlConsumer.finished control rivals,rfl,FuelReentrySource.produce (FuelControlConsumer.finished control rivals).cursor,rfl⟩

def check (node : Node) : Bool := decide (FuelReentrySource.status node.cursor = .decided true)
def checkAll : Nat → Node → Bool :=
  Nat.rec check fun _ recur node => (controls node).all fun requested =>
    (choices node).all fun move => recur (step node requested (EventStep.fixed move))

theorem every_source_generated_first_window_generates_a_new_paid_round : checkAll window initial = true := by
  decide +kernel

theorem generated_prefix_keeps_its_remaining_check
    (count remaining : Nat) (node : Node) (member : node ∈ generate count)
    (passed : checkAll (count+remaining) initial = true) : checkAll remaining node = true := by
  induction count generalizing remaining node with
  | zero => cases List.mem_singleton.mp member;simpa only [Nat.zero_add] using passed
  | succ count ih =>
    obtain ⟨before,inside,next⟩ := List.mem_flatMap.mp member
    obtain ⟨requested,selected,rest⟩ := List.mem_flatMap.mp next
    obtain ⟨move,allowed,rfl⟩ := List.mem_map.mp rest
    have previous := ih (remaining+1) before inside (by simpa only [Nat.add_assoc,Nat.add_comm 1] using passed)
    exact List.all_eq_true.mp (List.all_eq_true.mp previous requested selected) move allowed

theorem every_actual_compliant_first_window_generates_its_own_new_paid_round
    (control : Controller) (rivals : Nat → Opponent code) (within : Within control rivals window) :
    FuelReentrySource.status (produce control rivals).first.cursor = .decided true := by
  obtain ⟨node,member,same⟩ := every_actual_joint_controller_has_a_generated_source_branch control rivals window within
  have one := generated_valid window node member
  have two := actual_valid control rivals window
  have passed : check node = true := generated_prefix_keeps_its_remaining_check window 0 node member
    (by simpa only [Nat.add_zero] using every_source_generated_first_window_generates_a_new_paid_round)
  have matched : EventStep.Matches node.cursor (FuelControlConsumer.finished control rivals).cursor := by
    rw [one.1,two.1]
    exact same.1.1
  have moved := FuelReentryCongruence.source_generated_next_round_status_is_preserved _ _ matched
  rw [check,decide_eq_true_eq] at passed
  exact moved.symm.trans passed

theorem the_first_actual_attempts_and_their_complete_evidence_are_retained
    (control : Controller) (rivals : Nat → Opponent code) :
    (produce control rivals).first = FuelControlConsumer.finished control rivals ∧
      (produce control rivals).next = FuelReentrySource.produce (produce control rivals).first.cursor := ⟨rfl,rfl⟩

private theorem completed_status_has_its_actual_generated_entry (cursor : Cursor code)
    (done : FuelReentrySource.status cursor = .decided true) :
    ∃ entry : MaterialRoundSource.Ready (FuelReentrySource.bound cursor) cursor.cut (FuelReentrySource.incoming cursor),
      MaterialRoundSource.inspect (FuelReentrySource.bound cursor) cursor.cut (FuelReentrySource.incoming cursor) = some entry ∧
      ∃ subject, MaterialRoundSource.outcome (FuelReentrySource.bound cursor) cursor.cut (FuelReentrySource.incoming cursor) entry = .decided true subject := by
  unfold FuelReentrySource.status FuelMaterialSource.status MaterialRoundConsumer.status MaterialRoundConsumer.produce at done
  cases generated : MaterialRoundSource.inspect (FuelReentrySource.bound cursor) cursor.cut (FuelReentrySource.incoming cursor) with
  | none =>
    simp only [generated,Option.map_none] at done
    split at done <;> contradiction
  | some entry =>
    simp only [generated,Option.map_some] at done
    cases outcome : MaterialRoundSource.outcome (FuelReentrySource.bound cursor) cursor.cut (FuelReentrySource.incoming cursor) entry with
    | blocked reason => simp only [outcome] at done;contradiction
    | decided value subject =>
      simp only [outcome,MaterialRoundConsumer.Status.decided.injEq] at done
      cases done
      exact ⟨entry,rfl,subject,outcome⟩

theorem every_compliant_actual_reentry_consumes_its_new_payment_whole_ledger_and_next
    (control : Controller) (rivals : Nat → Opponent code) (within : Within control rivals window) :
    let cursor := (produce control rivals).first.cursor
    let old := FuelReentrySource.bound cursor
    let arrival := FuelReentrySource.incoming cursor
    ∃ entry : MaterialRoundSource.Ready old cursor.cut arrival,
      MaterialRoundSource.inspect old cursor.cut arrival = some entry ∧
      ∃ subject, MaterialRoundSource.outcome old cursor.cut arrival entry = .decided true subject ∧
      let consumed := ControlResponsibility.produce entry.bound (MaterialRoundSource.input old cursor.cut arrival entry) 0
        (MaterialRoundSource.protocol old cursor.cut arrival entry) (MaterialRoundSource.environment old cursor.cut arrival entry)
        (MaterialRoundSource.vocabulary old cursor.cut arrival entry) (MaterialRoundSource.encoding old cursor.cut arrival entry)
        (MaterialRoundSource.reception old cursor.cut arrival entry) rfl 0
      let runtime := ControlResponsibility.runtime entry.bound (MaterialRoundSource.input old cursor.cut arrival entry) 0
        (MaterialRoundSource.protocol old cursor.cut arrival entry) (MaterialRoundSource.environment old cursor.cut arrival entry)
        (MaterialRoundSource.vocabulary old cursor.cut arrival entry) (MaterialRoundSource.encoding old cursor.cut arrival entry)
        (MaterialRoundSource.reception old cursor.cut arrival entry) rfl 0
      (∃ item, (item,true) ∈ consumed.requests ∧ 0 < subject.2.amount ∧
        flowAt ((MaterialRoundSource.code old cursor.cut arrival entry).law.actualDebit item.before item.request) subject.2.debtor subject.2.unit = subject.2.amount ∧
        flowAt ((MaterialRoundSource.code old cursor.cut arrival entry).law.actualCredit item.before item.request) subject.2.creditor subject.2.unit = subject.2.amount ∧
        ((MaterialRoundSource.code old cursor.cut arrival entry).law.step item.before item.request).claims subject.2.instrument subject.2.debtor subject.2.creditor = subject.2.priorClaim-subject.2.quantity) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (CommunicationRuntime.facade entry.bound (MaterialRoundSource.input old cursor.cut arrival entry) 0
        (MaterialRoundSource.protocol old cursor.cut arrival entry) (MaterialRoundSource.environment old cursor.cut arrival entry)
        (MaterialRoundSource.vocabulary old cursor.cut arrival entry) (MaterialRoundSource.encoding old cursor.cut arrival entry)
        (MaterialRoundSource.reception old cursor.cut arrival entry) rfl).process.stateAt
          ((CommunicationRuntime.facade entry.bound (MaterialRoundSource.input old cursor.cut arrival entry) 0
            (MaterialRoundSource.protocol old cursor.cut arrival entry) (MaterialRoundSource.environment old cursor.cut arrival entry)
            (MaterialRoundSource.vocabulary old cursor.cut arrival entry) (MaterialRoundSource.encoding old cursor.cut arrival entry)
            (MaterialRoundSource.reception old cursor.cut arrival entry) rfl).process.successor runtime.state) := by
  obtain ⟨entry,generated,subject,done⟩ := completed_status_has_its_actual_generated_entry _
    (every_actual_compliant_first_window_generates_its_own_new_paid_round control rivals within)
  exact ⟨entry,generated,subject,done,
    MaterialRoundConsumer.every_completed_new_round_consumes_its_entire_payment_responsibility_and_next
      _ _ _ entry true subject done⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelReentryConsumer
