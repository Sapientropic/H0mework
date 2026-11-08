import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointReceivedRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResponseCapacity

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

-- These are finite source transition laws, independent of validity, motives,
-- the scheduler, authentication results, and any proposed completion certificate.
structure Absorbing (code : Code Party Good Port (Mandate.State Party Technology) Instrument) : Prop where
  action : ∀ site old word, word ∈ words code.actions code.actionLimit →
    code.memoryReady (code.afterAction site old word) = false
  send : ∀ sender recipient old reading, code.memoryReady old = false →
    code.memoryReady (code.afterSend sender recipient old reading) = false
  delivery : ∀ recipient sender old reading, code.memoryReady old = false →
    code.memoryReady (code.afterDelivery recipient sender old reading) = false

omit [DecidableEq Port] [DecidableEq Technology] in
theorem generated_action_is_in_the_source_alphabet (policy : code.Policy) (generated : policy ∈ code.policies)
    (site : Fin code.sites) (signal : Fin code.signals) :
    code.action policy site signal ∈ words code.actions code.actionLimit := by
  unfold Code.action
  split
  · exact ((List.mem_pi _ _).mp generated) (site, signal) (code.key_mem _)
  · exact (mem_words_iff _ _ _).mpr (by simp)

def available (frame : code.Frame) : Finset (Fin code.sites) :=
  Finset.univ.filter fun site => code.memoryReady (frame.inbox site) = true

def rank (cursor : Cursor code) : Nat := (available (EventStep.seed cursor).frame).card

omit [DecidableEq Port] [DecidableEq Technology] in
theorem an_actual_event_cannot_refill_consumed_memory (source : Absorbing code)
    (policy : code.Policy) (generated : policy ∈ code.policies) (initial : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
    (frame : code.Frame) (event : Event Party Good Port (Mandate.State Party Technology) Instrument code.sites)
    (site : Fin code.sites) (spent : code.memoryReady (frame.inbox site) = false) :
    code.memoryReady ((code.step policy initial frame event).inbox site) = false := by
  cases event with
  | adversary request => exact spent
  | send sender recipient =>
    simp only [Code.step]
    split
    · dsimp only
      split
      · rename_i same; subst site; exact source.send _ _ _ _ spent
      · exact spent
    · exact spent
  | deliver address =>
    simp only [Code.step]
    split
    · exact spent
    · split
      · dsimp only
        split
        · exact source.delivery _ _ _ _ spent
        · exact spent
      · exact spent
  | activate worker =>
    simp only [Code.step]
    split
    · exact source.action _ _ _ (generated_action_is_in_the_source_alphabet policy generated _ _)
    · exact spent

theorem every_actual_cut_preserves_consumed_memory (source : Absorbing code)
    (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code)
    (site : Fin code.sites) (spent : code.memoryReady ((EventStep.seed cursor).frame.inbox site) = false) :
    code.memoryReady ((EventStep.seed (cursor.after protocol rival)).frame.inbox site) = false := by
  rw [EventStep.actual_next_state]
  cases chosen : decision code (EventStep.applied cursor protocol rival) (EventStep.seed cursor) with
  | none => simpa only [Reaction.Feedback.advance, chosen] using spent
  | some event =>
    simpa only [Reaction.Feedback.advance, chosen, stepLocal] using
      an_actual_event_cannot_refill_consumed_memory source protocol.work.val protocol.work.property
      (EventStep.seed cursor).current { (EventStep.seed cursor).frame with word := [] } event.val site spent

theorem actual_capacity_never_increases (source : Absorbing code)
    (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code) :
    available (EventStep.seed (cursor.after protocol rival)).frame ⊆ available (EventStep.seed cursor).frame := by
  intro site present
  simp only [available, Finset.mem_filter, Finset.mem_univ, true_and] at present ⊢
  by_contra absent
  have spent : code.memoryReady ((EventStep.seed cursor).frame.inbox site) = false := by
    cases value : code.memoryReady ((EventStep.seed cursor).frame.inbox site) <;> simp_all
  rw [every_actual_cut_preserves_consumed_memory source cursor protocol rival site spent] at present
  contradiction

theorem an_owned_action_consumes_its_source_capacity (source : Absorbing code)
    (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code) (site : Fin code.sites)
    (owned : StageTrace.activation (StageTrace.material cursor protocol rival) = some site) :
    code.memoryReady ((EventStep.seed (cursor.after protocol rival)).frame.inbox site) = false := by
  have live := (StageTrace.an_owned_activation_submits_its_selected_work cursor protocol rival site owned).1
  change (EventStep.seed cursor).remaining ≠ 0 at live
  change (match StageTrace.capture cursor protocol rival (EventStep.seed cursor) with
    | .own worker (some event) => if event.val = .activate worker then some worker else none
    | _ => none) = some site at owned
  simp only [StageTrace.capture, if_neg live] at owned
  cases owner : Distributed.Recall.Information.Agency.ownerAt code cursor.ownerStart (EventStep.seed cursor).history.length with
  | none => simp only [owner] at owned; contradiction
  | some worker =>
    simp only [owner] at owned
    cases chosen : localEvent code protocol worker ((EventStep.seed cursor).frame.inbox worker) with
    | none => simp only [chosen] at owned; contradiction
    | some event =>
      simp only [chosen] at owned
      split_ifs at owned with activated
      · have same := Option.some.inj owned
        subst site
        rw [EventStep.actual_next_state]
        have decisionAt : decision code (EventStep.applied cursor protocol rival) (EventStep.seed cursor) = some event := by
          simp only [decision, if_neg live, Cursor.controller, driver, owner, chosen]
        simpa only [Reaction.Feedback.advance, decisionAt, stepLocal, activated, Code.step, if_true] using
          source.action worker ((EventStep.seed cursor).frame.inbox worker)
            (code.action protocol.work.val worker ((EventStep.seed cursor).frame.inbox worker))
            (generated_action_is_in_the_source_alphabet protocol.work.val protocol.work.property _ _)

def productive (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code) : Bool :=
  (StageTrace.activation (StageTrace.material cursor protocol rival)).isSome &&
    !(StageTrace.material cursor protocol rival).submitted.isEmpty

def count (cursor : Cursor code) : List (EventHistory.Stage (code := code)) → Nat
  | [] => 0
  | (protocol, rival) :: tail => (if productive cursor protocol rival then 1 else 0) + count (cursor.after protocol rival) tail

theorem a_nonempty_owned_action_strictly_spends_capacity (source : Absorbing code)
    (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code)
    (active : productive cursor protocol rival = true) :
    rank (cursor.after protocol rival) < rank cursor := by
  have facts : (StageTrace.activation (StageTrace.material cursor protocol rival)).isSome = true ∧
      (StageTrace.material cursor protocol rival).submitted ≠ [] := by
    simpa [productive] using active
  obtain ⟨selected, nonempty⟩ := facts
  obtain ⟨site, owned⟩ := Option.isSome_iff_exists.mp selected
  have submitted := (StageTrace.an_owned_activation_submits_its_selected_work cursor protocol rival site owned).2
  have ready : code.memoryReady ((EventStep.seed cursor).frame.inbox site) = true := by
    by_contra missing
    have empty : code.action protocol.work.val site ((EventStep.seed cursor).frame.inbox site) = [] := by
      simp [Code.action, missing]
    rw [submitted, empty] at nonempty
    contradiction
  have consumed := an_owned_action_consumes_its_source_capacity source cursor protocol rival site owned
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨actual_capacity_never_increases source cursor protocol rival, ?_⟩
  intro same
  have member : site ∈ available (EventStep.seed cursor).frame := by simp [available, ready]
  rw [← same] at member
  simp [available, consumed] at member

-- Unlike remaining fuel, this counts only actual nonempty owned submissions.
theorem the_actual_source_pays_for_every_productive_response (source : Absorbing code)
    (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) :
    count cursor stages + rank (EventHistory.execute cursor stages) ≤ rank cursor := by
  induction stages generalizing cursor with
  | nil => simp [count, EventHistory.execute]
  | cons stage tail ih =>
    rcases stage with ⟨protocol, rival⟩
    have rest := ih (cursor.after protocol rival)
    have nonincrease := Finset.card_le_card (actual_capacity_never_increases source cursor protocol rival)
    change rank (cursor.after protocol rival) ≤ rank cursor at nonincrease
    simp only [count, EventHistory.execute]
    split
    · have strict := a_nonempty_owned_action_strictly_spends_capacity source cursor protocol rival (by assumption)
      omega
    · omega

theorem response_count_is_bounded_by_the_actual_initial_memory (source : Absorbing code)
    (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) :
    count cursor stages ≤ rank cursor ∧ rank cursor ≤ code.sites := by
  have paid := the_actual_source_pays_for_every_productive_response source cursor stages
  refine ⟨by omega, ?_⟩
  exact (Finset.card_filter_le _ _).trans (by simp)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResponseCapacity
