import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PartyFeedback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PartyCursor
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Repayment.Recovery (Good)
open WholePartyLift PartyCode

abbrev OldMachine := Machine OldParty Good OldPort OldState Unit

def controls (old : OldCode) (outside : Good → ℚ) (entries : List (Nat × Option old.Policy)) :=
  entries.map (fun entry => (entry.1,entry.2.map (policy old outside)))

def machine (source : OldMachine) (outside : Good → ℚ) (same : source.code.law = oldLaw) :
    Machine WholeCursorLaw.Party Good WholeCursorLaw.Port NewState Unit where
  code := code source.code outside
  reference := policy source.code outside source.reference
  reference_generated := generated source.code outside source.reference source.reference_generated
  history := source.history.map (List.map request)
  original := histories source.code outside same source.history source.original
  opponent := PartyFeedback.opponent source.code outside source.opponent
  side := source.side
  continuation := source.continuation.map (List.map request)
  feedback? := source.feedback?.map (PartyFeedback.input source.code outside)
  feedbackOverrides := controls source.code outside source.feedbackOverrides

variable (source : OldMachine) (outside : Good → ℚ) (same : source.code.law = oldLaw)

theorem policy_original (original : source.side = .original) :
    (machine source outside same).policy? = source.policy?.map (policy source.code outside) := by
  simp only [Machine.policy?,Machine.policyForSide,machine,original,Option.map_some]

include same in
theorem eventsFor (p : Option source.code.Policy) (here : OldCurrent) :
    Machine.eventsFor (code source.code outside) (p.map (policy source.code outside))
      (source.history.map (List.map request)) (PartyFeedback.opponent source.code outside source.opponent)
      (current here outside) =
      (Machine.eventsFor source.code p source.history source.opponent here).map event := by
  cases p with
  | none => rfl
  | some p => exact PartyFeedback.traceFrom source.code outside same p here source.history source.opponent source.code.eventLimit [] source.code.start

include same in
theorem frameFor (p : Option source.code.Policy) (here : OldCurrent) :
    Machine.frameFor (code source.code outside) (p.map (policy source.code outside))
      (source.history.map (List.map request)) (PartyFeedback.opponent source.code outside source.opponent)
      (current here outside) =
      PartyFrame.frame source.code outside (Machine.frameFor source.code p source.history source.opponent here) := by
  cases p with
  | none => rfl
  | some p =>
      simp only [Option.map_some,Machine.frameFor]
      rw [show some (policy source.code outside p) = (some p).map (policy source.code outside) from rfl,
        eventsFor source outside same,PartyFrame.replay source.code outside same]

theorem response (original : source.side = .original) (here : OldCurrent) :
    (machine source outside same).response (current here outside) = (source.response here).map request := by
  unfold Machine.response
  rw [policy_original source outside same original]
  change (Machine.frameFor (code source.code outside) (source.policy?.map (policy source.code outside))
    (source.history.map (List.map request)) (PartyFeedback.opponent source.code outside source.opponent)
    (current here outside)).word = _
  rw [frameFor source outside same]
  rfl

theorem responseFrame (original : source.side = .original) :
    (machine source outside same).responseFrame = PartyFrame.frame source.code outside source.responseFrame := by
  unfold Machine.responseFrame
  rw [policy_original source outside same original]
  change Machine.frameFor (code source.code outside) (source.policy?.map (policy source.code outside))
    (source.history.map (List.map request)) (PartyFeedback.opponent source.code outside source.opponent)
    ((code source.code outside).historyCurrent (source.history.map (List.map request))) = _
  rw [historyCurrent source.code outside same,frameFor source outside same]

theorem feedbackPolicy (original : source.side = .original) (index : Nat) :
    (machine source outside same).feedbackPolicy index =
      (source.feedbackPolicy index).map (policy source.code outside) := by
  have fold : ∀ (entries : List (Nat × Option source.code.Policy)) (prior : Option source.code.Policy),
      (controls source.code outside entries).foldl (fun prior entry => if entry.1 = index then entry.2 else prior)
        (prior.map (policy source.code outside)) =
      (entries.foldl (fun prior entry => if entry.1 = index then entry.2 else prior) prior).map (policy source.code outside) := by
    intro entries prior
    induction entries generalizing prior with
    | nil => rfl
    | cons head tail ih =>
        simp only [controls,List.map_cons,List.foldl_cons]
        split_ifs <;> exact ih _
  unfold Machine.feedbackPolicy
  rw [policy_original source outside same original]
  exact fold source.feedbackOverrides source.policy?

theorem feedbackInitial (original : source.side = .original) (entry : Input source.code) :
    (machine source outside same).feedbackInitial (PartyFeedback.input source.code outside entry) =
      PartyFeedback.state source.code outside (source.feedbackInitial entry) := by
  unfold Machine.feedbackInitial
  rw [responseFrame source outside same original]
  have history := historyCurrent source.code outside same source.history
  have chosen := policy_original source outside same original
  simp only [Machine.emissionEvents,chosen]
  erw [history,eventsFor source outside same]
  change (⟨newLaw.next (current (source.code.historyCurrent source.history) outside) (source.responseFrame.word.map request),_,_,_,_⟩ : Feedback.State (code source.code outside)) = _
  rw [WholePartyExecution.next,← same]
  simp only [PartyFeedback.state,List.map_append,List.map_singleton]
  rfl

theorem feedbackState (original : source.side = .original) (entry : Input source.code) (n : Nat) :
    (machine source outside same).feedbackState (PartyFeedback.input source.code outside entry) n =
      PartyFeedback.state source.code outside (source.feedbackState entry n) := by
  induction n with
  | zero => exact feedbackInitial source outside same original entry
  | succ n ih =>
      simp only [Machine.feedbackState,feedbackPolicy source outside same original,ih]
      exact PartyFeedback.advance source.code outside same _ _ _

theorem laterResponse (original : source.side = .original) (here : OldCurrent) (index : Nat) :
    (machine source outside same).laterResponse (current here outside) index =
      (source.laterResponse here index).map request := by
  unfold Machine.laterResponse
  rw [show (machine source outside same).feedback? = source.feedback?.map (PartyFeedback.input source.code outside) from rfl]
  cases entry : source.feedback? with
  | none => exact response source outside same original here
  | some entry =>
      simp only [Option.map_some]
      rw [feedbackPolicy source outside same original,feedbackState source outside same original]
      exact PartyFeedback.word source.code outside same _ _ _

theorem body (original : source.side = .original) (here : OldCurrent) :
    (machine source outside same).body (current here outside) = (source.body here).map request := by
  unfold Machine.body
  simp only [show (current here outside).round - (machine source outside same).code.initial.round - 1 =
    here.round-source.code.initial.round-1 from rfl,
    show (machine source outside same).history = source.history.map (List.map request) from rfl,
    show (machine source outside same).continuation = source.continuation.map (List.map request) from rfl,
    List.getElem?_map,List.length_map]
  cases found : source.history[here.round-source.code.initial.round-1]? with
  | some word => rfl
  | none =>
      simp only [Option.map_none]
      split_ifs
      · cases found : source.continuation[here.round-source.code.initial.round-1-source.history.length-1]? with
        | some word => rfl
        | none => exact laterResponse source outside same original here _
      · exact response source outside same original here

-- Every field is retained. In particular, ownerStart is not recomputed from a new history.
def cursor (old : OldCode) (outside : Good → ℚ) (same : old.law = oldLaw) (saved : Cursor old) :
    Cursor (code old outside) :=
  ⟨policy old outside saved.reference,generated old outside saved.reference saved.reference_generated,
    saved.history.map (List.map request),histories old outside same saved.history saved.original,
    PartyFeedback.opponent old outside saved.opponent,saved.side,PartyFeedback.input old outside saved.entry,
    controls old outside saved.overrides,saved.cut,saved.ownerStart⟩

theorem cursor_source (old : OldCode) (same : old.law = oldLaw) (saved : Cursor old) :
    (cursor old outside same saved).source = machine saved.source outside same := rfl

theorem whole_live_seed (old : OldCode) (same : old.law = oldLaw) (saved : Cursor old)
    (original : saved.side = .original) :
    EventStep.seed (cursor old outside same saved) = PartyFeedback.state old outside (EventStep.seed saved) :=
  feedbackState saved.source outside same original saved.entry saved.cut
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PartyCursor
