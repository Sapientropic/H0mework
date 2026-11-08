import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PartyFrame

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PartyFeedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed Reaction Reaction.Feedback
open Repayment.Recovery (Good)
open WholePartyLift PartyCode
variable (old : OldCode) (outside : Good → ℚ)

def choice (c : Choice old) : Choice (code old outside) :=
  ⟨event c.val,List.mem_map.mpr ⟨c.val,c.property,rfl⟩⟩

def opponent (rival : Opponent old) : Opponent (code old outside) := fun history past f =>
  match history? history,events? past,word? f.word with
  | some original,some events,some _ => (rival original events (PartyFrame.unframe old outside f)).map (choice old outside)
  | _,_,_ => none

theorem opponent_image (rival : Opponent old) (history : List (List OldAction)) (past : Events old) (f : old.Frame) :
    opponent old outside rival (history.map (List.map request)) (past.map event) (PartyFrame.frame old outside f) =
      (rival history past f).map (choice old outside) := by
  unfold opponent
  rw [history_history,events_events,show word? (PartyFrame.frame old outside f).word = some f.word from word_word f.word]
  rw [PartyFrame.unframe_frame]

def input (entry : Input old) : Input (code old outside) := ⟨opponent old outside entry.opponent,entry.budget⟩
def state (s : Feedback.State old) : Feedback.State (code old outside) :=
  ⟨current s.current outside,s.history.map (List.map request),s.past.map event,PartyFrame.frame old outside s.frame,s.remaining⟩

theorem decision (entry : Input old) (s : Feedback.State old) :
    Feedback.decision (code old outside) (input old outside entry) (state old outside s) =
      (Feedback.decision old entry s).map (choice old outside) := by
  simp only [Feedback.decision,input,state]
  split <;> simp_all only [Option.map_none,opponent_image]

theorem stepLocal (same : old.law = oldLaw) (p : old.Policy) (s : Feedback.State old)
    (ev : Event OldParty Good OldPort OldState Unit old.sites) :
    Feedback.stepLocal (code old outside) (policy old outside p) (state old outside s) (event ev) =
      PartyFrame.frame old outside (Feedback.stepLocal old p s ev) :=
  PartyFrame.step old outside same p s.current {s.frame with word := []} ev

theorem word (same : old.law = oldLaw) (p : Option old.Policy) (entry : Input old) (s : Feedback.State old) :
    Feedback.word (code old outside) (p.map (policy old outside)) (input old outside entry) (state old outside s) =
      (Feedback.word old p entry s).map request := by
  simp only [Feedback.word,decision]
  cases p with
  | none => rfl
  | some p =>
      cases selected : Feedback.decision old entry s with
      | none => rfl
      | some ev =>
          simp only [Option.map_some,choice]
          rw [stepLocal old outside same]
          rfl

theorem advance (same : old.law = oldLaw) (p : Option old.Policy) (entry : Input old) (s : Feedback.State old) :
    Feedback.advance (code old outside) (p.map (policy old outside)) (input old outside entry) (state old outside s) =
      state old outside (Feedback.advance old p entry s) := by
  simp only [Feedback.advance,word old outside same,decision]
  cases p with
  | none =>
      simp only [Option.map_none,state,List.map_append,List.map_singleton]
      erw [WholePartyExecution.next,← same]
  | some p =>
      cases selected : Feedback.decision old entry s with
      | none =>
          simp only [Option.map_some,Option.map_none,state,List.map_append,List.map_singleton]
          erw [WholePartyExecution.next,← same]
      | some ev =>
          simp only [Option.map_some,choice]
          rw [stepLocal old outside same]
          simp only [state,PartyFrame.frame,List.map_append,List.map_drop,List.map_map,List.length_map]
          erw [WholePartyExecution.next,← same]
          congr 2

theorem run (same : old.law = oldLaw) (p : Option old.Policy) (entry : Input old) (s : Feedback.State old) (n : Nat) :
    Feedback.run (code old outside) (p.map (policy old outside)) (input old outside entry) (state old outside s) n =
      state old outside (Feedback.run old p entry s n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Feedback.run,ih,advance old outside same]

theorem traceFrom (same : old.law = oldLaw) (p : old.Policy) (here : OldCurrent)
    (history : List (List OldAction)) (rival : Opponent old) (n : Nat) (past : Events old) (f : old.Frame) :
    Reaction.traceFrom (code old outside) (policy old outside p) (current here outside) (history.map (List.map request))
      (opponent old outside rival) n (past.map event) (PartyFrame.frame old outside f) =
      (Reaction.traceFrom old p here history rival n past f).map event := by
  induction n generalizing past f with
  | zero => rfl
  | succ n ih =>
      simp only [Reaction.traceFrom,opponent_image]
      cases selected : rival history past f with
      | none => rfl
      | some ev =>
          simp only [Option.map_some,choice,PartyFrame.step old outside same,List.map_cons]
          simpa only [List.map_append,List.map_singleton] using
            congrArg (List.cons (event ev.val)) (ih (past ++ [ev.val]) (old.step p here f ev.val))
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PartyFeedback
