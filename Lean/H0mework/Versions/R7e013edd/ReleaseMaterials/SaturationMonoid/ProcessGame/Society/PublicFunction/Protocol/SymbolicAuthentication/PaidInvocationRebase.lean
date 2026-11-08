import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CatalogueHandoffSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidInvocationRebase
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
section
variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
abbrev Emitter := Code Party Good Port (Mandate.State Party Technology) Instrument

def credit {code : Emitter (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)} (state : Feedback.State code) (amount : Nat) : Feedback.State code :=
 {state with remaining := state.remaining+amount}

def entry {code : Emitter (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)} (input : Input code) (amount : Nat) : Input code :=
 ⟨input.opponent,input.budget+amount⟩

-- The caller of this transporter must obtain amount from its actual admission
-- producer. It is deliberately not an opportunity or authority producer.
def cursor {code : Emitter (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)} (before : Cursor code) (amount : Nat) : Cursor code :=
 {before with entry := entry before.entry amount}

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem advance_credit {code : Emitter (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)} (policy : Option code.Policy)
 (input : Input code) (state : Feedback.State code) (amount : Nat) (live : 0 < state.remaining) :
 Feedback.advance code policy (entry input amount) (credit state amount) =
 credit (Feedback.advance code policy input state) amount := by
 have old : state.remaining ≠ 0 := by omega
 have fresh : state.remaining+amount ≠ 0 := by omega
 have rem : state.remaining+amount-1 = state.remaining-1+amount := by omega
 simp only [Feedback.advance,Feedback.word,Feedback.decision,credit,entry,if_neg old,if_neg fresh,rem]
 rfl

theorem remaining (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
 (input : Input source.code) (count : Nat) : (source.feedbackState input count).remaining = input.budget-count := by
 induction count with
 | zero => rfl
 | succ count ih => change (source.feedbackState input count).remaining-1 = _;rw [ih];omega

theorem feedback_credit (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
 (input : Input source.code) (amount count : Nat) (within : count ≤ input.budget) :
 source.feedbackState (entry input amount) count = credit (source.feedbackState input count) amount := by
 induction count with
 | zero => rfl
 | succ count ih =>
   rw [Machine.feedbackState,Machine.feedbackState,ih (by omega)]
   apply advance_credit
   rw [remaining]
   omega

theorem seed_credit {code : Emitter (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)} (before : Cursor code) (amount : Nat)
 (within : before.cut ≤ before.entry.budget) :
 EventStep.seed (cursor before amount) = credit (EventStep.seed before) amount := by
 have same : (cursor before amount).source.feedbackState (entry before.entry amount) before.cut =
     before.source.feedbackState (entry before.entry amount) before.cut := by
   generalize before.cut = count
   induction count with
   | zero => rfl
   | succ count ih =>
     rw [Machine.feedbackState,Machine.feedbackState,ih]
     rfl
 exact same.trans (feedback_credit before.source before.entry amount before.cut within)

private theorem same_feedback {code : Emitter (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)} (before : Cursor code) (amount : Nat)
 (input : Input code) (count : Nat) :
 (cursor before amount).source.feedbackState input count = before.source.feedbackState input count := by
 induction count with
 | zero => rfl
 | succ count ih => rw [Machine.feedbackState,Machine.feedbackState,ih];rfl

theorem body_before {code : Emitter (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)} (before : Cursor code) (amount : Nat)
 (within : before.cut ≤ before.entry.budget) (location : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
 (earlier : location.round-code.initial.round-1 < before.history.length+1+before.cut) :
 (cursor before amount).source.body location = before.source.body location := by
 unfold Machine.body
 dsimp only [cursor,Cursor.source]
 simp only [List.getElem?_nil]
 split
 · rfl
 · split
   · rename_i later
     have count : location.round-code.initial.round-1-before.history.length-1 < before.cut := by omega
     change Feedback.word code _ (entry before.entry amount)
       ((cursor before amount).source.feedbackState (entry before.entry amount) _) =
       Feedback.word code _ before.entry (before.source.feedbackState before.entry _)
     rw [same_feedback,feedback_credit _ _ _ _ (by omega)]
     have old : (before.source.feedbackState before.entry
         (location.round-code.initial.round-1-before.history.length-1)).remaining ≠ 0 := by rw [remaining];omega
     have fresh : (before.source.feedbackState before.entry
         (location.round-code.initial.round-1-before.history.length-1)).remaining+amount ≠ 0 := by omega
     simp only [Feedback.word,Feedback.decision,entry,credit,if_neg old,if_neg fresh]
     rfl
   · rfl

theorem prior_raw_event {code : Emitter (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)} (before : Cursor code) (amount : Nat)
 (within : before.cut ≤ before.entry.budget) (ordinal : Nat) (earlier : ordinal < EventStep.boundary before) :
 ProgrammeSource.rawEvent (cursor before amount).source.input
     (ProgrammeHistory.visitAt before.source.input ordinal).current =
 ProgrammeSource.rawEvent before.source.input (ProgrammeHistory.visitAt before.source.input ordinal).current := by
 cases view : (ProgrammeHistory.visitAt before.source.input ordinal).current with
 | bootstrap => rfl
 | running location past =>
   change (cursor before amount).source.body location = before.source.body location
   apply body_before before amount within location
   have rounds := ProgrammeHistory.visit_round before.source.input ordinal
   rw [view] at rounds
   change location.round = code.initial.round+ordinal at rounds
   dsimp only [EventStep.boundary] at earlier
   omega

theorem complete_financial_prefix {code : Emitter (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)} (before : Cursor code) (amount : Nat)
 (within : before.cut ≤ before.entry.budget) (ordinal : Nat) (earlier : ordinal ≤ EventStep.boundary before) :
 Native.Coupling.Match code before.source.input (cursor before amount).source.input
   (Financial.accountAt before.source.input ordinal) (Financial.accountAt (cursor before amount).source.input ordinal) :=
 Native.Coupling.History.complete_accounts code before.source.input (cursor before amount).source.input rfl rfl
   (EventStep.boundary before) (prior_raw_event before amount within) before.source.body (cursor before amount).source.body
   rfl rfl ordinal earlier

theorem complete_physical_state {code : Emitter (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)} (before : Cursor code) (amount : Nat)
 (within : before.cut ≤ before.entry.budget) :
 (EventStep.seed (cursor before amount)).current = (EventStep.seed before).current ∧
 (EventStep.seed (cursor before amount)).history = (EventStep.seed before).history ∧
 (EventStep.seed (cursor before amount)).past = (EventStep.seed before).past ∧
 (EventStep.seed (cursor before amount)).frame = (EventStep.seed before).frame ∧
 (EventStep.seed (cursor before amount)).remaining = (EventStep.seed before).remaining+amount := by
 rw [seed_credit before amount within]
 exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidInvocationRebase
