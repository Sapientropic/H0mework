import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal.Action

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
open Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (frame : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)
  (proposal : RawEvent Party Good Port Technology Instrument)

local notation "current" => Source.native claim frame proposal
local notation "word" => Root.Gate.executableWord claim frame proposal

private def answerTarget
    {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {event : ExactTemporalCausalRootEventAt root.toAuthoritativeRoot.toLedgerRoot visit}
    {entry : OpenResponsibilityAt N (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (root.emitted visit.current))}
    {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry}
    (original : SourceNativeSequentialActualActionTargetAt root visit event entry authority)
    (Answer : Type) (answer : Answer) : SourceNativeSequentialActualActionTargetAt root visit event entry authority :=
  { original with
    Answer := Answer
    answer := answer
    Receipt := fun returned => ULift.{3,0} (PLift (returned = answer)) ×
      original.Receipt original.answer
    receipt := ⟨⟨⟨rfl⟩⟩,original.receipt⟩ }

private def sourceProgram (original : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)
    (executed : RawEvent Party Good Port Technology Instrument) (Answer : Type) (answer : Answer) :
    SourceNativeSequentialActualActionProgramAt original.root original.visit original.row original.authority where
  targetAt := fun event => answerTarget
    (Abolition.Accounting.Root.Reentry.targetAt claim original executed event) Answer answer

/-- The answer is read on this source. The physical word, translation,
whole-ledger write and canonical next remain the original actual action. -/
def program := sourceProgram claim current word (Reply claim frame proposal) (Source.readReply claim frame proposal)

def generated := (program claim frame proposal).generate
  ((current).root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (current).visit)

def nextFrame : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim :=
  Abolition.Accounting.Root.Reentry.nextFrame claim current word

theorem the_reply_is_the_actual_action_answer :
    (generated claim frame proposal).target.answer = Source.readReply claim frame proposal := rfl

theorem the_reply_keeps_the_same_actual_target_root :
    (generated claim frame proposal).target.targetRoot = (nextFrame claim frame proposal).root := rfl

theorem the_reply_keeps_the_same_actual_target_entry :
    (generated claim frame proposal).target.targetEntry = (nextFrame claim frame proposal).row := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal.Action
