import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Next
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {original : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : original.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim original past nature response)
  (current : Current (oldN := oldN) claim) (word : RawEvent Party Good Port Technology Instrument)

def executedWord : RawEvent Party Good Port Technology Instrument :=
  (Source.readReply claim current word).executableWord

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
    Receipt := fun returned => ULift.{3,0} (PLift (returned = answer)) × original.Receipt original.answer
    receipt := ⟨⟨⟨rfl⟩⟩,original.receipt⟩ }

private theorem answerTarget_next
    {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {event : ExactTemporalCausalRootEventAt root.toAuthoritativeRoot.toLedgerRoot visit}
    {entry : OpenResponsibilityAt N (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (root.emitted visit.current))}
    {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry}
    (original : SourceNativeSequentialActualActionTargetAt root visit event entry authority)
    (Answer : Type) (answer : Answer) :
    (answerTarget original Answer answer).targetAnswerAndNext.nextCurrent =
      original.targetAnswerAndNext.nextCurrent := rfl

def program : SourceNativeSequentialActualActionProgramAt
    (Source.native claim current word).root current.visit current.row (Source.native claim current word).authority where
  targetAt := fun event => answerTarget
    (targetAt claim (Source.native claim current word) (executedWord claim current word) event)
    (Reply claim current word) (Source.readReply claim current word)

def generated := (program claim current word).generate
  ((Source.native claim current word).root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt current.visit)

/-- The next inquiry consumes this exact updated row, including partial payment
and a refused tail. No finite old-ledger or singleton-fibre premise is needed. -/
def nextCurrent : Current (oldN := oldN) claim :=
  rawNext claim (Source.native claim current word) (executedWord claim current word)

theorem the_reply_is_the_actual_answer :
    (generated claim current word).target.answer = Source.readReply claim current word := rfl

theorem the_executed_word_is_read_from_the_source_reply :
    executedWord claim current word = Gate.executableWord claim current word :=
  (Source.readReply claim current word).executable_eq

theorem the_reply_and_next_use_the_same_target :
    (generated claim current word).target.targetRoot = (nextCurrent claim current word).root := rfl

theorem next_reads_the_actual_gated_state :
    Current.state claim (nextCurrent claim current word) =
      Responsibility.Family.State.advance claim (Current.state claim current) current.actualLaw
        (Gate.executableWord claim current word) := by
  unfold nextCurrent
  rw [next_reads_the_actual_updated_state]
  unfold updated
  rw [Source.state_eq,the_executed_word_is_read_from_the_source_reply]
  rfl

theorem next_is_the_actual_canonical_root_next :
    (⟨DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim),
      (generated claim current word).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) =
      Current.erase claim (nextCurrent claim current word) := by
  change (⟨DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim),
    (answerTarget (rawGenerated claim (Source.native claim current word) (executedWord claim current word)).target
      (Reply claim current word) (Source.readReply claim current word)).targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) = _
  rw [answerTarget_next]
  exact raw_next_is_the_canonical_root_next claim (Source.native claim current word) (executedWord claim current word)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse
