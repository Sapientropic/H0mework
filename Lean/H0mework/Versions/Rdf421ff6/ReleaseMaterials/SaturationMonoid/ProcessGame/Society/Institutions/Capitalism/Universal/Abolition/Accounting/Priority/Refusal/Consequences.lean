import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal.Installation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal

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

local notation "next" => Action.nextFrame claim frame proposal
local notation "current" => Source.native claim frame proposal
local notation "word" => Root.Gate.executableWord claim frame proposal

theorem the_liability_is_read_on_the_same_actual_next_row :
    Abolition.Accounting.Root.Reentry.Frame.state claim next =
      Responsibility.Family.State.advance claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
        frame.actualLaw word :=
  Abolition.Accounting.Root.Reentry.next_frame_reads_the_actual_updated_state claim current word

theorem every_original_ledger_key_is_retained :
    type_of% (Abolition.Accounting.Root.Reentry.actual_keeps_every_original_responsibility_key claim current word) :=
  Abolition.Accounting.Root.Reentry.actual_keeps_every_original_responsibility_key claim current word

theorem the_original_row_has_not_been_replaced :
    (next).row.1 = .inr (Responsibility.Family.activationLaw claim).debtId := (next).rowKey

theorem the_entire_original_support_is_literal :
    (Abolition.Accounting.Root.Reentry.Frame.support claim next).1 =
      (Abolition.Accounting.Root.Reentry.Frame.support claim frame).1 := by
  change (Abolition.Accounting.Root.Reentry.support claim current word
    (Abolition.Accounting.Root.Compiler.successor
      (Abolition.Accounting.Root.Reentry.flow claim current word) false).targetCurrent).1 = _
  exact congrArg (fun phase : Bool => (Abolition.Accounting.Root.Reentry.support claim current word phase).1)
    (Abolition.Accounting.Root.Compiler.successor_current
      (Abolition.Accounting.Root.Reentry.flow claim current word) false)

def nextReplyFace : SourceNativeRootSemanticFaceAt (next).root (next).visit where
  projection := Abolition.Accounting.Root.Reentry.inquiryOldProjection claim current word
    (Source.replyFace claim frame proposal).projection
  active := (Source.replyFace claim frame proposal).active
  classifier_eq := (Source.replyFace claim frame proposal).classifier_eq

theorem the_actual_next_retains_its_source_reply :
    HEq (nextReplyFace claim frame proposal).rootRead (Source.readReply claim frame proposal) := HEq.rfl

private def needsFaceAt (original : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)
    (executed : RawEvent Party Good Port Technology Instrument) :
    SourceNativeRootSemanticFaceAt (Abolition.Accounting.Root.Reentry.nextFrame claim original executed).root
      (Abolition.Accounting.Root.Reentry.nextFrame claim original executed).visit where
  projection := .component Abolition.Accounting.Root.Reentry.Report.needs
  active := PUnit.unit
  classifier_eq := rfl

private theorem needsFaceAt_reads_the_actual_source
    (original : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)
    (executed : RawEvent Party Good Port Technology Instrument) :
    HEq (needsFaceAt claim original executed).rootRead
      (Responsibility.Family.inspectActualNeeds claim
        (Abolition.Accounting.Root.Reentry.Frame.state claim original) original.actualLaw executed original.members) := HEq.rfl

def nextNeedsFace := needsFaceAt claim current word

private theorem needs_at_equal_states
    (first second : Responsibility.Family.State claim) (same : first = second)
    (law : RawLaw Party Good Port Technology Instrument)
    (executed : RawEvent Party Good Port Technology Instrument) (members : List Party) :
    HEq (Responsibility.Family.inspectActualNeeds claim first law executed members)
      (Responsibility.Family.inspectActualNeeds claim second law executed members) := by
  cases same
  exact HEq.rfl

theorem the_reply_retains_the_independent_actual_need_bearers :
    HEq (nextNeedsFace claim frame proposal).rootRead (Source.readReply claim frame proposal).liability.needs := by
  have sourceRead := needsFaceAt_reads_the_actual_source claim current word
  have literal : HEq (Responsibility.Family.inspectActualNeeds claim
      (Abolition.Accounting.Root.Reentry.Frame.state claim current) (current).actualLaw word (current).members)
        (Source.readReply claim frame proposal).liability.needs := by
    rw [Source.the_compiler_reply_is_the_actual_source_face]
    exact needs_at_equal_states claim _ _ (Source.the_source_state_is_the_original_row claim frame proposal)
      frame.actualLaw word frame.members
  exact sourceRead.trans literal

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal
