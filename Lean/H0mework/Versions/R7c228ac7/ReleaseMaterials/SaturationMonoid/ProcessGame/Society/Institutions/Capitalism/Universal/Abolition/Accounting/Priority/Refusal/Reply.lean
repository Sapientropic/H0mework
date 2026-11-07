import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal.Liability

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation

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

structure Reply : Type where
  submittedWord : RawEvent Party Good Port Technology Instrument
  executableWord : RawEvent Party Good Port Technology Instrument
  unexecutedSuffix : RawEvent Party Good Port Technology Instrument
  source_submitted : submittedWord = Root.Input.readProposal claim frame proposal
  source_executed : executableWord = Root.Gate.executableWord claim frame proposal
  whole_word : submittedWord = executableWord ++ unexecutedSuffix
  classification : Classification claim
    (Abolition.Accounting.Root.Reentry.Frame.state claim (Root.Input.native claim frame proposal))
    (Root.readLaw claim (Root.Input.native claim frame proposal))
    (Root.readMembers claim (Root.Input.native claim frame proposal))
    (Root.Input.readProposal claim frame proposal) (Root.Gate.readRenewal claim frame proposal)
  liability : LiabilityAt claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
    frame.actualLaw frame.members (Root.Gate.executableWord claim frame proposal)

def reply : Reply claim frame proposal where
  submittedWord := Root.Input.readProposal claim frame proposal
  executableWord := Root.Gate.executableWord claim frame proposal
  unexecutedSuffix := (Root.Gate.readEvaluation claim frame proposal).remainder
  source_submitted := rfl
  source_executed := rfl
  whole_word := (Root.Gate.readEvaluation claim frame proposal).original
  classification := classify claim _ _ _ _ (Root.Gate.readRenewal claim frame proposal)
  liability := carryLiability claim _ _ _ _

def Reply.refusalWitness? (packet : Reply claim frame proposal) :=
  Refusal.refusalWitness? claim _ _ _ _ packet.classification

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal
