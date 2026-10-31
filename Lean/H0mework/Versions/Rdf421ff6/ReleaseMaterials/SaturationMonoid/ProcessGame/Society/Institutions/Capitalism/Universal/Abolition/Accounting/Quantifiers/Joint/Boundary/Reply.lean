import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary.Refusal

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary

open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed)) (current : Current seed claim)
  (proposal : RawEvent Party Good Port Technology Instrument)

structure Reply : Type where
  submittedWord : RawEvent Party Good Port Technology Instrument
  executableWord : RawEvent Party Good Port Technology Instrument
  unexecutedSuffix : RawEvent Party Good Port Technology Instrument
  source_submitted : submittedWord = proposal
  source_executed : executableWord = executed seed claim current proposal
  source_suffix : unexecutedSuffix = suffix seed claim current proposal
  whole_word : submittedWord = executableWord ++ unexecutedSuffix
  classification : Classification seed claim current proposal (verdict seed claim current proposal)
  liability : LiabilityAt seed claim current proposal
  originalAttempt : Entitlement.Execution.InspectionAt (actualLaw seed) current.raw proposal
  actual_accepted : ∀ item ∈ (actualLaw seed).rawItems current.raw executableWord,
    (actualLaw seed).Valid item.before item.request

def reply : Reply seed claim current proposal where
  submittedWord := proposal
  executableWord := executed seed claim current proposal
  unexecutedSuffix := suffix seed claim current proposal
  source_submitted := rfl
  source_executed := rfl
  source_suffix := rfl
  whole_word := the_submitted_word_keeps_the_actual_prefix_and_unexecuted_suffix seed claim current proposal
  classification := classify seed claim current proposal (verdict seed claim current proposal)
  liability := carryLiability seed claim current proposal
  originalAttempt := inspection seed claim current proposal
  actual_accepted := all_executed_items_are_actual seed claim current proposal

def AuthorityDispositionAt
    {decision : Verdict seed claim current proposal} (classification : Classification seed claim current proposal decision) : Prop :=
  match classification with
  | .admitted _ => RequestedRenewalAuthorityAt seed claim current proposal decision
  | .settled .. | .refused .. => ¬ RequestedRenewalAuthorityAt seed claim current proposal decision

theorem classification_keeps_the_requested_authority_disposition
    {decision : Verdict seed claim current proposal} (classification : Classification seed claim current proposal decision) :
    AuthorityDispositionAt seed claim current proposal classification := by
  cases classification with
  | admitted permit => trivial
  | settled paid needs p g noStop => exact fun impossible => impossible
  | refused refusal => exact refusal_cannot_mint_the_requested_renewal_authority seed claim current proposal refusal

theorem the_actual_reply_keeps_the_requested_authority_disposition :
    AuthorityDispositionAt seed claim current proposal (reply seed claim current proposal).classification :=
  classification_keeps_the_requested_authority_disposition seed claim current proposal (reply seed claim current proposal).classification

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary
