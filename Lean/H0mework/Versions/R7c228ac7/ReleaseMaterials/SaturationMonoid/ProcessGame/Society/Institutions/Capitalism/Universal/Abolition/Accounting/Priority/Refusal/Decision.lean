import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root.Finite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal

open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (state : Responsibility.Family.State claim) (law : RawLaw Party Good Port Technology Instrument)
  (members : List Party) (proposal : RawEvent Party Good Port Technology Instrument)

abbrev CapitalRenewalLegitimacyAt (verdict : Selection.RenewalVerdict claim state law members proposal) : Prop :=
  Root.VerdictAdmitted claim verdict

/-- A refusal records a source verdict. Its constructors do not infer a new
loss, invalidate a paid prefix, or classify ordinary standing as illegitimate. -/
inductive RefusalAt : Selection.RenewalVerdict claim state law members proposal → Type
  | gate (issue : Selection.GateIssue claim state law members proposal) : RefusalAt (.gate issue)
  | needs (issue : Selection.NeedFailure claim state law members proposal) : RefusalAt (.needs issue)
  | residual (issue : Responsibility.Family.ObstructionAt claim state)
      (noProgress : ¬ Progress.budget claim (Policy.evaluate claim state law members proposal).updated <
        Progress.budget claim state) : RefusalAt (.residual issue noProgress)

namespace RefusalAt

theorem no_capital_renewal_legitimacy {verdict : Selection.RenewalVerdict claim state law members proposal}
    (refusal : RefusalAt claim state law members proposal verdict) :
    ¬ CapitalRenewalLegitimacyAt claim state law members proposal verdict := by
  cases refusal <;> exact fun impossible => impossible

theorem admitted_is_not_a_refusal (permit : Selection.Permit claim state law members proposal)
    (refusal : RefusalAt claim state law members proposal (.admitted permit)) : False := nomatch refusal

theorem settled_is_not_a_refusal (paid needs declared noStop)
    (refusal : RefusalAt claim state law members proposal (.settled paid needs declared noStop)) : False := nomatch refusal

end RefusalAt

inductive Classification : Selection.RenewalVerdict claim state law members proposal → Type
  | admitted (permit : Selection.Permit claim state law members proposal) : Classification (.admitted permit)
  | settled (paid needs declared noStop) : Classification (.settled paid needs declared noStop)
  | refused {verdict : Selection.RenewalVerdict claim state law members proposal}
      (refusal : RefusalAt claim state law members proposal verdict) : Classification verdict

def refusalWitness? {verdict : Selection.RenewalVerdict claim state law members proposal} :
    Classification claim state law members proposal verdict → Option (RefusalAt claim state law members proposal verdict)
  | .admitted _ | .settled .. => none
  | .refused refusal => some refusal

def classify : (verdict : Selection.RenewalVerdict claim state law members proposal) →
    Classification claim state law members proposal verdict
  | .admitted permit => .admitted permit
  | .settled paid needs declared noStop => .settled paid needs declared noStop
  | .gate issue => .refused (.gate issue)
  | .needs issue => .refused (.needs issue)
  | .residual issue noProgress => .refused (.residual issue noProgress)

def AuthorityDispositionAt
    {verdict : Selection.RenewalVerdict claim state law members proposal}
    (classification : Classification claim state law members proposal verdict) : Prop :=
    match classification with
    | .admitted _ => CapitalRenewalLegitimacyAt claim state law members proposal verdict
    | .settled .. | .refused .. => ¬ CapitalRenewalLegitimacyAt claim state law members proposal verdict

theorem the_classification_keeps_the_original_renewal_authority
    {verdict : Selection.RenewalVerdict claim state law members proposal}
    (classification : Classification claim state law members proposal verdict) :
    AuthorityDispositionAt claim state law members proposal classification := by
  cases classification with
  | admitted permit => trivial
  | settled paid needs declared noStop => exact fun impossible => impossible
  | refused refusal => exact RefusalAt.no_capital_renewal_legitimacy claim state law members proposal refusal

theorem settlement_is_nonrenewal_without_being_refusal (paid needs declared noStop) :
    ¬ CapitalRenewalLegitimacyAt claim state law members proposal (.settled paid needs declared noStop) ∧
      ¬ Nonempty (RefusalAt claim state law members proposal (.settled paid needs declared noStop)) :=
  ⟨(fun impossible => impossible),fun ⟨refusal⟩ => nomatch refusal⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal
