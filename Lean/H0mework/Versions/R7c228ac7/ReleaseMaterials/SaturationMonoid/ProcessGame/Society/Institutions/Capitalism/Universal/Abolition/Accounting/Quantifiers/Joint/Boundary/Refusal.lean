import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary.Verdict

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

/-- Authority is only the source verdict's admitted renewal of these old
repair rows. It says nothing against independent standing or new contributions. -/
def RequestedRenewalAuthorityAt (decision : Verdict seed claim current proposal) : Prop :=
  match decision with
  | .admitted _ => True
  | .settled .. | .gate .. | .needs .. | .residual .. => False

inductive RefusalAt : Verdict seed claim current proposal → Type
  | gate (issue : GateIssue seed claim current proposal) : RefusalAt (.gate issue)
  | needs (issue : NeedFailure seed claim current proposal) : RefusalAt (.needs issue)
  | residual (issue : ResidualAt seed claim (next seed claim current proposal))
      (noProgress : ¬ budget seed claim (next seed claim current proposal) < budget seed claim current) :
      RefusalAt (.residual issue noProgress)

theorem refusal_cannot_mint_the_requested_renewal_authority
    {decision : Verdict seed claim current proposal} (refusal : RefusalAt seed claim current proposal decision) :
    ¬ RequestedRenewalAuthorityAt seed claim current proposal decision := by
  cases refusal <;> exact fun impossible => impossible

inductive Classification : Verdict seed claim current proposal → Type
  | admitted (permit : Permit seed claim current proposal) : Classification (.admitted permit)
  | settled (paid needs productiveDeclared grossDeclared noStop) :
      Classification (.settled paid needs productiveDeclared grossDeclared noStop)
  | refused {decision : Verdict seed claim current proposal}
      (refusal : RefusalAt seed claim current proposal decision) : Classification decision

def classify : (decision : Verdict seed claim current proposal) → Classification seed claim current proposal decision
  | .admitted permit => .admitted permit
  | .settled paid needs p g noStop => .settled paid needs p g noStop
  | .gate issue => .refused (.gate issue)
  | .needs issue => .refused (.needs issue)
  | .residual issue noProgress => .refused (.residual issue noProgress)

theorem settlement_is_nonrenewal_without_being_refusal (paid needs p g noStop) :
    ¬ RequestedRenewalAuthorityAt seed claim current proposal (.settled paid needs p g noStop) ∧
      ¬ Nonempty (RefusalAt seed claim current proposal (.settled paid needs p g noStop)) :=
  ⟨(fun impossible => impossible),fun ⟨refusal⟩ => nomatch refusal⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary
