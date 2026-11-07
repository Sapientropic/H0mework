import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary.Liability

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary

open Source.Program Innovation Exit.Necessity

noncomputable section

attribute [local irreducible] actualLaw budget

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed)) (current : Current seed claim)
  (proposal : RawEvent Party Good Port Technology Instrument)

structure Permit : Prop where
  productiveDeclared : current.productiveDeclared = true
  grossDeclared : current.grossDeclared = true
  noStop : executed seed claim current proposal = proposal
  needs : AllNeedsPaid (actualLaw seed) current.raw seed.current.members (executed seed claim current proposal)
  strictProgress : budget seed claim (next seed claim current proposal) < budget seed claim current

inductive GateIssue : Type
  | pendingProductive (undeclared : current.productiveDeclared ≠ true)
  | pendingGross (undeclared : current.grossDeclared ≠ true)
  | request (request : Request Party Good Port Technology Instrument)
      (rest : RawEvent Party Good Port Technology Instrument)
      (original : proposal = executed seed claim current proposal ++ request :: rest)
      (denied : ¬ (actualLaw seed).Valid
        ((actualLaw seed).execute current.raw 0 (executed seed claim current proposal)).final request)

inductive NeedFailure : Type
  | necessity (actor : Party) (original : actor ∈ seed.current.members)
      (unpaid : ¬ BundlePaid (actualLaw seed) current.raw (executed seed claim current proposal)
        actor ((actualLaw seed).necessities current.raw actor) .necessity)
  | maintenance (actor : Party) (original : actor ∈ seed.current.members)
      (unpaid : ¬ BundlePaid (actualLaw seed) current.raw (executed seed claim current proposal)
        actor ((actualLaw seed).mandatoryMaintenance current.raw actor) .maintenance)

inductive Verdict : Type
  | admitted (permit : Permit seed claim current proposal)
  | settled (paid : Current.productivePaid seed claim (next seed claim current proposal) ∧
        Current.grossPaid seed claim (next seed claim current proposal))
      (needs : AllNeedsPaid (actualLaw seed) current.raw seed.current.members (executed seed claim current proposal))
      (productiveDeclared : current.productiveDeclared = true) (grossDeclared : current.grossDeclared = true)
      (noStop : executed seed claim current proposal = proposal)
  | gate (issue : GateIssue seed claim current proposal)
  | needs (issue : NeedFailure seed claim current proposal)
  | residual (issue : ResidualAt seed claim (next seed claim current proposal))
      (noProgress : ¬ budget seed claim (next seed claim current proposal) < budget seed claim current)

def verdict : Verdict seed claim current proposal :=
  if p : current.productiveDeclared = true then
    if g : current.grossDeclared = true then
      match inspection seed claim current proposal with
      | .blocked request rest original denied => .gate (.request request rest original denied)
      | .complete noStop =>
        match Responsibility.Family.inspectNeeds (actualLaw seed) current.raw (executed seed claim current proposal)
          seed.current.members with
        | .necessity actor original unpaid => .needs (.necessity actor original unpaid)
        | .maintenance actor original unpaid => .needs (.maintenance actor original unpaid)
        | .paid needs =>
          if progress : budget seed claim (next seed claim current proposal) < budget seed claim current then
            .admitted ⟨p,g,noStop,needs,progress⟩
          else match inspectDebt seed claim (next seed claim current proposal) with
            | .paid productive gross => .settled ⟨productive,gross⟩ needs p g noStop
            | .unpaid issue => .residual issue progress
    else .gate (.pendingGross g)
  else .gate (.pendingProductive p)

theorem an_actual_permit_clears_at_least_one_original_unpaid_cell
    (permit : Permit seed claim current proposal) :
    ∃ cell ∈ scope seed, 0 < remaining seed claim current cell ∧
      remaining seed claim (next seed claim current proposal) cell = 0 :=
  strict_source_progress_really_clears_an_original_cell seed claim current (executed seed claim current proposal)
    permit.strictProgress

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary
