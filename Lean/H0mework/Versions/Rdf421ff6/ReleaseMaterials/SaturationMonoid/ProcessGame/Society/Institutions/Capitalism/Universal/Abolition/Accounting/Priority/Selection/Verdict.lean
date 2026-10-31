import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Progress.Budget

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Selection

open Source.Program Innovation
open Exit.Necessity

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {source : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : source.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim source past nature response)
  (state : Responsibility.Family.State claim) (law : RawLaw Party Good Port Technology Instrument)
  (members : List Party) (proposal : RawEvent Party Good Port Technology Instrument)

local notation "ev" => Policy.evaluate claim state law members proposal

structure Permit : Prop where
  declared : state.declared = true
  noStop : (ev).stop = none
  needs : AllNeedsPaid law state.raw members (ev).actualWord
  strictProgress : Progress.budget claim (ev).updated < Progress.budget claim state

inductive GateIssue : Type
  | pending (undeclared : state.declared ≠ true)
  | request (issue : Policy.StoppedAt claim state law members proposal) (original : (ev).stop = some issue)

inductive NeedFailure : Type
  | necessity (actor : Party) (original : actor ∈ members)
      (unpaid : ¬ BundlePaid law state.raw (ev).actualWord actor (law.necessities state.raw actor) .necessity)
  | maintenance (actor : Party) (original : actor ∈ members)
      (unpaid : ¬ BundlePaid law state.raw (ev).actualWord actor (law.mandatoryMaintenance state.raw actor) .maintenance)

inductive RenewalVerdict : Type
  | admitted (permit : Permit claim state law members proposal)
  | settled (paid : Responsibility.Family.State.isPaid claim (ev).updated)
      (needs : AllNeedsPaid law state.raw members (ev).actualWord)
      (declared : state.declared = true) (noStop : (ev).stop = none)
  | gate (issue : GateIssue claim state law members proposal)
  | needs (issue : NeedFailure claim state law members proposal)
  | residual (issue : Responsibility.Family.ObstructionAt claim state)
      (noProgress : ¬ Progress.budget claim (ev).updated < Progress.budget claim state)

/-- The policy is selected before its next source input. Every branch is
computed from that actual input; no successful endpoint or cap is supplied. -/
def renewalVerdict : RenewalVerdict claim state law members proposal :=
  if declared : state.declared = true then
    match noStop : (ev).stop with
    | some issue => .gate (.request issue noStop)
    | none =>
      match Responsibility.Family.inspectActualNeeds claim state law (ev).executableWord members with
      | .necessity actor original unpaid => .needs (.necessity actor original unpaid)
      | .maintenance actor original unpaid => .needs (.maintenance actor original unpaid)
      | .paid needs =>
        if progress : Progress.budget claim (ev).updated < Progress.budget claim state then
          .admitted ⟨declared,noStop,needs,progress⟩
        else match Responsibility.Family.adjudicate claim state law (ev).executableWord with
          | .paid complete => .settled complete needs declared noStop
          | .blocked issue => .residual issue progress
  else .gate (.pending declared)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Selection
