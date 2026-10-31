import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Compile.Raw

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Compile

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

structure CheckedAt (raw : RawInput Party Good Port Technology Instrument) where
  private mk ::
  command : Actual.Command input depth count prefixLimit renewalLimit current
  source : SourceAt input depth count prefixLimit renewalLimit current raw command

inductive Result (raw : RawInput Party Good Port Technology Instrument) : Type
  | accepted (checked : CheckedAt input depth count prefixLimit renewalLimit current raw)
  | refused (reason : RefusalAt input depth count prefixLimit renewalLimit current raw)

private theorem code_check_not_none (submission : Actual.Submission Party Good Port Technology Instrument)
    (admitted : (Actual.receive input depth count prefixLimit renewalLimit current).admissible input depth count prefixLimit renewalLimit) :
    Actual.submissionCheck? input depth count prefixLimit renewalLimit current submission ≠ none := by
  simp only [Actual.submissionCheck?, dif_pos admitted]
  intro impossible
  cases impossible

private def compileCode (submission : Actual.Submission Party Good Port Technology Instrument) :
    Result input depth count prefixLimit renewalLimit current (.code submission) :=
  match checked : Actual.submissionCheck? input depth count prefixLimit renewalLimit current submission with
  | some admitted => .accepted ⟨.submission submission admitted, .code submission admitted⟩
  | none => match observed : Actual.receive input depth count prefixLimit renewalLimit current with
    | .busy operation notBoundary source => .refused (.busy submission operation notBoundary source)
    | .received obstruction source => False.elim (by
        apply code_check_not_none input depth count prefixLimit renewalLimit current submission _ checked
        rw [observed]
        trivial)
    | .receivedBoundary word phase paid source => False.elim (by
        apply code_check_not_none input depth count prefixLimit renewalLimit current submission _ checked
        rw [observed]
        trivial)

private def compileReview (code : ReviewSource.Control.Code Party Good Port Technology Instrument) :
    Result input depth count prefixLimit renewalLimit current (.review code) :=
  match observed : Actual.receive input depth count prefixLimit renewalLimit current with
  | .received obstruction source =>
      let admitted : (Actual.receive input depth count prefixLimit renewalLimit current).admissible input depth count prefixLimit renewalLimit := by
        rw [observed]
        trivial
      .accepted ⟨.review code admitted, .review code admitted⟩
  | .receivedBoundary word phase paid source =>
      let admitted : (Actual.receive input depth count prefixLimit renewalLimit current).admissible input depth count prefixLimit renewalLimit := by
        rw [observed]
        trivial
      .accepted ⟨.review code admitted, .review code admitted⟩
  | .busy operation notBoundary source => .refused (.reviewBusy code operation notBoundary source)

/-- This is the only checked-command factory: the caller supplies the finite
registered payload, never a command, successful plan, or physical target. -/
def compile : (raw : RawInput Party Good Port Technology Instrument) →
    Result input depth count prefixLimit renewalLimit current raw
  | .advance => match Actual.dispatch input depth count prefixLimit renewalLimit current with
    | .automatic generated => .accepted ⟨.automatic generated, .advance generated⟩
    | .refusal obstruction source => .refused (.blocked obstruction source)
  | .code submission => compileCode input depth count prefixLimit renewalLimit current submission
  | .primitive request => match Actual.inspectPrimitive input current request with
    | .accepted legal => .accepted ⟨.primitive request (Actual.primitive input current request), .primitive request legal⟩
    | .refused failure => .refused (.invalid request failure)
  | .execute word => match Actual.Batch.inspect input (Actual.origin input depth count) current.raw (Actual.members input depth count) word with
    | .accepted checked => .accepted ⟨.execute word checked, .execute word checked⟩
    | .refused issue => .refused (.batch word issue)
  | .migrate pair => match Actual.Migration.inspect input (Actual.origin input depth count) current.raw (Actual.members input depth count) pair with
    | .accepted checked => .accepted ⟨.migrate pair checked, .migrate pair checked⟩
    | .refused issue => .refused (.migration pair issue)
  | .stopReview => .refused .reviewStopped
  | .review code => compileReview input depth count prefixLimit renewalLimit current code

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Compile
