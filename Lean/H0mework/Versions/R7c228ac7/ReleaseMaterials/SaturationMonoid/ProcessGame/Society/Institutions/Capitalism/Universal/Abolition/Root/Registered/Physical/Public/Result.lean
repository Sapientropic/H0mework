import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Execution
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Planning
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Resigning
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Scan

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def interpreter := PublicFunction.physicalLaw input.law

/-- Raw syntax remains raw syntax. Meta-programme changes are returned to
their root consumer, rather than silently executed as physical periods. -/
def wordAt (current : Actual.Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) : Compile.RawInput Party Good Port Technology Instrument →
    Option (RawEvent Party Good Port Technology Instrument)
  | .advance => match current.phase with
    | .renewal word => some (word.map (fun request => request.resign request.signer))
    | .seeking => none
  | .primitive request => some [request.resign request.signer]
  | .execute word => some (word.map (fun request => request.resign request.signer))
  | .migrate _ | .code _ | .review _ | .stopReview => none

inductive ResultAt (before : Actual.Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (raw : Compile.RawInput Party Good Port Technology Instrument) : Type
  | accepted (word : RawEvent Party Good Port Technology Instrument) (selected : wordAt before raw = some word)
      (checked : ∀ item ∈ (interpreter input).rawItems before.raw word, (interpreter input).Valid item.before item.request)
  | refused (word : RawEvent Party Good Port Technology Instrument) (selected : wordAt before raw = some word)
      (item : ExecutionItem Party Good Port Technology Instrument) (listed : item ∈ (interpreter input).rawItems before.raw word)
      (failed : ¬ (interpreter input).Valid item.before item.request)
  | metadata (selected : wordAt before raw = none)

def compile (before : Actual.Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (raw : Compile.RawInput Party Good Port Technology Instrument) :
    ResultAt input before raw :=
  match selected : wordAt before raw with
  | none => .metadata selected
  | some word =>
      match Material.inspectList (fun item : ExecutionItem Party Good Port Technology Instrument =>
          (interpreter input).Valid item.before item.request) ((interpreter input).rawItems before.raw word) with
      | .clear checked => .accepted word selected checked
      | .failure item listed failed => .refused word selected item listed failed

namespace ResultAt
variable {input} {before : Actual.Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)} {raw : Compile.RawInput Party Good Port Technology Instrument}

def execution : ResultAt input before raw → ExecutionResult Party Good Port Technology Instrument
  | .accepted word _ _ => (interpreter input).execute before.raw 0 word
  | .refused .. | .metadata _ => ⟨before.raw, []⟩

def next : ResultAt input before raw → Actual.Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
  | .accepted word _ _ => { before with raw := match raw with
    | .primitive _ => ((interpreter input).execute before.raw 0 word).final
    | _ => (interpreter input).next before.raw word }
  | .refused .. | .metadata _ => before

def isAccepted : ResultAt input before raw → Bool
  | .accepted .. => true
  | .refused .. | .metadata _ => false

end ResultAt

#print axioms compile

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public
