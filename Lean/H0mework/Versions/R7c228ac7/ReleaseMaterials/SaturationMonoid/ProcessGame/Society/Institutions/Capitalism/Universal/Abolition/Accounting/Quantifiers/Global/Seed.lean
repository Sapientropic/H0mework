import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Completeness.Registered
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Global.Capital

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Global

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}

/-- Only original source coordinates and submitted finite inputs enter.
There is no supplied open-law invariant, target frame or successful plan. -/
structure Seed where
  input : ProgrammeSource.Input Party Good Port Technology Instrument
  depth : Nat
  count : Nat
  claim : Responsibility.Family.Claim mechanism past nature response
  origin : Abolition.Accounting.Root.Source.OriginAt input
    (Financial.Installation.Runtime.frames input depth count).native
    ((Financial.Installation.Runtime.frames input depth count).temporal input) claim
  inputs : List (RawEvent Party Good Port Technology Instrument)

namespace Seed
variable (seed : Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))

def current := Priority.Root.afterInputs seed.claim
  (Completion.currentFamily seed.input seed.depth seed.count seed.claim []) seed.inputs

theorem registered : Priority.Completion.RegisteredPriorityAt seed.input seed.depth seed.count seed.claim seed.origin [] :=
  Priority.Completion.responsibility_is_paid_before_capital_and_has_no_unbounded_renewal_authority
    seed.input seed.depth seed.count seed.claim seed.origin []

theorem declared : (Abolition.Accounting.Root.Reentry.Frame.state seed.claim seed.current).declared = true :=
  seed.registered.every_continuation_declared seed.inputs

theorem opened (technology : Technology) (port : Port) (person : Party) :
    seed.current.actualLaw.allowed technology port person = true :=
  seed.registered.no_control_reintroduced seed.inputs technology port person

theorem noCapital : NoCapital seed.current.actualLaw := noCapitalOfOpen _ seed.opened

end Seed
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Global
