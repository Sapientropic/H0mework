import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Decision.Types

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Decision

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin : RawCurrent Party Good Technology Instrument) (members : List Party)
  (depth count prefixLimit renewalLimit : Nat)

private def repair (current : Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (cause : Cause input origin members prefixLimit renewalLimit current) :
    Outcome input origin members depth count prefixLimit renewalLimit current :=
  match Repair.choose input depth count current.raw
      (cause.focus input origin members prefixLimit renewalLimit) current.remaining with
  | .attempt attempt => .action (.repair cause attempt)
  | .exhausted rejected => .blocked ⟨cause,rejected⟩

/-- All checks use this explicit law/current/roster. No changed Input is
registered and no history is reconstructed under the checker view. -/
def compile (current : Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :
    Outcome input origin members depth count prefixLimit renewalLimit current :=
  match phase : current.phase with
  | .seeking =>
      match source : Material.Migration.Preferred.compile input origin current.raw members prefixLimit renewalLimit with
      | .accepted plan => .action (.migration plan source)
      | .obstructed issue => repair input origin members depth count prefixLimit renewalLimit current (.migration issue)
  | .renewal word =>
      match Review.Guarded.inspect input origin current.raw members word with
      | .accepted checked => .action (.renewal word phase checked)
      | .rejected issue => repair input origin members depth count prefixLimit renewalLimit current (.renewal word issue)

attribute [local simp] compile

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Decision
