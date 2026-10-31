import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.State
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.AccountKeys

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument) (sourcePosition : Nat)
  (review : Option (ReviewPhase.ContextAt input) := none)

local notation "W" => N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "C" => Current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

theorem open_fibres : ∀ support responsibility, Subsingleton ((W).OpenAt support responsibility) :=
  Account.open_fibres (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

theorem wholeEvolution_keeps_keys (current : C) : Financial.Installation.KeepsKeys
    (wholeEvolution (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current) := by
  rcases current with ⟨phase⟩
  cases phase with
  | none => exact (initialLedger (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).2.prop
  | some account => exact Account.wholeEvolution_keeps_keys (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition account

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting
