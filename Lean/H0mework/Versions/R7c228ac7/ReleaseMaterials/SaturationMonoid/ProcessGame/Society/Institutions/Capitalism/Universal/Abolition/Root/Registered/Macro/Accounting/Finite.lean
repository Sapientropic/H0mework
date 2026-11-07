import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.Keys
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.AccountFinite

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
  (current : Current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)

theorem entries_finite : Finite (OpenResponsibilityAt
    (N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
    (supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current)) := by
  rcases current with ⟨phase⟩
  cases phase with
  | none =>
      let := Account.entries_finite (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
        (Account.initial (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
      let transition := (initialLedger (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).2
      exact Finite.of_injective (fun entry => (transition.val.destination entry).1)
        (Financial.Installation.keys_imply_destination_injective transition.val transition.prop
          (open_fibres (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition))
  | some account => exact Account.entries_finite (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition account

@[instance_reducible] def entryFintype : Fintype (OpenResponsibilityAt
    (N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
    (supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current)) := by
  letI := entries_finite (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current
  exact Fintype.ofFinite _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting
