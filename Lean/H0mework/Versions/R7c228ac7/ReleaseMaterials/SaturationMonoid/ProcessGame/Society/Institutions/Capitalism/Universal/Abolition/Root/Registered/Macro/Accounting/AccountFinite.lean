import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.Account

import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Finiteness

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.Account

open Epoch.Finance.Future.Finiteness
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

variable (prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument) (sourcePosition : Nat)
  (review : Option (ReviewPhase.ContextAt input) := none)
  (current : Current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)

theorem entries_finite : Finite (OpenResponsibilityAt
    (N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
    (supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current)) :=
  future_support_finite input depth count _ _
    (shape_support_finite input depth count _ _ current.account _) _ current.account current.native

@[instance_reducible] def entryFintype : Fintype (OpenResponsibilityAt
    (N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
    (supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current)) := by
  letI := entries_finite (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current
  exact Fintype.ofFinite _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.Account
