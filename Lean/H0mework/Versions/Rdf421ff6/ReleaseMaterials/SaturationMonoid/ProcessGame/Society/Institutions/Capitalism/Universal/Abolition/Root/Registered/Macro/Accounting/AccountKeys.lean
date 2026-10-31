import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.Account
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Structure

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.Account

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Financial.Installation (KeepsKeys)
open Epoch.Finance.Future.Structure

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

variable (prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument) (sourcePosition : Nat)
  (review : Option (ReviewPhase.ContextAt input) := none)

local notation "W" => N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "C" => Current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

theorem open_fibres : ∀ support responsibility, Subsingleton ((W).OpenAt support responsibility) :=
  future_fibres input depth count _ (shape_fibres input depth count _) _

theorem wholeEvolution_keeps_keys (current : C) :
    KeepsKeys (wholeEvolution (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current) := by
  unfold wholeEvolution
  cases item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current with
  | some item =>
      exact future_evolution_keys input depth count _ _ _
        (shape_evolution_keys input depth count _ _ _ current.account _ _) _ current.account current.native _
  | none => exact ⟨fun _ => rfl, fun _ => rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.Account
