import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.Account
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.EnterKeys

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

local notation "W" => Account.N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "seed" => Account.initial (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "normal" => Account.supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition seed

private def stationary (world : WorldRelationNetwork) (support : world.Support) :
    LedgerWriteEvolutionAt world ⟨support⟩ ⟨support⟩ where
  destination := fun entry => ⟨entry, .carried rfl HEq.rfl⟩
  origin := fun entry => ⟨entry, .carried rfl HEq.rfl⟩

/-- The original empty-prefix ingress enters the actual account representation;
all later source prefixes are already in that representation. -/
def initialLedger : Σ before : (W).Support, { evolution : LedgerWriteEvolutionAt W ⟨before⟩ ⟨normal⟩ // Financial.Installation.KeepsKeys evolution } := by
  rcases start with ⟨past, incoming⟩
  by_cases original : past = [] ∧ sourcePosition = 0
  · rcases original with ⟨empty, zero⟩
    subst past
    subst sourcePosition
    simpa only [Account.N, Account.seedRun, Inventory.completeRun, Inventory.beforeRun, Inventory.runAt,
      Epoch.Finance.ActualPast.run, Epoch.Finance.ActualPast.runFrom,
      NativeResponsibilityProcess.Run.concatRuns, Epoch.Finance.Future.world,
      Account.supportAt, Account.initial, Account.seedAccount, Inventory.accountAt, Inventory.before,
      Epoch.Finance.ActualPast.account, Epoch.Finance.ActualPast.foldFrom,
      Epoch.Finance.Future.Installed.support, Epoch.Finance.Future.support,
      Epoch.Finance.Future.Installed.nativeTail, Epoch.Finance.Future.Installed.initial,
      Epoch.Finance.Future.Installed.shape, Epoch.Finance.Future.Installed.frame,
      Financial.Installation.Runtime.Frame.cursor,
      Inventory.baseAccount, Epoch.Finance.Installation.Shape.enteredSupport] using
      (show Σ before : (Epoch.Finance.Future.Installed.base input depth count sourceDepth sourceCount).Support,
        { evolution : LedgerWriteEvolutionAt (Epoch.Finance.Future.Installed.base input depth count sourceDepth sourceCount)
          ⟨before⟩ ⟨(Epoch.Finance.Installation.Generated.shape input sourceDepth sourceCount).enteredSupport input depth count
            (Financial.Installation.Runtime.frames input sourceDepth sourceCount).visit.current⟩ // Financial.Installation.KeepsKeys evolution } from
        ⟨_, ⟨Epoch.Finance.Installation.Generated.enterEvolution input depth count sourceDepth sourceCount,
          generated_entry_keeps_every_original_key input depth count sourceDepth sourceCount⟩⟩)
  · exact ⟨_, ⟨stationary _ _, ⟨fun _ => rfl, fun _ => rfl⟩⟩⟩

theorem empty_initial_support_is_the_original_mapped_support :
    (initialLedger (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      (Physical.initial (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) proposal 0).1 =
      (Epoch.Finance.Installation.Generated.shape input sourceDepth sourceCount).mappedSupport input depth count
        (Financial.Installation.Runtime.frames input sourceDepth sourceCount).visit.current := by
  rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting
