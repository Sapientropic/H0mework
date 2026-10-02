import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaPatches.TerminalCoordinates
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.TerminalBody

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms MotherExactPrograms
open MotherPatchInventory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (rows : LedgerTerminalRowSourceAt source)

def terminalItemAddress (ledger : MotherArenaCompiler.LedgerCoordinates (rank := rank) N) (eventCode : ∀ context, RowEvents rows context ↪ B)
    (point : Point source) : TerminalItem rows point ↪ B where
  toFun := fun item => (MotherArenaHigher.pair rank) (ledger.entry point.2.1 item.1, eventCode ⟨point, item.1⟩ item.2)
  inj' := by
    rintro ⟨entry, event⟩ ⟨entry', event'⟩ same
    have pairEq := (MotherArenaHigher.pairEquiv rank).injective same
    have same := (ledger.entry point.2.1).injective (congrArg Prod.fst pairEq)
    cases same
    have same := (eventCode ⟨point, entry⟩).injective (congrArg Prod.snd pairEq)
    cases same
    rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
