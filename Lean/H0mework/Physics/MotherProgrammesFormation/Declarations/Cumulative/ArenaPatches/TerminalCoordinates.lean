import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaPatches.PatchFormation
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.TerminalCoordinates

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

def requestParent (material : M) : M :=
  ((MotherArenaHigher.split rank) ((MotherArenaHigher.split rank) ((MotherArenaHigher.split rank) material).1).1).1

theorem requests_programmes_formed (material : M) (value : RequestValue)
    (formed : formPatchRequests material = some value) :
    MotherArenaExact.formWritePrograms (requestParent material) = some (requestProgramme value) := by
  unfold formPatchRequests formPatchRequestParts at formed
  dsimp only at formed
  obtain ⟨base, baseFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  have same := congrArg Sigma.fst (Option.some.inj selected)
  have selectedFormed := baseFormed.trans (congrArg some same)
  exact inventory_programmes_formed _ _ (selections_inventory_formed _ _ selectedFormed)

def terminalParent (material : M) : M :=
  ((MotherArenaHigher.split rank) ((MotherArenaHigher.split rank) material).1).1

theorem programmes_terminal_formed (material : M) (value : WriteProgramValue)
    (formed : MotherArenaExact.formWritePrograms material = some value) :
    MotherArenaPrograms.formTerminalSource (terminalParent material) = some ⟨value.1, value.2.1, value.2.2.1⟩ :=
  MotherArenaExact.transitions_terminal_formed _ _ _ _ _ (write_transitions_formed material value formed)

def terminalAddresses (material : M) (value : WriteProgramValue) (formed : MotherArenaExact.formWritePrograms material = some value) :
    ∀ context, RowEvents value.2.2.1 context ↪ B := by
  have origin := programmes_terminal_formed material value formed
  have compiledOrigin := MotherArenaExact.terminal_compilation_formed _ _ _ _ origin
  unfold MotherArenaPrograms.formTerminalSource at origin
  dsimp only at origin
  simp only [compiledOrigin, Option.pbind_some] at origin
  split at origin
  · have same := Option.some.inj origin
    exact Eq.mp (congrArg (fun result : Σ value : MotherArenaCompiler.SourceValue,
      CompilationSection value.2.2 × LedgerTerminalRowSourceAt value.2.2 => ∀ context, RowEvents result.2.2 context ↪ B) same)
      (fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩)
  · cases origin

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
