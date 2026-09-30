import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaExact.Consumer
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.Coordinates

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

theorem write_transitions_formed (material : M) (value : WriteProgramValue)
    (formed : MotherArenaExact.formWritePrograms material = some value) :
    MotherArenaExact.formTransitions ((MotherArenaHigher.split rank) material).1 = some (transitionValue value) := by
  unfold MotherArenaExact.formWritePrograms MotherArenaExact.formWriteProgramParts at formed
  dsimp only at formed
  obtain ⟨base, baseFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  split at selected
  · split at selected
    · exact baseFormed.trans (congrArg some (congrArg transitionValue (Option.some.inj selected)))
    · cases selected
  · cases selected

def rowAddresses (material : M) (value : WriteProgramValue) (formed : MotherArenaExact.formWritePrograms material = some value) :
    ∀ context, WriteEvents value.2.2.2.2 context ↪ B := by
  have origin := write_transitions_formed material value formed
  unfold MotherArenaExact.formWritePrograms MotherArenaExact.formWriteProgramParts at formed
  dsimp only at formed
  simp only [origin, Option.pbind_some] at formed
  split at formed
  · split at formed
    · have same := Option.some.inj formed
      exact Eq.mp (congrArg (fun result : WriteProgramValue => ∀ context, WriteEvents result.2.2.2.2 context ↪ B) same)
        (fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩)
    · cases formed
  · cases formed

def compilationMaterial (material : M) : M :=
  ((MotherArenaHigher.split rank) ((MotherArenaHigher.split rank) ((MotherArenaHigher.split rank) material).1).1).1

theorem programme_compilation_formed (material : M) (value : WriteProgramValue)
    (formed : MotherArenaExact.formWritePrograms material = some value) :
    MotherArenaCompiler.formCompilation (compilationMaterial material) = some ⟨value.1, value.2.1⟩ :=
  MotherArenaExact.terminal_compilation_formed ((MotherArenaHigher.split rank) ((MotherArenaHigher.split rank) material).1).1
    value.1 value.2.1 value.2.2.1
    (MotherArenaExact.transitions_terminal_formed ((MotherArenaHigher.split rank) material).1 value.1 value.2.1 value.2.2.1 value.2.2.2.1
      (write_transitions_formed material value formed))

def sourceCoordinates (material : M) (value : WriteProgramValue) (formed : MotherArenaExact.formWritePrograms material = some value) :
    MotherArenaCompiler.Coordinates (rank := rank) value.1.2.2 :=
  MotherArenaPrograms.coordinatesOfCompilation (compilationMaterial material) value.1 value.2.1 (programme_compilation_formed material value formed)

def ledgerCoordinates (material : M) (value : WriteProgramValue) (formed : MotherArenaExact.formWritePrograms material = some value) :
    MotherArenaCompiler.LedgerCoordinates (rank := rank) value.1.1 :=
  MotherArenaPrograms.ledgerCoordinatesOfCompilation (compilationMaterial material) value.1 value.2.1 (programme_compilation_formed material value formed)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
