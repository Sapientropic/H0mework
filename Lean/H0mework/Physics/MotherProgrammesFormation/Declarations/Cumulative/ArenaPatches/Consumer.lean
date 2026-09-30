import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaPatches.CompilerRecovery
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.Consumer

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

/-- The original full source constructor consumes the formed compiler,
including its actual branch-indexed patch and complete fold equality. -/
theorem every_ledger_source_from_programmes (parent : M) (value : WriteProgramValue)
    (formed : MotherArenaExact.formWritePrograms parent = some value) (patches : PatchSection value) :
    ∃ material : M,
      formCompiler material = some ⟨value, compilerOfPatches value patches⟩ ∧
      formLedgerSource material = some ⟨value.1.1, value.1.2.1,
        (⟨value.1.2.2, compilerOfPatches value patches⟩ : SourceNativeLedgerSource value.1.1 value.1.2.1)⟩ := by
  obtain ⟨material, compiled⟩ := every_compiler_patch_section parent value formed patches
  refine ⟨material, compiled, ?_⟩
  unfold formLedgerSource
  rw [compiled]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
