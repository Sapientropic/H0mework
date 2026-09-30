import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.CompilerRecovery

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherExactPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

/-- The original full source constructor consumes the formed compiler,
including its actual branch-indexed patch and complete fold equality. -/
theorem every_ledger_source_from_programmes (parent : M) (value : WriteProgramValue)
    (formed : formWritePrograms parent = some value) (patches : PatchSection value) :
    ∃ material : M,
      formCompiler material = some ⟨value, compilerOfPatches value patches⟩ ∧
      formLedgerSource material = some ⟨value.1.1, value.1.2.1,
        (⟨value.1.2.2, compilerOfPatches value patches⟩ : SourceNativeLedgerSource value.1.1 value.1.2.1)⟩ := by
  obtain ⟨material, compiled⟩ := every_compiler_patch_section parent value formed patches
  refine ⟨material, compiled, ?_⟩
  unfold formLedgerSource
  rw [compiled]
  rfl

theorem compiler_patch_original (value : WriteProgramValue) (patches : PatchSection value)
    (point : Point value.1.2.2) :
    (compilerOfPatches value patches).compilePatch point.2 = patches point := rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
