import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaPatches.Compiler
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.CompilerRecovery

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms MotherExactPrograms
open MotherPatchInventory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

theorem every_compiler_patch_section (parent : M) (value : WriteProgramValue)
    (formed : MotherArenaExact.formWritePrograms parent = some value) (patches : PatchSection value) :
    ∃ material : M, formCompiler material = some ⟨value, compilerOfPatches value patches⟩ := by
  let writes : OriginalPatchRequests value := fun context =>
    originalWriteRequest value.2.2.2.1 value.2.2.2.2 value.2.2.1 context.1 (value.2.1 context.1) (patches context.1) context.2
  let ends : TerminalRequests value := fun point =>
    originalTerminalRequest value.2.2.2.1 value.2.2.2.2 value.2.2.1 point (value.2.1 point) (patches point)
  obtain ⟨material, inventories, selections, requestsFormed⟩ := every_complete_patch_requests parent value formed writes ends
  let bundle : AllRequestValue := ⟨⟨⟨⟨value, inventories⟩, selections⟩, writes⟩, ends⟩
  have parsed : ∀ point, parsePatchSection bundle point = some (patches point) :=
    fun point => parse_original value.2.2.2.1 value.2.2.2.2 value.2.2.1 point (value.2.1 point) (patches point)
  have checked : CompilerCheck bundle := fun point => by rw [parsed]; rfl
  have patchEq : (fun point => (parsePatchSection bundle point).get (checked point)) = patches := by
    funext point
    exact Option.some.inj ((Option.some_get _).trans (parsed point))
  have compilerEq : generatedCompiler bundle checked = compilerOfPatches value patches :=
    congrArg (compilerOfPatches value) patchEq
  refine ⟨material, ?_⟩
  unfold formCompiler
  rw [requestsFormed, Option.bind_some, dif_pos checked]
  exact congrArg (fun compiler => some (⟨value, compiler⟩ : CompilerValue)) compilerEq

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
