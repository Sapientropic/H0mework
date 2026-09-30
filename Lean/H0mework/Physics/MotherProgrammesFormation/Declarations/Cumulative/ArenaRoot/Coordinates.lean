import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaPatches.FullConsumer
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Root.Coordinates

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaRoot
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms MotherExactPrograms MotherPatchInventory
open MotherPatchInventory
open MotherLedgerRoot
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

def programmeParent (material : M) : M := MotherArenaPatches.requestParent ((MotherArenaHigher.split rank) material).1

theorem all_requests_programmes_formed (material : M) (value : AllRequestValue)
    (formed : MotherArenaPatches.formAllRequests material = some value) :
    MotherArenaExact.formWritePrograms (programmeParent material) = some (allProgramme value) := by
  unfold MotherArenaPatches.formAllRequests MotherArenaPatches.formAllRequestParts at formed
  dsimp only at formed
  obtain ⟨request, requestFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  split at selected
  · have same := congrArg Sigma.fst (Option.some.inj selected)
    exact (MotherArenaPatches.requests_programmes_formed _ _ requestFormed).trans (congrArg (fun request => some (requestProgramme request)) same)
  · cases selected

theorem compiler_programmes_formed (material : M) (value : CompilerValue)
    (formed : MotherArenaPatches.formCompiler material = some value) :
    MotherArenaExact.formWritePrograms (programmeParent material) = some value.1 := by
  unfold MotherArenaPatches.formCompiler at formed
  obtain ⟨requests, requestFormed, selected⟩ := Option.bind_eq_some_iff.mp formed
  split at selected
  · exact (all_requests_programmes_formed _ _ requestFormed).trans
      (congrArg (fun value : CompilerValue => some value.1) (Option.some.inj selected))
  · cases selected

def compilerCoordinates (material : M) (value : CompilerValue)
    (formed : MotherArenaPatches.formCompiler material = some value) : MotherArenaCompiler.Coordinates (rank := rank) value.1.1.2.2 :=
  MotherArenaPatches.sourceCoordinates (programmeParent material) value.1 (compiler_programmes_formed material value formed)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaRoot
