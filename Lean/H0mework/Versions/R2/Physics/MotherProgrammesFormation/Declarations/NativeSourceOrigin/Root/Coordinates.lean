import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.FullSource.Consumer

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLedgerRoot
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherPatchInventory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

def programmeParent (material : M) : M := requestParent (MotherHigherLawValue.split material).1

theorem all_requests_programmes_formed (material : M) (value : AllRequestValue)
    (formed : formAllRequests material = some value) :
    formWritePrograms (programmeParent material) = some (allProgramme value) := by
  unfold formAllRequests formAllRequestParts at formed
  dsimp only at formed
  obtain ⟨request, requestFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  split at selected
  · have same := congrArg Sigma.fst (Option.some.inj selected)
    exact (requests_programmes_formed _ _ requestFormed).trans (congrArg (fun request => some (requestProgramme request)) same)
  · cases selected

theorem compiler_programmes_formed (material : M) (value : CompilerValue)
    (formed : formCompiler material = some value) :
    formWritePrograms (programmeParent material) = some value.1 := by
  unfold formCompiler at formed
  obtain ⟨requests, requestFormed, selected⟩ := Option.bind_eq_some_iff.mp formed
  split at selected
  · exact (all_requests_programmes_formed _ _ requestFormed).trans
      (congrArg (fun value : CompilerValue => some value.1) (Option.some.inj selected))
  · cases selected

def compilerCoordinates (material : M) (value : CompilerValue)
    (formed : formCompiler material = some value) : Coordinates value.1.1.2.2 :=
  sourceCoordinates (programmeParent material) value.1 (compiler_programmes_formed material value formed)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLedgerRoot
