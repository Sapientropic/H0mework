import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaAdmission.SharedNetwork
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.NetworkOrigin

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaAdmission
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms MotherExactPrograms MotherPatchInventory
open MotherLedgerRoot MotherProjectionOrigin MotherObligationOrigin MotherRestructuringReceipts
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open MotherInventoryAdmission
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

def compilerNativeMaterial (material : M) : M := MotherArenaPrograms.sourceMaterial (MotherArenaPatches.compilationMaterial (MotherArenaRoot.programmeParent material))

theorem compiler_native_formed (material : M) (value : MotherPatchInventory.CompilerValue)
    (formed : MotherArenaPatches.formCompiler material = some value) :
    MotherArenaSource.formSource (compilerNativeMaterial material) = some value.1.1 :=
  MotherArenaPrograms.compilation_source_formed _ _ value.1.2.1
    (MotherArenaPatches.programme_compilation_formed _ _ (MotherArenaRoot.compiler_programmes_formed material value formed))

def rootNativeMaterial (material : M) : M := compilerNativeMaterial ((MotherArenaHigher.split rank) material).1

theorem root_native_formed (material : M) (value : RootValue) (formed : MotherArenaRoot.formRoot material = some value) :
    MotherArenaSource.formSource (rootNativeMaterial material) = some ⟨value.1, value.2.1, value.2.2.source.source⟩ := by
  unfold MotherArenaRoot.formRoot MotherArenaRoot.formRootParts at formed
  dsimp only at formed
  obtain ⟨compiler, compilerFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  split at selected
  · split at selected
    · exact (compiler_native_formed _ _ compilerFormed).trans
        (congrArg (fun root : RootValue => some (⟨root.1, root.2.1, root.2.2.source.source⟩ : MotherArenaCompiler.SourceValue)) (Option.some.inj selected))
    · cases selected
  · cases selected

def lawNativeMaterial (material : M) : M :=
  rootNativeMaterial ((MotherArenaHigher.split rank) ((MotherArenaHigher.split rank) material).1).1

theorem law_native_formed (material : M) (value : LawValue) (formed : MotherArenaObligation.formLaw material = some value) :
    MotherArenaSource.formSource (lawNativeMaterial material) =
      some ⟨value.1.1.1, value.1.1.2.1, value.1.1.2.2.source.source⟩ :=
  root_native_formed _ value.1.1 (MotherArenaObligation.projection_root_formed _ value.1 (MotherArenaReceipts.law_projection_formed material value formed))

theorem restructuring_law_formed (material : M) (value : MotherRestructuringReceipts.CompilerValue)
    (formed : MotherArenaReceipts.formRestructuringCompiler material = some value) :
    MotherArenaObligation.formLaw ((MotherArenaHigher.split rank) material).1 = some value.1 := by
  unfold MotherArenaReceipts.formRestructuringCompiler MotherArenaReceipts.formCompilerParts at formed
  dsimp only at formed
  obtain ⟨law, lawFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  obtain ⟨certificates, certificatesFormed, same⟩ := Option.map_eq_some_iff.mp selected
  exact lawFormed.trans (congrArg (fun value : MotherRestructuringReceipts.CompilerValue => some value.1) same)

def restructuringNativeMaterial (material : M) : M := lawNativeMaterial ((MotherArenaHigher.split rank) material).1

theorem restructuring_native_formed (material : M) (value : MotherRestructuringReceipts.CompilerValue)
    (formed : MotherArenaReceipts.formRestructuringCompiler material = some value) :
    MotherArenaSource.formSource (restructuringNativeMaterial material) =
      some ⟨value.1.1.1.1, value.1.1.1.2.1, value.1.1.1.2.2.source.source⟩ :=
  law_native_formed _ value.1 (restructuring_law_formed material value formed)

theorem source_network_formed (material : M) (value : MotherArenaCompiler.SourceValue)
    (formed : MotherArenaSource.formSource material = some value) :
    formNetwork ((MotherArenaHigher.split rank) material).1 = some value.1 := by
  unfold MotherArenaSource.formSource MotherArenaSource.formComponents at formed
  dsimp only at formed
  split at formed
  · rename_i hn
    split at formed
    · split at formed
      · split at formed
        · split at formed
          · exact (MotherArenaSource.network_formed _ hn).trans
              (congrArg (fun value : MotherArenaCompiler.SourceValue => some value.1) (Option.some.inj formed))
          · cases formed
        · cases formed
      · cases formed
    · cases formed
  · cases formed

def networkMaterial (material : M) : M := ((MotherArenaHigher.split rank) (restructuringNativeMaterial material)).1

theorem restructuring_network_formed (material : M) (value : MotherRestructuringReceipts.CompilerValue)
    (formed : MotherArenaReceipts.formRestructuringCompiler material = some value) :
    formNetwork (networkMaterial material) = some value.1.1.1.1 :=
  source_network_formed _ _ (restructuring_native_formed material value formed)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaAdmission
