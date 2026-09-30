import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.CompilerFormation

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherPatchInventory
open MotherLedgerRoot MotherProjectionOrigin MotherObligationOrigin MotherRestructuringReceipts
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

def compilerNativeMaterial (material : M) : M := sourceMaterial (compilationMaterial (programmeParent material))

theorem compiler_native_formed (material : M) (value : MotherPatchInventory.CompilerValue)
    (formed : MotherPatchInventory.formCompiler material = some value) :
    MotherNativeSourceOrigin.formSource (compilerNativeMaterial material) = some value.1.1 :=
  compilation_source_formed _ _ value.1.2.1
    (programme_compilation_formed _ _ (compiler_programmes_formed material value formed))

def rootNativeMaterial (material : M) : M := compilerNativeMaterial (MotherHigherLawValue.split material).1

theorem root_native_formed (material : M) (value : RootValue) (formed : formRoot material = some value) :
    MotherNativeSourceOrigin.formSource (rootNativeMaterial material) = some ⟨value.1, value.2.1, value.2.2.source.source⟩ := by
  unfold formRoot formRootParts at formed
  dsimp only at formed
  obtain ⟨compiler, compilerFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  split at selected
  · split at selected
    · exact (compiler_native_formed _ _ compilerFormed).trans
        (congrArg (fun root : RootValue => some (⟨root.1, root.2.1, root.2.2.source.source⟩ : SourceValue)) (Option.some.inj selected))
    · cases selected
  · cases selected

def lawNativeMaterial (material : M) : M :=
  rootNativeMaterial (MotherHigherLawValue.split (MotherHigherLawValue.split material).1).1

theorem law_native_formed (material : M) (value : LawValue) (formed : formLaw material = some value) :
    MotherNativeSourceOrigin.formSource (lawNativeMaterial material) =
      some ⟨value.1.1.1, value.1.1.2.1, value.1.1.2.2.source.source⟩ :=
  root_native_formed _ value.1.1 (projection_root_formed _ value.1 (law_projection_formed material value formed))

theorem restructuring_law_formed (material : M) (value : MotherRestructuringReceipts.CompilerValue)
    (formed : formRestructuringCompiler material = some value) :
    formLaw (MotherHigherLawValue.split material).1 = some value.1 := by
  unfold formRestructuringCompiler MotherRestructuringReceipts.formCompilerParts at formed
  dsimp only at formed
  obtain ⟨law, lawFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  obtain ⟨certificates, certificatesFormed, same⟩ := Option.map_eq_some_iff.mp selected
  exact lawFormed.trans (congrArg (fun value : MotherRestructuringReceipts.CompilerValue => some value.1) same)

def restructuringNativeMaterial (material : M) : M := lawNativeMaterial (MotherHigherLawValue.split material).1

theorem restructuring_native_formed (material : M) (value : MotherRestructuringReceipts.CompilerValue)
    (formed : formRestructuringCompiler material = some value) :
    MotherNativeSourceOrigin.formSource (restructuringNativeMaterial material) =
      some ⟨value.1.1.1.1, value.1.1.1.2.1, value.1.1.1.2.2.source.source⟩ :=
  law_native_formed _ value.1 (restructuring_law_formed material value formed)

theorem source_network_formed (material : M) (value : SourceValue)
    (formed : MotherNativeSourceOrigin.formSource material = some value) :
    formNetwork (MotherHigherLawValue.split material).1 = some value.1 := by
  unfold MotherNativeSourceOrigin.formSource MotherNativeSourceOrigin.formComponents at formed
  dsimp only at formed
  split at formed
  · rename_i hn
    split at formed
    · split at formed
      · split at formed
        · split at formed
          · exact (MotherNativeSourceOrigin.network_formed _ hn).trans
              (congrArg (fun value : SourceValue => some value.1) (Option.some.inj formed))
          · cases formed
        · cases formed
      · cases formed
    · cases formed
  · cases formed

def networkMaterial (material : M) : M := (MotherHigherLawValue.split (restructuringNativeMaterial material)).1

theorem restructuring_network_formed (material : M) (value : MotherRestructuringReceipts.CompilerValue)
    (formed : formRestructuringCompiler material = some value) :
    formNetwork (networkMaterial material) = some value.1.1.1.1 :=
  source_network_formed _ _ (restructuring_native_formed material value formed)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
