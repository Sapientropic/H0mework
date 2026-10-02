import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.PatchFormation

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherExactPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

abbrev RequestValue := Σ value : SelectionValue, PatchRequests value

def requestProgramme (value : RequestValue) : WriteProgramValue := value.1.1.1

def requestParent (material : M) : M :=
  (MotherHigherLawValue.split (MotherHigherLawValue.split (MotherHigherLawValue.split material).1).1).1

theorem requests_programmes_formed (material : M) (value : RequestValue)
    (formed : formPatchRequests material = some value) :
    formWritePrograms (requestParent material) = some (requestProgramme value) := by
  unfold formPatchRequests formPatchRequestParts at formed
  dsimp only at formed
  obtain ⟨base, baseFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  have same := congrArg Sigma.fst (Option.some.inj selected)
  have selectedFormed := baseFormed.trans (congrArg some same)
  exact inventory_programmes_formed _ _ (selections_inventory_formed _ _ selectedFormed)

def terminalParent (material : M) : M :=
  (MotherHigherLawValue.split (MotherHigherLawValue.split material).1).1

theorem programmes_terminal_formed (material : M) (value : WriteProgramValue)
    (formed : formWritePrograms material = some value) :
    formTerminalSource (terminalParent material) = some ⟨value.1, value.2.1, value.2.2.1⟩ :=
  transitions_terminal_formed _ _ _ _ _ (write_transitions_formed material value formed)

def terminalAddresses (material : M) (value : WriteProgramValue) (formed : formWritePrograms material = some value) :
    ∀ context, RowEvents value.2.2.1 context ↪ B := by
  have origin := programmes_terminal_formed material value formed
  have compiledOrigin := terminal_compilation_formed _ _ _ _ origin
  unfold formTerminalSource at origin
  dsimp only at origin
  simp only [compiledOrigin, Option.pbind_some] at origin
  split at origin
  · have same := Option.some.inj origin
    exact Eq.mp (congrArg (fun result : Σ value : SourceValue,
      CompilationSection value.2.2 × LedgerTerminalRowSourceAt value.2.2 => ∀ context, RowEvents result.2.2 context ↪ B) same)
      (fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩)
  · cases origin

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
