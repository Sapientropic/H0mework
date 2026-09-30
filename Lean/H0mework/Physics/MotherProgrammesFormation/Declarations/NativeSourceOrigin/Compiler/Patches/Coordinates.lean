import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Joint.Consumer

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherExactPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

def transitionValue (value : WriteProgramValue) : TransitionValue :=
  ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1⟩

theorem write_transitions_formed (material : M) (value : WriteProgramValue)
    (formed : formWritePrograms material = some value) :
    formTransitions (MotherHigherLawValue.split material).1 = some (transitionValue value) := by
  unfold formWritePrograms formWriteProgramParts at formed
  dsimp only at formed
  obtain ⟨base, baseFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  split at selected
  · split at selected
    · exact baseFormed.trans (congrArg some (congrArg transitionValue (Option.some.inj selected)))
    · cases selected
  · cases selected

def rowAddresses (material : M) (value : WriteProgramValue) (formed : formWritePrograms material = some value) :
    ∀ context, WriteEvents value.2.2.2.2 context ↪ B := by
  have origin := write_transitions_formed material value formed
  unfold formWritePrograms formWriteProgramParts at formed
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
  (MotherHigherLawValue.split (MotherHigherLawValue.split (MotherHigherLawValue.split material).1).1).1

theorem programme_compilation_formed (material : M) (value : WriteProgramValue)
    (formed : formWritePrograms material = some value) :
    formCompilation (compilationMaterial material) = some ⟨value.1, value.2.1⟩ :=
  terminal_compilation_formed (MotherHigherLawValue.split (MotherHigherLawValue.split material).1).1
    value.1 value.2.1 value.2.2.1
    (transitions_terminal_formed (MotherHigherLawValue.split material).1 value.1 value.2.1 value.2.2.1 value.2.2.2.1
      (write_transitions_formed material value formed))

def sourceCoordinates (material : M) (value : WriteProgramValue) (formed : formWritePrograms material = some value) :
    Coordinates value.1.2.2 :=
  coordinatesOfCompilation (compilationMaterial material) value.1 value.2.1 (programme_compilation_formed material value formed)

def ledgerCoordinates (material : M) (value : WriteProgramValue) (formed : formWritePrograms material = some value) :
    LedgerCoordinates value.1.1 :=
  ledgerCoordinatesOfCompilation (compilationMaterial material) value.1 value.2.1 (programme_compilation_formed material value formed)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
