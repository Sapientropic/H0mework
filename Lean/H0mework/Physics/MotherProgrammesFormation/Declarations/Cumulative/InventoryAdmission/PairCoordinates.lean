import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.Coordinates

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
open MotherNetworkFactory MotherFullCompiler
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

abbrev LedgerValue := Σ N : WorldRelationNetwork.{0}, Σ V : ConstructiveRoot.Vocabulary.{0}, SourceNativeLedgerSource N V

def coordinatesOfLedger (material : M) (value : LedgerValue)
    (formed : MotherPatchInventory.formLedgerSource material = some value) : SourceCoordinates value.2.2.source := by
  unfold MotherPatchInventory.formLedgerSource at formed
  cases compilerFormed : MotherPatchInventory.formCompiler material with
  | none => simp only [compilerFormed, Option.map_none, reduceCtorEq] at formed
  | some compiler =>
      simp only [compilerFormed, Option.map_some] at formed
      exact Eq.mp (congrArg (fun value : LedgerValue => SourceCoordinates value.2.2.source) (Option.some.inj formed))
        (coordinatesOfNativeSource (compilerNativeMaterial material) compiler.1.1 (compiler_native_formed material compiler compilerFormed))

def coordinatesOfRestructuring (material : M) (value : MotherRestructuringReceipts.CompilerValue)
    (formed : MotherRestructuringReceipts.formRestructuringCompiler material = some value) :
    SourceCoordinates (MotherRestructuringReceipts.sourceOf value).source :=
  coordinatesOfNativeSource (restructuringNativeMaterial material) _ (restructuring_native_formed material value formed)

structure PairCoordinates (value : SourcePair) where
  represented : SourceCoordinates (MotherRestructuringReceipts.sourceOf value.1).source
  actual : SourceCoordinates value.2.2.source

def coordinatesOfPair (material : M) (value : SourcePair) (formed : formSources material = some value) : PairCoordinates value := by
  unfold formSources formSourcesParts at formed
  dsimp only at formed
  cases parentFormed : MotherRestructuringReceipts.formRestructuringCompiler (MotherHigherLawValue.split material).1 with
  | none => simp only [parentFormed, Option.bind_none, reduceCtorEq] at formed
  | some parent =>
      simp only [parentFormed, Option.bind_some] at formed
      cases actualFormed : MotherPatchInventory.formLedgerSource (MotherHigherLawValue.split material).2 with
      | none => simp only [actualFormed, Option.bind_none, reduceCtorEq] at formed
      | some actual =>
          rcases actual with ⟨N, V, actual⟩
          simp only [actualFormed, Option.bind_some] at formed
          split at formed
          · rename_i same
            cases same
            exact Eq.mp (congrArg PairCoordinates (Option.some.inj formed))
              { represented := coordinatesOfRestructuring (MotherHigherLawValue.split material).1 parent parentFormed
                actual := coordinatesOfLedger (MotherHigherLawValue.split material).2 _ actualFormed }
          · cases formed

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
