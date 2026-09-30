import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaAdmission.Coordinates
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.PairCoordinates

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaAdmission
open MotherArenaNetwork MotherFullCompiler
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open MotherInventoryAdmission
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

def coordinatesOfLedger (material : M) (value : LedgerValue)
    (formed : MotherArenaPatches.formLedgerSource material = some value) : SourceCoordinates (rank := rank) value.2.2.source := by
  unfold MotherArenaPatches.formLedgerSource at formed
  cases compilerFormed : MotherArenaPatches.formCompiler material with
  | none => simp only [compilerFormed, Option.map_none, reduceCtorEq] at formed
  | some compiler =>
      simp only [compilerFormed, Option.map_some] at formed
      exact Eq.mp (congrArg (fun value : LedgerValue => SourceCoordinates (rank := rank) value.2.2.source) (Option.some.inj formed))
        (coordinatesOfNativeSource (compilerNativeMaterial material) compiler.1.1 (compiler_native_formed material compiler compilerFormed))

def coordinatesOfRestructuring (material : M) (value : MotherRestructuringReceipts.CompilerValue)
    (formed : MotherArenaReceipts.formRestructuringCompiler material = some value) :
    SourceCoordinates (rank := rank) (MotherRestructuringReceipts.sourceOf value).source :=
  coordinatesOfNativeSource (restructuringNativeMaterial material) _ (restructuring_native_formed material value formed)

structure PairCoordinates (value : SourcePair) where
  represented : SourceCoordinates (rank := rank) (MotherRestructuringReceipts.sourceOf value.1).source
  actual : SourceCoordinates (rank := rank) value.2.2.source

def coordinatesOfPair (material : M) (value : SourcePair) (formed : formSources material = some value) : PairCoordinates (rank := rank) value := by
  unfold formSources formSourcesParts at formed
  dsimp only at formed
  cases parentFormed : MotherArenaReceipts.formRestructuringCompiler ((MotherArenaHigher.split rank) material).1 with
  | none => simp only [parentFormed, Option.bind_none, reduceCtorEq] at formed
  | some parent =>
      simp only [parentFormed, Option.bind_some] at formed
      cases actualFormed : MotherArenaPatches.formLedgerSource ((MotherArenaHigher.split rank) material).2 with
      | none => simp only [actualFormed, Option.bind_none, reduceCtorEq] at formed
      | some actual =>
          rcases actual with ⟨N, V, actual⟩
          simp only [actualFormed, Option.bind_some] at formed
          split at formed
          · rename_i same
            cases same
            exact Eq.mp (congrArg (PairCoordinates (rank := rank)) (Option.some.inj formed))
              { represented := coordinatesOfRestructuring ((MotherArenaHigher.split rank) material).1 parent parentFormed
                actual := coordinatesOfLedger ((MotherArenaHigher.split rank) material).2 _ actualFormed }
          · cases formed

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaAdmission
