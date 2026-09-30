import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaRoot.Consumer
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Projection.Coordinates
import H0mework.Foundation.Authority.SourceProjectionInventory

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaProjection
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms MotherPatchInventory MotherLedgerRoot
open MotherPatchInventory
open MotherProjectionOrigin
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

/-- Full current/event addresses come from the actual root factory output,
not from a header supplied by the original projection law. -/
def rootCoordinates (material : M) (value : RootValue) (formed : MotherArenaRoot.formRoot material = some value) :
    MotherArenaCompiler.Coordinates (rank := rank) value.2.2.source.source := by
  unfold MotherArenaRoot.formRoot MotherArenaRoot.formRootParts at formed
  dsimp only at formed
  cases compilerFormed : MotherArenaPatches.formCompiler ((MotherArenaHigher.split rank) material).1 with
  | none => simp only [compilerFormed, Option.pbind_none, reduceCtorEq] at formed
  | some compiler =>
      simp only [compilerFormed, Option.pbind_some] at formed
      split at formed
      · split at formed
        · exact Eq.mp (congrArg (fun result : RootValue => MotherArenaCompiler.Coordinates (rank := rank) result.2.2.source.source) (Option.some.inj formed))
            (MotherArenaRoot.compilerCoordinates ((MotherArenaHigher.split rank) material).1 compiler compilerFormed)
        · cases formed
      · cases formed

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaProjection
