import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Root.Consumer
import H0mework.Foundation.Authority.SourceProjectionInventory

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProjectionOrigin
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherPatchInventory MotherLedgerRoot
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

/-- Full current/event addresses come from the actual root factory output,
not from a header supplied by the original projection law. -/
def rootCoordinates (material : M) (value : RootValue) (formed : formRoot material = some value) :
    Coordinates value.2.2.source.source := by
  unfold formRoot formRootParts at formed
  dsimp only at formed
  cases compilerFormed : formCompiler (MotherHigherLawValue.split material).1 with
  | none => simp only [compilerFormed, Option.pbind_none, reduceCtorEq] at formed
  | some compiler =>
      simp only [compilerFormed, Option.pbind_some] at formed
      split at formed
      · split at formed
        · exact Eq.mp (congrArg (fun result : RootValue => Coordinates result.2.2.source.source) (Option.some.inj formed))
            (compilerCoordinates (MotherHigherLawValue.split material).1 compiler compilerFormed)
        · cases formed
      · cases formed

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProjectionOrigin
