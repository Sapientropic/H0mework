import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaTheory.Coverage

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityCoordinates
open MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}

abbrev Output := Σ declaration : (Σ value : SourcePair, PresentationData value),
  TheoryState declaration.1.1.1.1.1.1

def declarationMaterial (material : MotherArenaHigher.Material rank) :=
  (MotherArenaHigher.split rank material).1

theorem declaration_formed (material : MotherArenaHigher.Material rank) (output : Output)
    (formed : MotherArenaTheory.formTheory material = some output) :
    MotherArenaAdmission.formDeclarationData (declarationMaterial material) = some output.1 := by
  unfold MotherArenaTheory.formTheory MotherArenaTheory.formTheoryParts at formed
  dsimp only at formed
  obtain ⟨declaration, parentFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  obtain ⟨surface, _surfaceFormed, same⟩ := Option.map_eq_some_iff.mp selected
  exact parentFormed.trans (congrArg some (congrArg Sigma.fst same))

def sourceMaterial (material : MotherArenaHigher.Material rank) :=
  (MotherArenaHigher.split rank (declarationMaterial material)).1

theorem sources_formed (material : MotherArenaHigher.Material rank) (output : Output)
    (formed : MotherArenaTheory.formTheory material = some output) :
    MotherArenaAdmission.formSources (sourceMaterial material) = some output.1.1 :=
  MotherArenaTheory.data_sources_formed (declarationMaterial material) output.1.1 output.1.2
    (declaration_formed material output formed)

def sourceCoordinates (material : MotherArenaHigher.Material rank) (output : Output)
    (formed : MotherArenaTheory.formTheory material = some output) :
    MotherArenaAdmission.PairCoordinates (rank := rank) output.1.1 :=
  MotherArenaAdmission.coordinatesOfPair (sourceMaterial material) output.1.1 (sources_formed material output formed)

def nativeMaterial (material : MotherArenaHigher.Material rank) :=
  MotherArenaAdmission.restructuringNativeMaterial (MotherArenaHigher.split rank (sourceMaterial material)).1

theorem native_formed (material : MotherArenaHigher.Material rank) (output : Output)
    (formed : MotherArenaTheory.formTheory material = some output) :
    MotherArenaSource.formSource (nativeMaterial material) =
      some ⟨output.1.1.1.1.1.1.1, RepresentedV output.1.1, (Represented output.1.1).source⟩ :=
  MotherArenaAdmission.restructuring_native_formed _ output.1.1.1
    (MotherArenaTheory.sources_restructuring_formed (sourceMaterial material) output.1.1
      (sources_formed material output formed))

def ledgerCoordinates (material : MotherArenaHigher.Material rank) (output : Output)
    (formed : MotherArenaTheory.formTheory material = some output) :
    MotherArenaCompiler.LedgerCoordinates (rank := rank) output.1.1.1.1.1.1.1 :=
  MotherArenaCompiler.ledgerCoordinatesOfFormation (nativeMaterial material) _ (native_formed material output formed)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityCoordinates
