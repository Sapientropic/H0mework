import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaAdmission.Factory

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaTheory
open MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

structure Coordinates (N : WorldRelationNetwork.{0}) where
  support : N.Support ↪ B
  claim : N.Claim ↪ B
  obstruction : ∀ support, N.ObstructionAt support ↪ B
  holds : ∀ support claim, N.HoldsAt support claim ↪ B

private def canonicalCoordinates (material : M) (checked : MotherArenaNetwork.Check material) :
    Coordinates (rank := rank) (MotherArenaSource.network material checked) where
  support := ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  claim := ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  obstruction := fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  holds := fun _ _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩

def coordinatesOfNetwork (material : M) (N : WorldRelationNetwork.{0})
    (formed : MotherArenaNetwork.formNetwork material = some N) : Coordinates (rank := rank) N := by
  let checked := MotherArenaSource.network_check formed
  have same : MotherArenaSource.network material checked = N :=
    Option.some.inj ((MotherArenaSource.network_formed material checked).symm.trans formed)
  exact Eq.mp (congrArg (Coordinates (rank := rank)) same) (canonicalCoordinates material checked)

theorem sources_restructuring_formed (material : M) (value : SourcePair)
    (formed : MotherArenaAdmission.formSources material = some value) :
    MotherArenaReceipts.formRestructuringCompiler (MotherArenaHigher.split rank material).1 = some value.1 := by
  unfold MotherArenaAdmission.formSources MotherArenaAdmission.formSourcesParts at formed
  dsimp only at formed
  obtain ⟨represented, representedFormed, selected⟩ := Option.bind_eq_some_iff.mp formed
  obtain ⟨⟨N, V, actual⟩, _actualFormed, selected⟩ := Option.bind_eq_some_iff.mp selected
  split at selected
  · exact representedFormed.trans (congrArg (fun value : SourcePair => some value.1) (Option.some.inj selected))
  · cases selected

def coordinatesOfSources (material : M) (value : SourcePair)
    (formed : MotherArenaAdmission.formSources material = some value) : Coordinates (rank := rank) value.1.1.1.1.1 :=
  coordinatesOfNetwork (MotherArenaAdmission.networkMaterial (MotherArenaHigher.split rank material).1) _
    (MotherArenaAdmission.restructuring_network_formed _ value.1 (sources_restructuring_formed material value formed))

theorem data_sources_formed (material : M) (value : SourcePair) (data : PresentationData value)
    (formed : MotherArenaAdmission.formDeclarationData material = some ⟨value, data⟩) :
    MotherArenaAdmission.formSources (MotherArenaHigher.split rank material).1 = some value := by
  unfold MotherArenaAdmission.formDeclarationData at formed
  dsimp only at formed
  obtain ⟨pair, pairFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  obtain ⟨data, _dataFormed, same⟩ := Option.map_eq_some_iff.mp selected
  exact pairFormed.trans (congrArg some (congrArg Sigma.fst same))

def coordinatesOfData (material : M) (value : SourcePair) (data : PresentationData value)
    (formed : MotherArenaAdmission.formDeclarationData material = some ⟨value, data⟩) :
    Coordinates (rank := rank) value.1.1.1.1.1 :=
  coordinatesOfSources (MotherArenaHigher.split rank material).1 value (data_sources_formed material value data formed)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaTheory
