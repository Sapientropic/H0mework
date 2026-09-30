import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaCompiler.WholeEncoding

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaCompiler
open MotherArenaNetwork MotherFullCompiler
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

theorem whole_formed (parent material : M) (value : SourceValue) (coordinates : Coordinates (rank := rank) value.2.2)
    (targets : TargetSection value.2.2) (formed : formTargets parent = some ⟨value, coordinates, targets⟩)
    (checked : WholeSectionCheck coordinates (ledgerCoordinatesOfTargets parent value coordinates targets formed) targets material) :
    formWhole ((MotherArenaHigher.pack rank) (parent, material)) =
      some ⟨value, targets, generatedWhole coordinates
        (ledgerCoordinatesOfTargets parent value coordinates targets formed) targets material checked⟩ := by
  unfold formWhole
  rw [(MotherArenaHigher.split_pack rank)]
  dsimp only
  unfold formWholeParts
  apply Option.pbind_eq_some_iff.mpr
  refine ⟨⟨value, coordinates, targets⟩, formed, ?_⟩
  exact dif_pos checked

/-- The whole dependent section is paid by one additional source material;
the desired tables enter only this coverage proof. -/
theorem every_whole_section (parent : M) (value : SourceValue) (coordinates : Coordinates (rank := rank) value.2.2)
    (targets : TargetSection value.2.2) (formed : formTargets parent = some ⟨value, coordinates, targets⟩)
    (desired : WholeSection value.2.2 targets) :
    ∃ material : M, ∃ ledgers : WholeSection value.2.2 targets,
      formWhole material = some ⟨value, targets, ledgers⟩ ∧ ledgers = desired := by
  let ledgerCoordinates := ledgerCoordinatesOfTargets parent value coordinates targets formed
  obtain ⟨material, hm⟩ := (MotherArenaHigher.read_surjective rank)
    (WholeEncoding.reader value.2.2 ledgerCoordinates coordinates targets desired)
  let checked := WholeEncoding.checked value.2.2 ledgerCoordinates coordinates targets desired hm
  exact ⟨(MotherArenaHigher.pack rank) (parent, material),
    generatedWhole coordinates ledgerCoordinates targets material checked,
    whole_formed parent material value coordinates targets formed checked,
    WholeEncoding.generated_eq value.2.2 ledgerCoordinates coordinates targets desired hm⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaCompiler
