import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaAdmission.PresentationData

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaAdmission
open MotherInventoryAdmission
noncomputable section
variable {rank : Ordinal.{0}}
local notation "M" => MotherArenaHigher.Material rank

/-- Both full source declarations and all four dependent presentation
programmes come from the actual material output before native restriction. -/
def formDeclarationData (material : M) : Option (Σ value : SourcePair, PresentationData value) :=
  let parts := MotherArenaHigher.split rank material
  (formSources parts.1).pbind (fun value formed =>
    (formPresentationData value (coordinatesOfPair parts.1 value formed) parts.2).map (fun data => ⟨value, data⟩))

theorem every_declaration_data (parent : M) (value : SourcePair) (formed : formSources parent = some value)
    (data : PresentationData value) :
    ∃ material : M, formDeclarationData material = some ⟨value, data⟩ := by
  obtain ⟨material, dataFormed⟩ := every_presentation_data value (coordinatesOfPair parent value formed) data
  refine ⟨MotherArenaHigher.pack rank (parent, material), ?_⟩
  simp only [formDeclarationData, MotherArenaHigher.split_pack, formed, Option.pbind_some]
  rw [dataFormed]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaAdmission
