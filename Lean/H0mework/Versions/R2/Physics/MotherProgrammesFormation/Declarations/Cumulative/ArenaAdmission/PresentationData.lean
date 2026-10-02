import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaAdmission.PairCoordinates
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.PresentationData

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaAdmission
open MotherArenaNetwork
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open MotherInventoryAdmission
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

private def oneIndex : Unit ↪ B := ⟨fun _ => (MotherArenaRestructuringVocabulary.natTag (rank := rank)) 0, fun _ _ _ => Subsingleton.elim _ _⟩

def formPresentation {A C : Type} (left : A ↪ B) (right : C ↪ B) (material : M) : Option (ConstructivePresentation A C) :=
  (formPresentationSection oneIndex (fun _ => left) (fun _ => right) material).map (fun family => family ())

theorem every_presentation {A C : Type} (left : A ↪ B) (right : C ↪ B) (original : ConstructivePresentation A C) :
    ∃ material : M, formPresentation left right material = some original := by
  obtain ⟨material, formed⟩ := every_presentation_section oneIndex (fun _ => left) (fun _ => right) (fun _ => original)
  refine ⟨material, ?_⟩
  simp only [formPresentation, formed, Option.map_some]

variable (value : SourcePair) (coordinates : PairCoordinates (rank := rank) value)

def formPresentationParts (currentMaterial occurrenceMaterial evolutionMaterial cofinalMaterial : M) : Option (PresentationData value) :=
  (formPresentation coordinates.actual.current coordinates.represented.current currentMaterial).bind (fun current =>
    (formPresentationSection coordinates.represented.current
      (fun point => coordinates.actual.event (current.backward point)) coordinates.represented.event occurrenceMaterial).bind (fun occurrence =>
        (formPresentationSection coordinates.represented.current
          (fun point => coordinates.actual.vocabulary.evolution (current.backward point)) coordinates.represented.vocabulary.evolution evolutionMaterial).bind (fun evolution =>
            (formPresentation coordinates.actual.vocabulary.cofinal coordinates.represented.vocabulary.cofinal cofinalMaterial).map
              (fun cofinal => ⟨current, occurrence, evolution, cofinal⟩))))

def formPresentationData (material : M) : Option (PresentationData value) :=
  let first := (MotherArenaHigher.split rank) material
  let second := (MotherArenaHigher.split rank) first.2
  let third := (MotherArenaHigher.split rank) second.2
  formPresentationParts value coordinates first.1 second.1 third.1 third.2

theorem every_presentation_data (original : PresentationData value) :
    ∃ material : M, formPresentationData value coordinates material = some original := by
  obtain ⟨currentMaterial, currentFormed⟩ := every_presentation coordinates.actual.current coordinates.represented.current original.current
  obtain ⟨occurrenceMaterial, occurrenceFormed⟩ := every_presentation_section coordinates.represented.current
    (fun point => coordinates.actual.event (original.current.backward point)) coordinates.represented.event original.occurrence
  obtain ⟨evolutionMaterial, evolutionFormed⟩ := every_presentation_section coordinates.represented.current
    (fun point => coordinates.actual.vocabulary.evolution (original.current.backward point)) coordinates.represented.vocabulary.evolution original.evolution
  obtain ⟨cofinalMaterial, cofinalFormed⟩ := every_presentation coordinates.actual.vocabulary.cofinal coordinates.represented.vocabulary.cofinal original.cofinal
  refine ⟨(MotherArenaHigher.pack rank) (currentMaterial, (MotherArenaHigher.pack rank)
    (occurrenceMaterial, (MotherArenaHigher.pack rank) (evolutionMaterial, cofinalMaterial))), ?_⟩
  simp only [formPresentationData, MotherArenaHigher.split_pack, formPresentationParts, currentFormed,
    Option.bind_some, occurrenceFormed, evolutionFormed, cofinalFormed, Option.map_some]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaAdmission
