import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.PairCoordinates

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
open MotherNetworkFactory
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

private def oneIndex : Unit ↪ B := ⟨fun _ => MotherRestructuringOrigin.natTag 0, fun _ _ _ => Subsingleton.elim _ _⟩

def formPresentation {A C : Type} (left : A ↪ B) (right : C ↪ B) (material : M) : Option (ConstructivePresentation A C) :=
  (formPresentationSection oneIndex (fun _ => left) (fun _ => right) material).map (fun family => family ())

theorem every_presentation {A C : Type} (left : A ↪ B) (right : C ↪ B) (original : ConstructivePresentation A C) :
    ∃ material : M, formPresentation left right material = some original := by
  obtain ⟨material, formed⟩ := every_presentation_section oneIndex (fun _ => left) (fun _ => right) (fun _ => original)
  refine ⟨material, ?_⟩
  simp only [formPresentation, formed, Option.map_some]

abbrev Represented (value : SourcePair) := MotherRestructuringReceipts.sourceOf value.1
abbrev RepresentedV (value : SourcePair) := value.1.1.1.1.2.1

structure PresentationData (value : SourcePair) where
  current : ConstructivePresentation value.2.1.Current (RepresentedV value).Current
  occurrence : ∀ point : (RepresentedV value).Current, ConstructivePresentation
    (value.2.2.source.toRootSource.actual.OccurrenceAt (current.backward point))
    ((Represented value).source.toRootSource.actual.OccurrenceAt point)
  evolution : ∀ point : (RepresentedV value).Current, ConstructivePresentation (EvolutionAt value.2.1 (current.backward point)) (EvolutionAt (RepresentedV value) point)
  cofinal : ConstructivePresentation value.2.1.cofinal.Event (RepresentedV value).cofinal.Event

variable (value : SourcePair) (coordinates : PairCoordinates value)

def formPresentationParts (currentMaterial occurrenceMaterial evolutionMaterial cofinalMaterial : M) : Option (PresentationData value) :=
  (formPresentation coordinates.actual.current coordinates.represented.current currentMaterial).bind (fun current =>
    (formPresentationSection coordinates.represented.current
      (fun point => coordinates.actual.event (current.backward point)) coordinates.represented.event occurrenceMaterial).bind (fun occurrence =>
        (formPresentationSection coordinates.represented.current
          (fun point => coordinates.actual.vocabulary.evolution (current.backward point)) coordinates.represented.vocabulary.evolution evolutionMaterial).bind (fun evolution =>
            (formPresentation coordinates.actual.vocabulary.cofinal coordinates.represented.vocabulary.cofinal cofinalMaterial).map
              (fun cofinal => ⟨current, occurrence, evolution, cofinal⟩))))

def formPresentationData (material : M) : Option (PresentationData value) :=
  let first := MotherHigherLawValue.split material
  let second := MotherHigherLawValue.split first.2
  let third := MotherHigherLawValue.split second.2
  formPresentationParts value coordinates first.1 second.1 third.1 third.2

theorem every_presentation_data (original : PresentationData value) :
    ∃ material : M, formPresentationData value coordinates material = some original := by
  obtain ⟨currentMaterial, currentFormed⟩ := every_presentation coordinates.actual.current coordinates.represented.current original.current
  obtain ⟨occurrenceMaterial, occurrenceFormed⟩ := every_presentation_section coordinates.represented.current
    (fun point => coordinates.actual.event (original.current.backward point)) coordinates.represented.event original.occurrence
  obtain ⟨evolutionMaterial, evolutionFormed⟩ := every_presentation_section coordinates.represented.current
    (fun point => coordinates.actual.vocabulary.evolution (original.current.backward point)) coordinates.represented.vocabulary.evolution original.evolution
  obtain ⟨cofinalMaterial, cofinalFormed⟩ := every_presentation coordinates.actual.vocabulary.cofinal coordinates.represented.vocabulary.cofinal original.cofinal
  refine ⟨MotherHigherLawValue.pack (currentMaterial, MotherHigherLawValue.pack
    (occurrenceMaterial, MotherHigherLawValue.pack (evolutionMaterial, cofinalMaterial))), ?_⟩
  simp only [formPresentationData, MotherHigherLawValue.split_pack, formPresentationParts, currentFormed,
    Option.bind_some, occurrenceFormed, evolutionFormed, cofinalFormed, Option.map_some]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
