import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffPayload.Assembly

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffPayload
open MotherHandoffRestriction
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeAuthoritySource N V} {events : EventFamily source}

/-- At one already paid rank, a single actual material supplies the full CP
and all debt values at every event and every target row. Recovery reads the
actual Option output before assembling the whole original declaration. -/
theorem every_original_payload (declaration : Declaration source events)
    (coordinates : Coordinates (rank := rank) (fun point => (declaration.continuation point).next)) :
    ∃ material : MotherArenaHigher.Material rank,
      ∃ available : (formValues (fun point => (declaration.continuation point).next) coordinates material).isSome,
        let actual := (formValues (fun point => (declaration.continuation point).next) coordinates material).get available
        ∃ same : actual = valuesOf declaration,
          assemble (fun point => (declaration.continuation point).next) declaration.emit actual
            (recovered_laws declaration actual same) = declaration := by
  obtain ⟨material, formed⟩ := every_values (fun point => (declaration.continuation point).next)
    coordinates (valuesOf declaration)
  have available : (formValues (fun point => (declaration.continuation point).next) coordinates material).isSome := by
    rw [formed]
    rfl
  have same : (formValues (fun point => (declaration.continuation point).next) coordinates material).get available =
      valuesOf declaration := Option.some.inj ((Option.some_get available).trans formed)
  exact ⟨material, available, same, actual_assembly_recovers declaration declaration.emit rfl _ same⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffPayload
