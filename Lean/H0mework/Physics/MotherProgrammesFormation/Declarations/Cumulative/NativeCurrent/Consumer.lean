import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.NativeCurrent.Visit
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffSource.Header

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeCurrent
open MotherHandoffRestriction MotherHandoffSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- A single material restores the complete original heterogeneous living
current, including the vocabulary value, entire living source and exact
chronological visit. It is ready for the original dependent inquiry indices. -/
theorem every_original_current (N : WorldRelationNetwork.{0}) (old : SourceNativeLivingRootCurrentAt N) :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      let sourceMaterial := (MotherArenaHigher.split rank material).1
      let jointMaterial := (MotherArenaHigher.split rank sourceMaterial).1
      let payloadMaterial := (MotherArenaHigher.split rank sourceMaterial).2
      ∃ available : (formJoint jointMaterial).isSome,
        let value := (formJoint jointMaterial).get available
        ∃ events : EventFamily old.root.source.base,
          ∃ declaration : Declaration old.root.source.base events,
          ∃ presentation : JointPresentation old.root.toAuthoritativeRoot events declaration value,
            ∃ payloadAvailable : (formPayload old.root declaration jointMaterial value
              (Option.some_get available).symm presentation payloadMaterial).isSome,
              let payload := (formPayload old.root declaration jointMaterial value
                (Option.some_get available).symm presentation payloadMaterial).get payloadAvailable
              ∃ same : payload = MotherHandoffPayload.valuesOf declaration,
                formCurrent (restrictHeader old.root declaration value presentation payload same)
                  (MotherArenaHigher.split rank material).2 = some old ∧
                ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
                  Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
                    (MotherArenaHigher.includeOriginal rank originalAddress) := by
  obtain ⟨rank, sourceMaterial, available, events, declaration, presentation, payloadAvailable, same, rootSame, original⟩ :=
    every_original_living_root N old.V old.root
  let value := (formJoint (MotherArenaHigher.split rank sourceMaterial).1).get available
  let payload := (formPayload old.root declaration (MotherArenaHigher.split rank sourceMaterial).1 value
    (Option.some_get available).symm presentation (MotherArenaHigher.split rank sourceMaterial).2).get payloadAvailable
  have headerSame := restrictHeader_of_root_eq old.root declaration value presentation payload same rootSame
  obtain ⟨visitMaterial, currentFormed⟩ := current_on_header (rank := rank) old
    (restrictHeader old.root declaration value presentation payload same) headerSame
  refine ⟨rank, MotherArenaHigher.pack rank (sourceMaterial, visitMaterial), ?_⟩
  rw [MotherArenaHigher.split_pack]
  exact ⟨available, events, declaration, presentation, payloadAvailable, same, currentFormed, original⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeCurrent
