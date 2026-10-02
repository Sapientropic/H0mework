import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffSource.Living

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffSource
open MotherHandoffRestriction
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- One sufficient rank and one mother material recover the entire original
living root. Its parent source, all legal handoff events, full successors,
both presentation programs and the complete old/target debt classifier are
actual material readouts. The original root enters coverage, not the factory. -/
theorem every_original_living_root (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (old : SourceNativeLivingRootClosure N V) :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ available : (formJoint (MotherArenaHigher.split rank material).1).isSome,
        let value := (formJoint (MotherArenaHigher.split rank material).1).get available
        ∃ events : EventFamily old.source.base, ∃ declaration : Declaration old.source.base events,
          ∃ presentation : JointPresentation old.toAuthoritativeRoot events declaration value,
            ∃ payloadAvailable : (formPayload old declaration (MotherArenaHigher.split rank material).1 value
              (Option.some_get available).symm presentation (MotherArenaHigher.split rank material).2).isSome,
              let payload := (formPayload old declaration (MotherArenaHigher.split rank material).1 value
                (Option.some_get available).symm presentation (MotherArenaHigher.split rank material).2).get payloadAvailable
              ∃ same : payload = MotherHandoffPayload.valuesOf declaration,
                restrictLiving old declaration value presentation payload same = old ∧
                ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
                  Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
                    (MotherArenaHigher.includeOriginal rank originalAddress) := by
  obtain ⟨events, declaration, lawSame⟩ := exists_declaration old.source.terminalHandoff
  let AllAddresses := JointAddress old.toAuthoritativeRoot events declaration ⊕ MotherNetworkFactory.B
  let rank := MotherArenaHigher.carrierRank AllAddresses
  let shared := MotherArenaHigher.carrierAddress AllAddresses
  let address : JointAddress old.toAuthoritativeRoot events declaration ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inl value), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr value), fun _ _ same => Sum.inr.inj (shared.injective same)⟩
  obtain ⟨jointMaterial, value, formed, ⟨presentation⟩⟩ :=
    joint_at_rank old.toAuthoritativeRoot events declaration address
  obtain ⟨payloadMaterial, payloadFormed⟩ := MotherHandoffPayload.every_values
    (fun point => (declaration.continuation point).next)
    (payloadCoordinates old declaration jointMaterial value formed presentation)
    (MotherHandoffPayload.valuesOf declaration)
  have available : (formJoint jointMaterial).isSome := by rw [formed]; rfl
  have outputSame : (formJoint jointMaterial).get available = value :=
    Option.some.inj ((Option.some_get available).trans formed)
  cases outputSame
  let value := (formJoint jointMaterial).get available
  refine ⟨rank, MotherArenaHigher.pack rank (jointMaterial, payloadMaterial), ?_⟩
  rw [MotherArenaHigher.split_pack]
  dsimp only
  refine ⟨available, ?_⟩
  refine ⟨events, declaration, presentation, ?_⟩
  have payloadAvailable : (formPayload old declaration jointMaterial value formed presentation payloadMaterial).isSome := by
    change (MotherHandoffPayload.formValues _ _ payloadMaterial).isSome
    rw [payloadFormed]
    rfl
  have same : (formPayload old declaration jointMaterial value formed presentation payloadMaterial).get payloadAvailable =
      MotherHandoffPayload.valuesOf declaration :=
    Option.some.inj ((Option.some_get payloadAvailable).trans payloadFormed)
  exact ⟨payloadAvailable, same, restrictLiving_eq old declaration value presentation _ same lawSame,
    originalAddress, MotherArenaHigher.restrict_includeOriginal rank originalAddress⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffSource
