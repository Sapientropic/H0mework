import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.CurrentFamilies.Material

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCurrentFamilies
open MotherHandoffRestriction MotherHandoffSource MotherNativeCurrent
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section

/-- Arbitrary complete small registries enter at once. The source graph
forms the whole index type, and every original complete current receives its
own full material components at one shared sufficient rank. -/
theorem every_current_family (I : Type) (N : I → WorldRelationNetwork.{0})
    (currents : (index : I) → SourceNativeLivingRootCurrentAt (N index)) :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ indices : I ≃ Member material,
        (∀ index, CurrentFormationAt rank (currents index) (atMember material (indices index))) ∧
        ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
          Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
            (MotherArenaHigher.includeOriginal rank originalAddress) := by
  have schemas : ∀ index : I, ∃ events : EventFamily (currents index).root.source.base,
      ∃ declaration : Declaration (currents index).root.source.base events,
        assembleLaw declaration = (currents index).root.source.terminalHandoff := fun index =>
    exists_declaration (currents index).root.source.terminalHandoff
  choose events declarations lawSame using schemas
  let AllAddresses := I ⊕
    (Σ index, JointAddress (currents index).root.toAuthoritativeRoot (events index) (declarations index)) ⊕
    MotherNetworkFactory.B
  let rank := MotherArenaHigher.carrierRank AllAddresses
  let shared := MotherArenaHigher.carrierAddress AllAddresses
  let indexCode : I ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inl value), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let rootCode : (Σ index, JointAddress (currents index).root.toAuthoritativeRoot (events index) (declarations index)) ↪
      MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inl value)), fun _ _ same => Sum.inl.inj (Sum.inr.inj (shared.injective same))⟩
  let originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr value)), fun _ _ same => Sum.inr.inj (Sum.inr.inj (shared.injective same))⟩
  have allCurrents : ∀ index : I, ∃ materials, CurrentFormationAt rank (currents index) materials := fun index =>
    current_at_rank (currents index) (events index) (declarations index) (lawSame index)
      ((Function.Embedding.sigmaMk index).trans rootCode)
  choose values formed using allCurrents
  obtain ⟨base, ⟨indexMap⟩⟩ := MotherAuthorityFamilies.every_index I indexCode
  obtain ⟨material, indices, recovered⟩ := every_material_family I base indexMap values
  refine ⟨rank, material, indices, fun index => ?_, originalAddress,
    MotherArenaHigher.restrict_includeOriginal rank originalAddress⟩
  rw [recovered]
  exact formed index

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCurrentFamilies
