import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AuthorityFamilies.Coverage

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityFamilies
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- The complete original small index and all of its roots are recovered
from a single actual material output at one adequate rank. Neither the
index address nor any child's address is a public assumption. -/
theorem every_original_family (I : Type) (N : I → WorldRelationNetwork.{0})
    (V : I → ConstructiveRoot.Vocabulary.{0}) (roots : ∀ index, SourceNativeAuthoritativeRootClosure (N index) (V index)) :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ available : (formFamily material).isSome,
        let output := (formFamily material).get available
        ∃ presentation : Presentation I N V roots output,
          presentation.restrict = roots ∧
          ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
            Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
              (MotherArenaHigher.includeOriginal rank originalAddress) := by
  let AllAddresses := I ⊕ (Σ index, MotherAuthorityRoot.AddressTotal (roots index)) ⊕ MotherNetworkFactory.B
  let rank := MotherArenaHigher.carrierRank AllAddresses
  let shared := MotherArenaHigher.carrierAddress AllAddresses
  let indexCode : I ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inl value), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let rootCode : (Σ index, MotherAuthorityRoot.AddressTotal (roots index)) ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inl value)), fun _ _ same => Sum.inl.inj (Sum.inr.inj (shared.injective same))⟩
  let originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr value)), fun _ _ same => Sum.inr.inj (Sum.inr.inj (shared.injective same))⟩
  obtain ⟨material, value, formed, ⟨presentation⟩⟩ := family_at_rank I N V roots indexCode rootCode
  have available : (formFamily material).isSome := by rw [formed]; rfl
  have outputSame : (formFamily material).get available = value :=
    Option.some.inj ((Option.some_get available).trans formed)
  refine ⟨rank, material, available, ?_⟩
  dsimp only
  rw [outputSame]
  exact ⟨presentation, presentation.restrict_eq, originalAddress,
    MotherArenaHigher.restrict_includeOriginal rank originalAddress⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityFamilies
