import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaReceipts.OriginalRoot

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaReceipts
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite MotherProjectionOrigin MotherRestructuringOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- The original admitted root supplies all four complete carrier operands
to one sufficient source rank. The actual full source factory consumes that
rank's material and restores the whole original certification and compiler. -/
theorem every_original_root (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (root : SourceNativeAuthoritativeRootClosure N V) :
    ∃ rank : Ordinal.{0}, OriginalRootFormation (rank := rank) N V root ∧
      ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
        Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
          (MotherArenaHigher.includeOriginal rank originalAddress) := by
  obtain ⟨rank, shared, originalAddress, retained⟩ := MotherArenaHigher.root_addresses_and_original_material root
  let rootCode : SourceWriteTotal root.source.restructuringSource.compiler.ledgerCompiler ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inl value), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let projectionCode : Total root.source.projectionLaw ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inl value)), fun _ _ same => Sum.inl.inj (Sum.inr.inj (shared.injective same))⟩
  let sortCode : (Σ index, sortsOf root.source.restructuringSource.compiler.restructuringLaw.vocabulary.base index) ↪
      MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr (.inl value))),
      fun _ _ same => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same)))⟩
  let familyCode : FamilyTotal (familiesOf root.source.restructuringSource.compiler.restructuringLaw.vocabulary) ↪
      MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr (.inr value))),
      fun _ _ same => Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same)))⟩
  exact ⟨rank, restructuring_at_rank N V root rootCode projectionCode sortCode familyCode,
    originalAddress, retained⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaReceipts
