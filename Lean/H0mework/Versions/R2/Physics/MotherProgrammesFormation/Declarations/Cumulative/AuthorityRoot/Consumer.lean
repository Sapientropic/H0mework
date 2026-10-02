import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.AuthorityRoot.Formation

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityRoot
open MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- The complete original authoritative root, source and all-current emitter, is read from the actual Option/Sigma
factory output. Availability and every dependent correspondence are generated
by coverage, without a caller-owned header or representation premise. -/
theorem every_original_root_recovered (N : WorldRelationNetwork.{0})
    (V : ConstructiveRoot.Vocabulary.{0}) (root : SourceNativeAuthoritativeRootClosure N V) :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ available : (MotherArenaTheory.formTheory material).isSome,
        let output := (MotherArenaTheory.formTheory material).get available
        ∃ presentation : Presentation root output.1.1 output.1.2 output.2,
          presentation.restrict = root ∧
          ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
            Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
              (MotherArenaHigher.includeOriginal rank originalAddress) := by
  obtain ⟨rank, material, value, data, surface, presentation, formed, recovered, original⟩ :=
    every_original_root N V root
  have available : (MotherArenaTheory.formTheory material).isSome := by
    rw [formed]
    rfl
  have outputSame : (MotherArenaTheory.formTheory material).get available = ⟨⟨value, data⟩, surface⟩ :=
    Option.some.inj ((Option.some_get available).trans formed)
  refine ⟨rank, material, available, ?_⟩
  dsimp only
  rw [outputSame]
  exact ⟨presentation, recovered, original⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityRoot
