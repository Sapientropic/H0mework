import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffRoots.Coverage
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffRestriction.Declaration

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffRoots
open MotherHandoffRestriction
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- An original sealed handoff contributes its full declaration only to
coverage. One material jointly forms every event, its selected emitter and
the whole vocabulary/root successor for every event. -/
theorem every_handoff_roots {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeAuthoritySource N V} (law : SourceNativeTerminalHandoffLaw source) :
    ∃ events : EventFamily source, ∃ declaration : Declaration source events,
      assembleLaw declaration = law ∧
      ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
        ∃ available : (formRoots material).isSome,
          let output := (formRoots material).get available
          ∃ presentation : Presentation (Index source) events declaration.emit N
            (fun point => (declaration.continuation point).next.1)
            (fun point => (declaration.continuation point).next.2) output,
            presentation.restrictRoots = (fun point => (declaration.continuation point).next) ∧
            ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
              Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
                (MotherArenaHigher.includeOriginal rank originalAddress) := by
  obtain ⟨events, declaration, declarationSame⟩ := exists_declaration law
  let next := fun point => (declaration.continuation point).next
  let AllAddresses := Index source ⊕ (Sigma events) ⊕
    (Σ point, MotherAuthorityRoot.AddressTotal (next point).2) ⊕ MotherNetworkFactory.B
  let rank := MotherArenaHigher.carrierRank AllAddresses
  let shared := MotherArenaHigher.carrierAddress AllAddresses
  let indexCode : Index source ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inl value), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let eventCode : Sigma events ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inl value)), fun _ _ same => Sum.inl.inj (Sum.inr.inj (shared.injective same))⟩
  let rootCode : (Σ point, MotherAuthorityRoot.AddressTotal (next point).2) ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr (.inl value))),
      fun _ _ same => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same)))⟩
  let originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr (.inr value))),
      fun _ _ same => Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same)))⟩
  obtain ⟨material, value, formed, ⟨presentation⟩⟩ := roots_at_rank (Index source) events declaration.emit N
    (fun point => (next point).1) (fun point => (next point).2) indexCode eventCode rootCode
  have available : (formRoots material).isSome := by rw [formed]; rfl
  have outputSame : (formRoots material).get available = value :=
    Option.some.inj ((Option.some_get available).trans formed)
  refine ⟨events, declaration, declarationSame, rank, material, available, ?_⟩
  dsimp only
  rw [outputSame]
  exact ⟨presentation, presentation.restrictRoots_eq, originalAddress,
    MotherArenaHigher.restrict_includeOriginal rank originalAddress⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffRoots
