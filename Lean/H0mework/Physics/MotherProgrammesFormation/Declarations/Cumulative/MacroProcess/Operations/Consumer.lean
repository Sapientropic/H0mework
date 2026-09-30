import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.MacroProcess.Operations.Coverage
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.MacroProcess.Operations.Recovery

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroOperations
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section

/-- The actual native process Option output is the restriction's source.
Node formation remains the upstream typed operand; this theorem does not
turn a nodesFormed assumption into a universal source law. -/
theorem every_original_on_nodes_consumed {rank : Ordinal.{0}}
    (domain : MotherArenaHigher.Material rank) (nodes : Nodes domain)
    (event : Event nodes ↪ MotherArenaHigher.Base rank)
    (original : SourceNativeInquiryEngineProcess.{0}) (state : State domain ≃ original.State)
    (nodeSame : ∀ current, nodes current = original.stateAt (state current)) :
    ∃ material : MotherArenaHigher.Material rank,
      ∃ available : (formProcess domain nodes event material).isSome,
      ∃ presentation : MotherRegistryRecovery.Presentation
          ((formProcess domain nodes event material).get available) original,
        restrict presentation = original ∧
        HEq (restrict presentation).successorAt original.successorAt := by
  obtain ⟨material, formed⟩ := every_original_on_nodes domain nodes event original state nodeSame
  have available : (formProcess domain nodes event material).isSome := by rw [formed]; rfl
  have generatedSame : (formProcess domain nodes event material).get available = MotherRegistryRecovery.rechart original state :=
    Option.some.inj ((Option.some_get available).trans formed)
  let presentation : MotherRegistryRecovery.Presentation
      ((formProcess domain nodes event material).get available) original :=
    generatedSame.symm ▸ MotherRegistryRecovery.rechartPresentation original state
  exact ⟨material, available, presentation, restrict_eq presentation, successorAt_recovers presentation⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroOperations
