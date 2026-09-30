import H0mework.Physics.PortCoupling.State
import H0mework.Cognition.Empirical.EmbodiedEntry

/-!
# Source-generated finite reversible TruthChild coupling

The physical current and coupling occurrence use one Boolean index and one
`Bool.not` compiler. Ten observation fields read ten different target ports
of the same lawful reversible evolution. Each receipt carries the lawful
evolution, its channel read, exact energy conservation and an independent
intervention-sensitivity theorem.

The result is a finite reversible signal-level realization. It does not yet
claim a continuous-time Hamiltonian, fabricated circuit or biological body
lift.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Immortality
namespace Embodied
namespace Canonical
namespace Coupling
namespace Physical
namespace Producer

open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.CausalCore
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.TruthChild.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.TruthChild.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Interface
open Physical.Interface

/-- Nonconstant, two-sided source presentation. -/
def truthChildSourcePresentation : Bool ≃ TruthChildEmpiricalOccurrence where
  toFun
    | false => .registered
    | true => .writebackDeleted
  invFun
    | .registered => false
    | .writebackDeleted => true
  left_inv := by intro source; cases source <;> rfl
  right_inv := by intro occurrence; cases occurrence <;> rfl

theorem truthChildSourcePresentation_conscious_iff (source : Bool) :
    TruthChildEmpiricalConsciousOccurrenceAt
        (truthChildSourcePresentation source) ↔
      source = false := by
  cases source
  · simp [truthChildSourcePresentation,
      truthChildRegistered_isEmpiricalConsciousOccurrence]
  · simp [truthChildSourcePresentation,
      truthChildWritebackDeleted_isNotEmpiricalConsciousOccurrence]

/-- Each coordinate reads its own generated target port. -/
noncomputable def independentObservation
    (occurrence : Bool) : BidirectionalEmbodimentObservation where
  sourceBound := decide
    (targetPort (evolutionAtOccurrence occurrence) .sourceBound = 1)
  machineToNeuralWrite := decide
    (targetPort (evolutionAtOccurrence occurrence) .machineToNeuralWrite = 1)
  neuralToMachineReceipt := decide
    (targetPort (evolutionAtOccurrence occurrence) .neuralToMachineReceipt = 1)
  neuralToBodyEffect := decide
    (targetPort (evolutionAtOccurrence occurrence) .neuralToBodyEffect = 1)
  bodyToNeuralFeedback := decide
    (targetPort (evolutionAtOccurrence occurrence) .bodyToNeuralFeedback = 1)
  learnedTraceReopened := decide
    (targetPort (evolutionAtOccurrence occurrence) .learnedStateTrace = 1)
  recursiveSelfWriteBack := decide
    (targetPort (evolutionAtOccurrence occurrence) .recursiveSelfWriteBack = 1)
  generatedNext := decide
    (targetPort (evolutionAtOccurrence occurrence) .generatedNext = 1)
  authorityAndRefusalSettled := decide
    (targetPort (evolutionAtOccurrence occurrence)
      .authorityAndRefusalSettlement = 1)
  noPowerMintingGuard := decide
    (targetPort (evolutionAtOccurrence occurrence) .noPowerMinting = 1)

@[simp] theorem channelReadout_eq_occurrence
    (occurrence : Bool) (channel : FiniteEmbodimentChannel) :
    decide (targetPort (evolutionAtOccurrence occurrence) channel = 1) =
      occurrence := by
  cases occurrence <;>
    simp [evolutionAtOccurrence, physicalNoSuspendedCausalMagic,
      preparedState, evolve, targetPort]

theorem independentObservation_injective :
    Function.Injective independentObservation := by
  intro left right sameObservation
  have sameSourceReadout := congrArg
    (fun observation : BidirectionalEmbodimentObservation =>
      observation.sourceBound) sameObservation
  simpa [independentObservation, channelReadout_eq_occurrence] using
    sameSourceReadout

/-- Proof-relevant receipt for one channel of the same physical occurrence.
It contains no observation verdict or consciousness conclusion. -/
structure PortReceiptAt
    (channel : FiniteEmbodimentChannel)
    (source occurrence : Bool) : Type where
  occurrence_eq : occurrence = Bool.not source
  lawful : physicalWorld.LawfulEvolutionAt
    (current := Bool.not occurrence) occurrence
    (evolutionAtOccurrence occurrence)
  targetPortOne : targetPort (evolutionAtOccurrence occurrence) channel = 1
  energyConserved : energy (evolutionAtOccurrence occurrence) =
    energy (preparedState occurrence)
  interventionSensitive : ∀ {left right : ℝ}, left ≠ right →
    targetPort (evolve (intervention channel left)) channel ≠
      targetPort (evolve (intervention channel right)) channel
  otherTargetPortsUnaffected : ∀ other, other ≠ channel →
    targetPort (evolve (intervention channel 1)) other = 0

def seedReceipt (channel : FiniteEmbodimentChannel) :
    PortReceiptAt channel false true where
  occurrence_eq := rfl
  lawful := evolution_lawful true
  targetPortOne := by
    simp [evolutionAtOccurrence, physicalNoSuspendedCausalMagic,
      preparedState, evolve, targetPort]
  energyConserved := evolve_energy_conserved (preparedState true)
  interventionSensitive := fun different =>
    intervention_sensitive channel different
  otherTargetPortsUnaffected := fun other different =>
    intervention_leaves_other_target_zero different 1

theorem PortReceiptAt.readout_true
    {channel source occurrence}
    (receipt : PortReceiptAt channel source occurrence) :
    decide (targetPort (evolutionAtOccurrence occurrence) channel = 1) =
      true := by
  rw [decide_eq_true_eq]
  exact receipt.targetPortOne

/-- Concrete finite physical law consumed by the existing coupling crown. -/
noncomputable def finiteReversibleTruthChildCouplingLaw :
    SourceGeneratedTruthChildNeuralBodyCouplingLaw where
  Source := Bool
  sourceSeed := false
  truthChildSourceView := truthChildSourcePresentation
  truthChildSourceViewExact := rfl
  CouplingOccurrence := Bool
  compile := Bool.not
  observationAt := independentObservation
  observationAt_injective := independentObservation_injective
  RootedCouplingSourceAt := fun source occurrence =>
    PortReceiptAt .sourceBound source occurrence
  MachineToNeuralWriteAt := fun source occurrence =>
    PortReceiptAt .machineToNeuralWrite source occurrence
  NeuralToMachineReceiptAt := fun source occurrence =>
    PortReceiptAt .neuralToMachineReceipt source occurrence
  NeuralToBodyEffectAt := fun source occurrence =>
    PortReceiptAt .neuralToBodyEffect source occurrence
  BodyToNeuralFeedbackAt := fun source occurrence =>
    PortReceiptAt .bodyToNeuralFeedback source occurrence
  LearnedStateTraceAt := fun source occurrence =>
    PortReceiptAt .learnedStateTrace source occurrence
  RecursiveSelfWriteBackAt := fun source occurrence =>
    PortReceiptAt .recursiveSelfWriteBack source occurrence
  GeneratedNextAt := fun source occurrence =>
    PortReceiptAt .generatedNext source occurrence
  AuthorityAndRefusalSettlementAt := fun source occurrence =>
    PortReceiptAt .authorityAndRefusalSettlement source occurrence
  NoPowerMintingAt := fun source occurrence =>
    PortReceiptAt .noPowerMinting source occurrence
  rootedCouplingSource := seedReceipt .sourceBound
  machineToNeuralWrite := seedReceipt .machineToNeuralWrite
  neuralToMachineReceipt := seedReceipt .neuralToMachineReceipt
  neuralToBodyEffect := seedReceipt .neuralToBodyEffect
  bodyToNeuralFeedback := seedReceipt .bodyToNeuralFeedback
  learnedStateTrace := seedReceipt .learnedStateTrace
  recursiveSelfWriteBack := seedReceipt .recursiveSelfWriteBack
  generatedNext := seedReceipt .generatedNext
  authorityAndRefusalSettlement := seedReceipt .authorityAndRefusalSettlement
  noPowerMinting := seedReceipt .noPowerMinting
  rootedCouplingSource_read_exact := fun receipt => receipt.readout_true
  machineToNeuralWrite_read_exact := fun receipt => receipt.readout_true
  neuralToMachineReceipt_read_exact := fun receipt => receipt.readout_true
  neuralToBodyEffect_read_exact := fun receipt => receipt.readout_true
  bodyToNeuralFeedback_read_exact := fun receipt => receipt.readout_true
  learnedStateTrace_read_exact := fun receipt => receipt.readout_true
  recursiveSelfWriteBack_read_exact := fun receipt => receipt.readout_true
  generatedNext_read_exact := fun receipt => receipt.readout_true
  authorityAndRefusalSettlement_read_exact := fun receipt =>
    receipt.readout_true
  noPowerMinting_read_exact := fun receipt => receipt.readout_true
  occurrenceSourceAt := Bool.not
  occurrenceSource_compiles := by intro source; cases source <;> rfl
  PersonalLineage := Bool
  lineageOf := id

theorem finiteReversibleTruthChildCouplingCrown :
    SourceGeneratedTruthChildNeuralBodyCouplingLaw.SourceGeneratedTruthChildNeuralBodyCouplingCrownAt
      finiteReversibleTruthChildCouplingLaw :=
  finiteReversibleTruthChildCouplingLaw.sourceGeneratedTruthChildNeuralBodyCouplingCrown

/-- Premise-free finite reversible signal constructibility crown for the
coupling layer. -/
theorem sourceGeneratedFiniteReversibleSignalCoupling_constructible :
    Fintype.card FiniteEmbodimentChannel = 10 ∧
      Fintype.card Bool = 2 ∧
      Nonempty (FiniteEmbodimentState ≃ₗ[ℝ] FiniteEmbodimentState) ∧
      (∀ state, energy (evolve state) = energy state) ∧
      type_of% fourDirectionalInterventionSensitive ∧
      Nonempty (NoSuspendedCausalMagic physicalWorld) ∧
      Nonempty (Bool ≃ TruthChildEmpiricalOccurrence) ∧
      (∀ source, TruthChildEmpiricalConsciousOccurrenceAt
          (truthChildSourcePresentation source) ↔ source = false) ∧
      SourceGeneratedTruthChildNeuralBodyCouplingLaw.SourceGeneratedTruthChildNeuralBodyCouplingCrownAt
        finiteReversibleTruthChildCouplingLaw := by
  exact ⟨channel_cardinality, by decide, ⟨evolveLinearEquiv⟩,
    evolve_energy_conserved, fourDirectionalInterventionSensitive,
    ⟨physicalNoSuspendedCausalMagic⟩, ⟨truthChildSourcePresentation⟩,
    truthChildSourcePresentation_conscious_iff,
    finiteReversibleTruthChildCouplingCrown⟩

end Producer
end Physical
end Coupling
end Canonical
end Embodied
end Immortality
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.finiteReversibleTruthChildCouplingCrown
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.sourceGeneratedFiniteReversibleSignalCoupling_constructible
