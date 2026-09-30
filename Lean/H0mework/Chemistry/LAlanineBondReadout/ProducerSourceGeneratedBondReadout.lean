import H0mework.Chemistry.LAlanineBondReadout.ConsumerHistoryGraph

/-! A complete registered bond readout of the existing 2q→3q occurrence; no further MD step. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BondReadout.Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open LAlanine40K2025.Interface

theorem bondRead_commutes_with_physicalOccurrence :
    Source.physicalFrame = Runtime.bondParentFrame ∧
    Source.physicalLedger = Runtime.bondParentLedger ∧
    Source.fullState = Runtime.bondParentFullState ∧
    Source.history = Runtime.bondParentHistory ∧
    Source.physicalTime = Runtime.bondParentTime ∧ Source.physicalElapsedTime = 0 :=
  ⟨Source.physicalFrame_eq_parent, Source.physicalLedger_eq_parent, Source.fullState_eq_parent,
    Source.history_eq_parent, Source.physicalTime_eq_parent, Source.no_extra_physical_step⟩

def bondReadoutClosure : Prop :=
  type_of% Runtime.bondParent_installed ∧
  type_of% bondRead_commutes_with_physicalOccurrence ∧
  type_of% Calculation.registeredSearch_complete_account ∧
  type_of% Calculation.sameDensity_energy_and_electrons ∧
  type_of% Calculation.derivative_receipt ∧
  Nonempty Consumers.physicalConsumers.Consumer ∧
  FaceKernelExactAt Consumers.physicalConsumers Consumers.bondFaceRead ∧
  Nonempty (Consumers.physicalConsumers.Quotient ≃ Set.range Consumers.bondFaceRead) ∧
  (∀ consumer, ∃! factor : Set.range Consumers.bondFaceRead → Consumers.physicalConsumers.Output consumer,
    ∀ pair, factor ⟨Consumers.bondFaceRead pair, pair, rfl⟩ = Consumers.physicalConsumers.read consumer pair) ∧
  (∀ {Alternate : Type} (alternate : ASUHeavyPair → Alternate),
    FaceKernelExactAt Consumers.physicalConsumers alternate →
    ∃! equivalence : Set.range Consumers.bondFaceRead ≃ Set.range alternate,
      ∀ pair, equivalence ⟨Consumers.bondFaceRead pair, pair, rfl⟩ = ⟨alternate pair, pair, rfl⟩) ∧
  type_of% Calculation.everyBCP_positive_and_stable ∧
  type_of% Calculation.independentAtomTopology_eq_actual ∧
  type_of% Calculation.actualTopology_eq_retainedInitial ∧
  type_of% Calculation.nonbond_midpoint_is_not_stationary ∧
  type_of% Calculation.retainedGraph_does_not_fix_density_or_laplacian ∧
  type_of% HistoryConsumers.graphProjection_kernelStrictlyCoarser ∧
  type_of% HistoryConsumers.graphProjection_energyEscape ∧
  type_of% HistoryConsumers.registeredGraph_cannotMint_density ∧
  type_of% HistoryConsumers.registeredGraph_cannotMint_energy ∧
  type_of% Source.packetText_eq_verifiedInput

theorem sourceGeneratedBondReadout : bondReadoutClosure :=
  ⟨Runtime.bondParent_installed, bondRead_commutes_with_physicalOccurrence,
    Calculation.registeredSearch_complete_account, Calculation.sameDensity_energy_and_electrons,
    Calculation.derivative_receipt, Consumers.physicalConsumers.positive,
    Consumers.bondFace_kernelExact_at_installedPhysicalConsumers,
    ⟨Consumers.bondQuotientEquivRange⟩, Consumers.everyConsumer_uniqueFactorization,
    fun alternate exact => Consumers.completeCarrier_uniqueIso alternate exact,
    Calculation.everyBCP_positive_and_stable, Calculation.independentAtomTopology_eq_actual,
    Calculation.actualTopology_eq_retainedInitial, Calculation.nonbond_midpoint_is_not_stationary,
    Calculation.retainedGraph_does_not_fix_density_or_laplacian,
    HistoryConsumers.graphProjection_kernelStrictlyCoarser, HistoryConsumers.graphProjection_energyEscape,
    HistoryConsumers.registeredGraph_cannotMint_density, HistoryConsumers.registeredGraph_cannotMint_energy,
    Source.packetText_eq_verifiedInput⟩

end LAlanine40K2025.BondReadout.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
