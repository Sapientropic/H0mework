import H0mework.Computation.ADCWire.DigitalReadback
import H0mework.Foundation.Relations.ConsumerFace

/-!
# Exact representation of all addressed ADC executions

The consumer system reads independently declared source requests. The carrier
is the clock tick and actual ADC word frames emitted by their physical runs.
Exact readback first proves both directions of kernel equality. The existing
quotient/range and factorization calculus then supplies the representation
crown over this same fixed hardware source.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Physical.Interface
open NoIslandNoMagic.Consciousness.Representation

noncomputable section

/-- Kernel exactness is derived from the physical decoder, not supplied with the source. -/
theorem addressedADCDigitalKernel
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    FaceKernelExactAt binaryDriveConsumers (compiledADCDigitalSample source) := by
  intro left right
  rw [binaryDriveConsumers_indistinguishable_iff_eq]
  exact (compiledADCDigitalSample_injective source).eq_iff

/-- The original consumer quotient is realized by the generated digital image. -/
def addressedADCQuotientEquivRange
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    binaryDriveConsumers.Quotient ≃ Set.range (compiledADCDigitalSample source) :=
  (addressedADCDigitalKernel source).quotientEquivRange

theorem addressedADC_everyConsumer_factors
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (consumer : binaryDriveConsumers.Consumer) :
    ∃! factor : Set.range (compiledADCDigitalSample source) →
        binaryDriveConsumers.Output consumer,
      ∀ drive, factor ⟨compiledADCDigitalSample source drive, drive, rfl⟩ =
        binaryDriveConsumers.read consumer drive :=
  (addressedADCDigitalKernel source).everyConsumer_unique_factorization consumer

/-- Any alternative complete carrier must commute with the very same source command occurrence. -/
theorem addressedADC_sameRoot_uniqueIso
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {Alternate : Type} (alternate : FiniteBinaryDrive → Alternate)
    (exactKernel : FaceKernelExactAt binaryDriveConsumers alternate) :
    ∃! equivalence : Set.range (compiledADCDigitalSample source) ≃ Set.range alternate,
      ∀ drive, equivalence ⟨compiledADCDigitalSample source drive, drive, rfl⟩ =
        ⟨alternate drive, drive, rfl⟩ :=
  ⟨(addressedADCDigitalKernel source).completeCarrierEquiv exactKernel,
    (addressedADCDigitalKernel source).completeCarrierEquiv_commutes exactKernel,
    fun candidate commutes =>
      (addressedADCDigitalKernel source).completeCarrierEquiv_unique
        exactKernel candidate commutes⟩

theorem addressedADC_everyFixedReadout_factors
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {Output : Type} (read : FiniteBinaryDrive → Output) :
    ∃! factor : Set.range (compiledADCDigitalSample source) → Output,
      ∀ drive, factor ⟨compiledADCDigitalSample source drive, drive, rfl⟩ = read drive :=
  FaceKernelExactAt.everyCurrentReadout_uniqueFactorization
    (compiledADCDigitalSample_injective source) read

/-- The source-generated digital image has 1024 elements, despite the ambient tick type being Nat. -/
theorem addressedADC_image_card
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    Nat.card (Set.range (compiledADCDigitalSample source)) = 1024 := by
  rw [← Nat.card_congr
    (Equiv.ofInjective _ (compiledADCDigitalSample_injective source))]
  rw [Nat.card_eq_fintype_card, finiteBinaryDrive_card]

/-- Any complete finite representation pays the full independent-address capacity. -/
theorem addressedADC_completeCarrier_capacity
    {Carrier : Type} [Fintype Carrier]
    (representation : FiniteBinaryDrive → Carrier)
    (exactKernel : FaceKernelExactAt binaryDriveConsumers representation) :
    1024 ≤ Fintype.card Carrier := by
  have injective : Function.Injective representation := by
    intro left right same
    exact (binaryDriveConsumers_indistinguishable_iff_eq left right).mp
      ((exactKernel left right).mp same)
  simpa only [finiteBinaryDrive_card] using Fintype.card_le_of_injective representation injective

theorem addressedADC_completeBitWord_minimum
    (bits : Nat) (representation : FiniteBinaryDrive → Fin (2 ^ bits))
    (exactKernel : FaceKernelExactAt binaryDriveConsumers representation) :
    10 ≤ bits := by
  have capacity := addressedADC_completeCarrier_capacity representation exactKernel
  simp only [Fintype.card_fin] at capacity
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (show 2 ^ 10 ≤ 2 ^ bits from capacity)

/-- Full addressed execution and representation certificate, generated from source parameters alone. -/
structure SourceGeneratedAddressedADCCrownAt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) : Prop where
  everyExecution : ∀ drive,
    SourceGeneratedFiniteADCClockedNoisyMeteredSynchronousSampleAt source drive
  exactDigitalReadback : ∀ drive,
    decodeDigitalSample source (compiledADCDigitalSample source drive) = drive
  kernelExact : FaceKernelExactAt binaryDriveConsumers (compiledADCDigitalSample source)
  quotientRange : Nonempty
    (binaryDriveConsumers.Quotient ≃ Set.range (compiledADCDigitalSample source))
  everyConsumerFactors : ∀ consumer,
    ∃! factor : Set.range (compiledADCDigitalSample source) →
        binaryDriveConsumers.Output consumer,
      ∀ drive, factor ⟨compiledADCDigitalSample source drive, drive, rfl⟩ =
        binaryDriveConsumers.read consumer drive
  imageCapacity : Nat.card (Set.range (compiledADCDigitalSample source)) = 1024
  channelIsolation : ∀ selected,
    decodeDigitalSample source
        (compiledADCDigitalSample source (singleBinaryDrive selected)) selected = true ∧
      ∀ other, other ≠ selected →
        decodeDigitalSample source
          (compiledADCDigitalSample source (singleBinaryDrive selected)) other = false

theorem sourceGeneratedAddressedADCCrown
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    SourceGeneratedAddressedADCCrownAt source where
  everyExecution := sourceGeneratedFiniteADCClockedNoisyMeteredSynchronousSample source
  exactDigitalReadback := decodeDigitalSample_compiled source
  kernelExact := addressedADCDigitalKernel source
  quotientRange := ⟨addressedADCQuotientEquivRange source⟩
  everyConsumerFactors := addressedADC_everyConsumer_factors source
  imageCapacity := addressedADC_image_card source
  channelIsolation := singleBinaryDrive_received_exactly source

end

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
