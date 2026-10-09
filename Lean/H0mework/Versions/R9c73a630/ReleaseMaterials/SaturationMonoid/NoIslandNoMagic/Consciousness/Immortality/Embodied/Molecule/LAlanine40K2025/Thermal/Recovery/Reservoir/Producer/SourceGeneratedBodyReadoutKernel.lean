import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Source.SourceGeneratedBodyChannel
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Source.IndependentBodyConsumers

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.BodyKernel

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open Load.Source
noncomputable section

theorem source_body_kernel_exact : FaceKernelExactAt bodyConsumers sourceBodyChannel := by
  intro left right
  rw [bodyConsumers_exact]
  exact ⟨fun same => sourceBodyChannel_injective same, fun same => congrArg sourceBodyChannel same⟩

def sourceBodyQuotientEquivRange : bodyConsumers.Quotient ≃ Set.range sourceBodyChannel :=
  source_body_kernel_exact.quotientEquivRange

theorem source_body_consumer_factorization (consumer : bodyConsumers.Consumer) :
    ∃! factor : Set.range sourceBodyChannel → bodyConsumers.Output consumer,
      ∀ rho, factor ⟨sourceBodyChannel rho, rho, rfl⟩ = bodyConsumers.read consumer rho :=
  source_body_kernel_exact.everyConsumer_unique_factorization consumer

theorem source_body_any_readout_factorization {Output : Type} (read : LoadedJoint → Output) :
    ∃! factor : Set.range sourceBodyChannel → Output,
      ∀ rho, factor ⟨sourceBodyChannel rho, rho, rfl⟩ = read rho :=
  FaceKernelExactAt.everyCurrentReadout_uniqueFactorization sourceBodyChannel_injective read

theorem source_body_readout_actual (consumer : bodyConsumers.Consumer) :
    source_body_kernel_exact.factor consumer
      ⟨Incidence.bodyRead (Current.supplyNext Current.initial).joint, Source.received.joint, sourceBodyChannel_actual⟩ =
        bodyConsumers.read consumer Source.received.joint := by
  have same : (⟨Incidence.bodyRead (Current.supplyNext Current.initial).joint,
      Source.received.joint, sourceBodyChannel_actual⟩ : Set.range sourceBodyChannel) =
      ⟨sourceBodyChannel Source.received.joint, Source.received.joint, rfl⟩ :=
    Subtype.ext sourceBodyChannel_actual.symm
  rw [same]
  exact source_body_kernel_exact.factor_commutes consumer _

theorem sourceGeneratedBodyReadoutKernel :
    type_of% source_body_kernel_exact ∧ type_of% sourceBodyChannel_actual ∧
    (∀ consumer, type_of% (source_body_consumer_factorization consumer)) ∧
    ∀ consumer, type_of% (source_body_readout_actual consumer) :=
  ⟨source_body_kernel_exact, sourceBodyChannel_actual, source_body_consumer_factorization, source_body_readout_actual⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.BodyKernel
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
