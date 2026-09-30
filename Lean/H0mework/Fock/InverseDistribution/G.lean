import H0mework.Fock.InverseDistribution.ActionGenerated
import H0mework.Fock.InverseDistribution.StreamSource
import H0mework.Fock.InverseDistribution.Realization
import H0mework.Fock.InverseDistribution.InverseDistribution.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionBirth

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceCopyTimeModel
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

def decoder (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth))
    (read : Nat → Key) (key : Key) : SourceJointClockGraph.Carrier :=
    let entries := (SourceInverseDistributionAction.generate read (word.map SourceCopyNativeWord.encode) (inventoryBound runtime + 1) key).2
    SourceCompiledGWord.effect depth word (SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (recovered (inventoryBound runtime + 1) entries))) +
      SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (residual (inventoryBound runtime + 1) entries))

theorem decoder_next (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth))
    (read : Nat → Key) (key : Key) :
    decoder runtime depth word read key = SourceConditionalNativePosterior.decoder runtime.tick.next read key := by
  dsimp only [decoder]
  rw [SourceInverseDistributionAction.generated_source, SourceInverseDistributionStream.generated_source]
  have paid := SourceNativeInverseDistribution.decoder_reconstruction runtime.tick.next depth word read key
  dsimp only at paid
  rw [SourceActualImageStep.next_bound] at paid
  exact paid

theorem next_moments (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth))
    (read : Nat → Key) (key : Key) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    let entries := (SourceInverseDistributionAction.generate read (word.map SourceCopyNativeWord.encode) (inventoryBound runtime + 1) key).2
    let remainder := SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (residual (inventoryBound runtime + 1) entries))
    SourceGWordInverse.recover depth word (decoder runtime depth word read key) =
      SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (recovered (inventoryBound runtime + 1) entries)) +
      SourceCopyGraph.axes (mass remainder)
        ((program.1 : ℂ)⁻¹ * (SourceJointClockGraph.clock remainder - (program.2 : ℂ) * mass remainder)) := by
  dsimp only
  rw [decoder_next, SourceInverseDistributionAction.generated_source, SourceInverseDistributionStream.generated_source]
  have paid := SourceNativeInverseDistribution.decoder_moments runtime.tick.next depth word read key
  dsimp only at paid
  rw [SourceActualImageStep.next_bound] at paid
  exact paid

theorem next_residual (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth))
    (read : Nat → Key) (key : Key) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    let entries := (SourceInverseDistributionAction.generate read (word.map SourceCopyNativeWord.encode) (inventoryBound runtime + 1) key).2
    let remainder := SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (residual (inventoryBound runtime + 1) entries))
    SourceGWordInverse.residual depth word (decoder runtime depth word read key) +
      SourceCompiledGWord.effect depth word (SourceCopyGraph.axes (mass remainder)
        ((program.1 : ℂ)⁻¹ * (SourceJointClockGraph.clock remainder - (program.2 : ℂ) * mass remainder))) = remainder := by
  dsimp only
  rw [decoder_next, SourceInverseDistributionAction.generated_source, SourceInverseDistributionStream.generated_source]
  have paid := SourceNativeInverseDistribution.decoder_residual runtime.tick.next depth word read key
  dsimp only at paid
  rw [SourceActualImageStep.next_bound] at paid
  exact paid

end
end SourceInverseDistributionBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
