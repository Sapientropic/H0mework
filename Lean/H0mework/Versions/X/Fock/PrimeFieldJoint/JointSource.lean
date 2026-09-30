import H0mework.Versions.X.Fock.PrimeFieldJoint.JointField
import H0mework.Versions.X.Fock.SourceHistory.MassCompletion

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedAcquisitionJoint

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceGeneratedAcquisitionMeasure
open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation SourcePrimeHistoryRecovery
open SourceSuccessorBoundary
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def depth (runtime : LivingRuntimeState process) : Nat :=
  completionDepth sourceOwner (inventoryBound runtime) + 2

def sourceDensity (runtime : LivingRuntimeState process) : FieldSpace (depth runtime) (inventoryBound runtime) :=
  density (depth runtime) (inventoryBound runtime)

def packet (runtime : LivingRuntimeState process) : SourceMassCompletion.Joint :=
  joint (depth runtime) (inventoryBound runtime) (sourceDensity runtime)

def addedDensity (runtime : LivingRuntimeState process) :
    FieldSpace (depth (next runtime)) (inventoryBound (next runtime)) :=
  Actor.currentTransfer (depth (next runtime)) (inventoryBound (next runtime))
    (SourceHistoryGrowth.remainder (retained runtime) (SourceHistoryWord.density (inventoryBound (next runtime))))

def addedPacket (runtime : LivingRuntimeState process) : SourceMassCompletion.Joint :=
  joint (depth (next runtime)) (inventoryBound (next runtime)) (addedDensity runtime)

theorem packet_original (runtime : LivingRuntimeState process) :
    packet runtime = SourceMassCompletion.jointRead (meanWord (inventoryBound runtime)) :=
  density_joint _ _

theorem added_word (runtime : LivingRuntimeState process) :
    word (depth (next runtime)) (inventoryBound (next runtime)) (addedDensity runtime) =
      SourceHistoryWord.word (inventoryBound (next runtime))
        (SourceHistoryGrowth.remainder (retained runtime) (SourceHistoryWord.density (inventoryBound (next runtime)))) :=
  word_from_actor _ _ _

theorem packet_update (runtime : LivingRuntimeState process) :
    packet (next runtime) = priorMass runtime • packet runtime + addedPacket runtime := by
  rw [packet_original, packet_original]
  change _ = _ + SourceMassCompletion.jointRead
    (word (depth (next runtime)) (inventoryBound (next runtime)) (addedDensity runtime))
  rw [added_word]
  have original := congrArg SourceMassCompletion.jointRead (SourceHistoryWord.density_update (retained runtime))
  rw [SourceHistoryWord.density_word, SourceHistoryWord.density_word, map_add, LinearMap.map_smul_of_tower] at original
  exact original

theorem packet_mass (runtime : LivingRuntimeState process) : SourceMassCompletion.massRead (packet runtime) = 1 := by
  rw [packet_original, SourceMassCompletion.massRead_source, mass_meanWord]

theorem added_mass (runtime : LivingRuntimeState process) :
    SourceMassCompletion.massRead (addedPacket runtime) = ((1 - priorMass runtime : ℝ) : ℂ) := by
  have generated := congrArg SourceMassCompletion.massRead (packet_update runtime)
  rw [map_add, LinearMapClass.map_smul_of_tower, packet_mass, packet_mass] at generated
  simp only [Complex.real_smul, mul_one] at generated
  push_cast
  linear_combination -generated

theorem normalized_packet (runtime : LivingRuntimeState process)
    (value : FieldSpace (depth runtime) (inventoryBound runtime)) :
    joint (depth (next runtime)) (inventoryBound (next runtime))
        (normalize (depth runtime) (depth (next runtime)) (retained runtime) value) =
      joint (depth runtime) (inventoryBound runtime) value :=
  normalize_joint _ _ _ value

theorem normalized_norm (runtime : LivingRuntimeState process)
    (value : FieldSpace (depth runtime) (inventoryBound runtime)) :
    ‖normalize (depth runtime) (depth (next runtime)) (retained runtime) value‖ = ‖value‖ :=
  normalize_norm _ _ _ value

end
end SourceGeneratedAcquisitionJoint
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
