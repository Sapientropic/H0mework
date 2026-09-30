import H0mework.Fock.InverseDistribution.Source
import H0mework.Fock.HistoryConditional.GWordInverseSource
import H0mework.Fock.HistoryConditional.NativeBirthSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNativeInverseDistribution

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem embed_action (program : Nat × Nat) (value : Nat →₀ ℚ) :
    SourceConditionalRationalStream.embedWord (action program value) =
      SourceGWordProgram.complexAction program (SourceConditionalRationalStream.embedWord value) := by
  change Finsupp.mapRange (Algebra.linearMap ℚ ℂ) (map_zero (Algebra.linearMap ℚ ℂ)) (Finsupp.mapDomain (SourceCopyWordAffine.execute program) value) =
    Finsupp.mapDomain (SourceCopyWordAffine.execute program) (Finsupp.mapRange (Algebra.linearMap ℚ ℂ) (map_zero (Algebra.linearMap ℚ ℂ)) value)
  exact (Finsupp.mapDomain_mapRange _ _ _ _ (map_add (Algebra.linearMap ℚ ℂ))).symm

theorem g_reconstruction (bound depth : Nat) (word : List (Fock.Letter depth)) (weights : Fin (bound + 1) → ℚ) :
    SourceCompiledGWord.effect depth word (SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord
      (recovered bound (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) weights))) +
      SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord
        (residual bound (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) weights)) =
      SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (SourceConditionalNativeKeys.word bound weights)) := by
  rw [SourceCompiledGWord.effect, SourceGWordProgram.action_source, ← embed_action, ← map_add, ← map_add,
    reconstruction bound _ (SourceCompiledWordOperator.slope_positive _)]

theorem decoder_reconstruction {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) :
    let weights := (SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).2
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    SourceCompiledGWord.effect depth word (SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord
      (recovered (inventoryBound runtime) program weights))) +
      SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (residual (inventoryBound runtime) program weights)) =
      SourceConditionalNativePosterior.decoder runtime read key := by
  dsimp only
  rw [SourceConditionalNativeBirth.decoder_word]
  exact g_reconstruction _ depth word _

theorem decoder_inverse {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) :
    let weights := (SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).2
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    SourceGWordInverse.recover depth word (SourceConditionalNativePosterior.decoder runtime read key) =
      SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (recovered (inventoryBound runtime) program weights)) +
      SourceGWordInverse.recover depth word
        (SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (residual (inventoryBound runtime) program weights))) := by
  dsimp only
  rw [← decoder_reconstruction runtime depth word read key, map_add, SourceGWordInverse.recover_effect]

end
end SourceNativeInverseDistribution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
