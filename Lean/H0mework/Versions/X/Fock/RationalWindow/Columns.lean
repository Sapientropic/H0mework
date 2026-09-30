import H0mework.Versions.X.Fock.FiniteObserver.Material

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRationalWindowReadout

abbrev Samples (bound scale : Nat) := Fin (scale + 1) → Fin (bound + 1) → ℚ

def column (bound scale : Nat) (samples : Samples bound scale) (actor : Fin (bound + 1)) (phase : Fin (scale + 1)) : ℚ :=
  samples phase actor + (∑ source, samples phase source) +
    (scale : ℚ)^2 * ((actor.val + 1 : Nat) : ℚ) *
      (∑ source, ((source.val + 1 : Nat) : ℚ) * samples phase source)

open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def embed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (samples : Samples (inventoryBound runtime + steps) (index.val + 1)) : SourceOperatorObservationAcquisition.Window runtime index :=
  fun phase => SourceFiniteObserverCalculation.finiteRead (inventoryBound runtime + steps) (fun actor => (samples phase actor : ℂ))

theorem column_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (samples : Samples (inventoryBound runtime + steps) (index.val + 1))
    (actor : Fin (inventoryBound runtime + steps + 1)) (phase : Fin (index.val + 2)) :
    (column (inventoryBound runtime + steps) (index.val + 1) samples actor phase : ℂ) =
      SourceOperatorObservationAcquisition.columns runtime index steps actor phase (embed runtime index steps samples) := by
  change _ = inner ℂ (SourceColumnForcing.column (inventoryBound runtime) index actor.val)
    (SourceCopyGraph.action (inventoryBound runtime) index (SourceFiniteObserverCalculation.finiteRead _ _))
  rw [SourceFiniteObserverCalculation.finite_pairing]
  simp only [column, Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_sum, Rat.cast_natCast]

theorem posterior_samples (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    {Key : Type*} [DecidableEq Key] (read : Nat → Key) (key : Key) :
    embed runtime index steps (fun phase => SourceFiniteObserverCalculation.posteriorCalculate
      (inventoryBound runtime) (index.val + 1) steps phase.val read key) =
      SourceCopyTemporalBoundary.recordedPrefix runtime index steps (index.val + 1)
        (SourceConditionalNativePosterior.decoder runtime read key) :=
  SourceFiniteObserverCalculation.window_source runtime index steps (index.val + 1) read key

end
end SourceRationalWindowReadout
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
