import H0mework.Fock.ReceivedStep.NativeCount

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalStep

def receiveState {Key : Type*} (bound stride : Nat) (nonunit : stride ≠ 0)
    (received : Key → SourceRationalWindowReadout.Samples bound (stride + 1)) : SourceConditionalNativeObservers.State Key bound :=
  fun key =>
    let row := SourceRationalWindowReadout.recover bound stride nonunit (received key)
    (rowCount bound row, row)

open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem state_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) {Key : Type*} [DecidableEq Key] (read : Nat → Key) :
    receiveState (inventoryBound runtime) index.val nonunit
      (fun key phase => SourceFiniteObserverCalculation.posteriorCalculate
        (inventoryBound runtime) (index.val + 1) 0 phase.val read key) =
      SourceConditionalNativeObservers.generate read (inventoryBound runtime) := by
  funext key
  apply Prod.ext
  · change rowCount (inventoryBound runtime)
      (SourceRationalWindowReadout.recover (inventoryBound runtime) index.val nonunit _) = _
    rw [SourceRationalWindowReadout.recovered_posterior, count_source]
  · exact SourceRationalWindowReadout.recovered_posterior runtime index nonunit read key

end
end SourceReceivedConditionalStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
