import H0mework.Probability.Source.Field
import H0mework.Probability.Runtime.InvariantMoments

/-! The canonical runtime's actual samples are the same native-source observation construction. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.Runtime

open SourceGeneratedScalarCofinalTopology
open SourceGeneratedRuntimeHistoryProbability MeasureTheory

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)

theorem advance_state (runtime : LivingRuntimeState process) (depth : Nat) :
    (runtime.advance depth).state = process.successor^[depth] runtime.state := by
  induction depth with
  | zero => rfl
  | succ depth previous =>
      exact (congrArg process.successor previous).trans
        (Function.iterate_succ_apply' process.successor depth runtime.state).symm

theorem fieldPoint_eq (state : process.State) :
    NativeProbability.fieldPoint read state =
      SourceOwnedObservationHistory.fieldPoint process.successor read state := rfl

local instance : MeasurableSpace (NativeProbability.Field read) := NativeProbability.fieldBorel read
local instance : MeasurableSpace (SourceOwnedObservationHistory.Field process.successor read) :=
  SourceOwnedObservationHistory.fieldBorel process.successor read

theorem empirical_eq (runtime : LivingRuntimeState process) (bound : Nat) :
    NativeProbability.empirical read runtime bound =
      SourceOwnedObservationHistory.empirical process.successor read runtime.state bound := by
  apply ProbabilityMeasure.toMeasure_injective
  change (NativeProbability.fieldPMF read runtime bound).toMeasure =
    (SourceOwnedObservationHistory.fieldPMF process.successor read runtime.state bound).toMeasure
  apply congrArg PMF.toMeasure
  unfold NativeProbability.fieldPMF SourceOwnedObservationHistory.fieldPMF
  rw [SourceGeneratedRuntimeHistoryProbability.statePMF, PMF.map_comp,
    SourceOwnedObservationHistory.statePMF, PMF.map_comp]
  congr 1
  funext index
  exact (fieldPoint_eq read _).trans
    (congrArg (SourceOwnedObservationHistory.fieldPoint process.successor read)
      (advance_state runtime index.val))

end
end SourceOwnedObservationHistory.Runtime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
