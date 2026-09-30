import H0mework.Chemistry.LAlanineBandSource.Data
import H0mework.Chemistry.LAlanineTrueFlowQuantitative.RuntimeConsumers

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandSource

noncomputable section

def sourceParentRuntime := TrueFlowQuantitativeRuntime.quantitativeRuntimeAfterFirst
theorem sourceParent_same_occurrence :
    sourceParentRuntime.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl
theorem sourceParent_clock : Reentry.Runtime.reentryPhysicalTime sourceParentRuntime.state.current =
    3 * Propagation.Producer.nativeClockStep :=
  TrueFlowQuantitativeRuntime.quantitativeRuntime_clock_preserved TrueFlowQuantitativeRuntime.quantitativeRuntimeSeed

end
end LAlanine40K2025.BasinRefinement.WholeBandSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
