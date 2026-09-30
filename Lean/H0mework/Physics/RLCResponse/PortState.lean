import H0mework.Physics.RLCResponse.State
import H0mework.Physics.RLCNetlist.DimensionedRun

/-!
# Exact physical `(V,I)` port-state coordinates

The compiled damped shear gives a bijective coordinate chart between the
normalized two-dimensional state and the physical voltage/current port state.
This is the exact carrier for arbitrary circuit initial data.  The auxiliary
charge coordinate in `FiniteDimensionedSeriesRLCState` is intentionally absent.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Immortality
namespace Embodied
namespace Canonical
namespace Coupling
namespace Physical
namespace Netlist
namespace Dissipative
namespace Dimensioned
namespace Driven
namespace Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Units.Interface

noncomputable section

def finiteDimensionedSeriesRLCPortStateOfNormalized
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (state : FiniteEmbodimentState) :
    FiniteDimensionedSeriesRLCPortState where
  voltageAt := (finiteDimensionedSeriesRLCStateOfNormalized run state).voltageAt
  currentAt := (finiteDimensionedSeriesRLCStateOfNormalized run state).currentAt

def normalizeFiniteDimensionedSeriesRLCPortState
    (run : FiniteDimensionedSeriesRLCNetlistRunOccurrence)
    (state : FiniteDimensionedSeriesRLCPortState) : FiniteEmbodimentState :=
  fun channel =>
    (((state.currentAt channel).value / run.scale.currentScale.value +
          run.normalizedRun.dampingRateAt channel *
            ((state.voltageAt channel).value /
              run.scale.voltageScale.value)) /
        run.normalizedRun.baseRun.frequencyAt channel,
      (state.voltageAt channel).value / run.scale.voltageScale.value)

theorem compiledFiniteDimensionedSeriesRLC_normalize_portStateOfNormalized
    (source : DimensionedSeriesRLCSource)
    (state : FiniteEmbodimentState) :
    normalizeFiniteDimensionedSeriesRLCPortState
        (compileFiniteDimensionedSeriesRLCNetlistRun source)
        (finiteDimensionedSeriesRLCPortStateOfNormalized
          (compileFiniteDimensionedSeriesRLCNetlistRun source) state) =
      state := by
  funext channel
  rcases hstate : state channel with ⟨sourceCoordinate, voltageCoordinate⟩
  apply Prod.ext
  · simp only [normalizeFiniteDimensionedSeriesRLCPortState,
      finiteDimensionedSeriesRLCPortStateOfNormalized,
      finiteDimensionedSeriesRLCStateOfNormalized, sourcePort, targetPort,
      hstate, SIQuantity.scale_value]
    have frequencyNonzero :
        (compileFiniteSeriesRLCNetlistRun source.1).baseRun.frequencyAt
          channel ≠ 0 :=
      ne_of_gt
        (compiledFiniteSeriesRLCNetlistRun_frequency_pos source.1 channel)
    rw [compiledFiniteDimensionedSeriesRLC_normalizedRun]
    field_simp [source.2.currentScale_ne, source.2.voltageScale_ne,
      frequencyNonzero]
    ring
  · simp only [normalizeFiniteDimensionedSeriesRLCPortState,
      finiteDimensionedSeriesRLCPortStateOfNormalized,
      finiteDimensionedSeriesRLCStateOfNormalized, sourcePort, targetPort,
      hstate, SIQuantity.scale_value]
    field_simp [source.2.voltageScale_ne]

theorem compiledFiniteDimensionedSeriesRLC_portStateOfNormalized_normalize
    (source : DimensionedSeriesRLCSource)
    (state : FiniteDimensionedSeriesRLCPortState) :
    finiteDimensionedSeriesRLCPortStateOfNormalized
        (compileFiniteDimensionedSeriesRLCNetlistRun source)
        (normalizeFiniteDimensionedSeriesRLCPortState
          (compileFiniteDimensionedSeriesRLCNetlistRun source) state) =
      state := by
  apply FiniteDimensionedSeriesRLCPortState.ext <;> funext channel
  · apply SIQuantity.ext
    simp only [finiteDimensionedSeriesRLCPortStateOfNormalized,
      normalizeFiniteDimensionedSeriesRLCPortState,
      finiteDimensionedSeriesRLCStateOfNormalized, targetPort,
      SIQuantity.scale_value]
    field_simp [source.2.voltageScale_ne]
  · have frequencyNonzero :
        (compileFiniteSeriesRLCNetlistRun source.1).baseRun.frequencyAt
          channel ≠ 0 :=
      ne_of_gt
        (compiledFiniteSeriesRLCNetlistRun_frequency_pos source.1 channel)
    apply SIQuantity.ext
    simp only [finiteDimensionedSeriesRLCPortStateOfNormalized,
      normalizeFiniteDimensionedSeriesRLCPortState,
      finiteDimensionedSeriesRLCStateOfNormalized, sourcePort, targetPort,
      SIQuantity.scale_value]
    rw [compiledFiniteDimensionedSeriesRLC_normalizedRun]
    field_simp [source.2.currentScale_ne, source.2.voltageScale_ne,
      frequencyNonzero]
    ring

def compiledFiniteDimensionedSeriesRLCPortStateEquiv
    (source : DimensionedSeriesRLCSource) :
    FiniteEmbodimentState ≃ FiniteDimensionedSeriesRLCPortState where
  toFun := finiteDimensionedSeriesRLCPortStateOfNormalized
    (compileFiniteDimensionedSeriesRLCNetlistRun source)
  invFun := normalizeFiniteDimensionedSeriesRLCPortState
    (compileFiniteDimensionedSeriesRLCNetlistRun source)
  left_inv := compiledFiniteDimensionedSeriesRLC_normalize_portStateOfNormalized
    source
  right_inv :=
    compiledFiniteDimensionedSeriesRLC_portStateOfNormalized_normalize source

theorem compiledFiniteDimensionedSeriesRLCPortStateOfNormalized_injective
    (source : DimensionedSeriesRLCSource) :
    Function.Injective
      (finiteDimensionedSeriesRLCPortStateOfNormalized
        (compileFiniteDimensionedSeriesRLCNetlistRun source)) :=
  (compiledFiniteDimensionedSeriesRLCPortStateEquiv source).injective

end


end Producer
end Driven
end Dimensioned
end Dissipative
end Netlist
end Physical
end Coupling
end Canonical
end Embodied
end Immortality
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.compiledFiniteDimensionedSeriesRLC_normalize_portStateOfNormalized
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.compiledFiniteDimensionedSeriesRLC_portStateOfNormalized_normalize
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.compiledFiniteDimensionedSeriesRLCPortStateEquiv
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.compiledFiniteDimensionedSeriesRLCPortStateOfNormalized_injective
