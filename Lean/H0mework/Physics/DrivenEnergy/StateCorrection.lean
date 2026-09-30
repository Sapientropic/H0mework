import H0mework.Physics.DrivenEnergy.RLCBankWork

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace RLCStateError

open Units.Interface Physical.Interface
open Netlist.Dissipative.Dimensioned.Producer Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

def shift (state : FiniteDimensionedSeriesRLCPortState)
    (voltageError : FiniteEmbodimentChannel → SIVolt)
    (currentError : FiniteEmbodimentChannel → SIAmpere) : FiniteDimensionedSeriesRLCPortState where
  voltageAt channel := state.voltageAt channel + voltageError channel
  currentAt channel := state.currentAt channel + currentError channel

def correction (source : DimensionedSeriesRLCSource) (state : FiniteDimensionedSeriesRLCPortState)
    (voltageError : FiniteEmbodimentChannel → SIVolt)
    (currentError : FiniteEmbodimentChannel → SIAmpere) : SIJoule :=
  let run := compileFiniteDimensionedSeriesRLCNetlistRun source
  ⟨∑ channel, (
    (run.capacitanceAt channel).value * (state.voltageAt channel).value * (voltageError channel).value +
      (run.capacitanceAt channel).value / 2 * (voltageError channel).value ^ 2 +
    (run.inductanceAt channel).value * (state.currentAt channel).value * (currentError channel).value +
      (run.inductanceAt channel).value / 2 * (currentError channel).value ^ 2)⟩

theorem storedEnergy_difference (source : DimensionedSeriesRLCSource) (state : FiniteDimensionedSeriesRLCPortState)
    (voltageError : FiniteEmbodimentChannel → SIVolt)
    (currentError : FiniteEmbodimentChannel → SIAmpere) :
    drivenRLCBankStoredEnergy source (shift state voltageError currentError) -
      drivenRLCBankStoredEnergy source state = correction source state voltageError currentError := by
  apply SIQuantity.ext
  simp only [SIQuantity.sub_value, drivenRLCBankStoredEnergy, drivenRLCStoredEnergy,
    shift, correction, SIQuantity.add_value]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro channel _
  ring

end
end RLCStateError
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
