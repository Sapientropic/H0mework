import H0mework.Physics.ADCSource.InverseFlow
import H0mework.Physics.DrivenEnergy.StateCorrection

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace RLCSourceInverse

open Physical.Interface Units.Interface
open Netlist.Dissipative.Producer
open Netlist.Dissipative.Dimensioned.Producer Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

variable (source : DimensionedSeriesRLCSource)
  (frequencyAt : FiniteEmbodimentChannel → SIHertz)
  (driveAt : FiniteEmbodimentChannel → SIVoltagePhasor)

def residualPort (state : FiniteDimensionedSeriesRLCPortState) (time : SISecond) :
    FiniteDimensionedSeriesRLCPortState where
  voltageAt channel := state.voltageAt channel -
    (drivenPeriodicPortStateAt source frequencyAt driveAt time).voltageAt channel
  currentAt channel := state.currentAt channel -
    (drivenPeriodicPortStateAt source frequencyAt driveAt time).currentAt channel

def recoverInitial (state : FiniteDimensionedSeriesRLCPortState) (time : SISecond) :
    FiniteDimensionedSeriesRLCPortState :=
  let run := compileFiniteDimensionedSeriesRLCNetlistRun source
  let normalized := (compiledFiniteDimensionedSeriesRLCPortStateEquiv source).symm
    (residualPort source frequencyAt driveAt state time)
  let back := (compiledFiniteDimensionedSeriesRLCPortStateEquiv source)
    (finiteSeriesRLCFlowAt run.normalizedRun normalized
      (-(finiteDimensionedSeriesRLCNormalizedTimeAt run time)))
  RLCStateError.shift (drivenPeriodicPortStateAt source frequencyAt driveAt 0)
    back.voltageAt back.currentAt

theorem residual_total (initial : FiniteDimensionedSeriesRLCPortState) (time : SISecond) :
    residualPort source frequencyAt driveAt
      (drivenTotalPortStateAt source frequencyAt driveAt initial time) time =
    (compiledFiniteDimensionedSeriesRLCPortStateEquiv source)
      (finiteSeriesRLCFlowAt (compileFiniteDimensionedSeriesRLCNetlistRun source).normalizedRun
        (drivenHomogeneousInitialAt source frequencyAt driveAt initial)
        (finiteDimensionedSeriesRLCNormalizedTimeAt (compileFiniteDimensionedSeriesRLCNetlistRun source) time)) := by
  apply FiniteDimensionedSeriesRLCPortState.ext <;> funext channel <;> apply SIQuantity.ext
  · simp only [residualPort, drivenTotalPortStateAt, drivenTotalVoltageAt, drivenPeriodicPortStateAt,
      compiledFiniteDimensionedSeriesRLCPortStateEquiv, finiteDimensionedSeriesRLCVoltageAt,
      finiteSeriesRLCVoltageAt, SIQuantity.sub_value, SIQuantity.add_value, add_sub_cancel_left]
    rfl
  · simp only [residualPort, drivenTotalPortStateAt, drivenTotalCurrentAt, drivenPeriodicPortStateAt,
      compiledFiniteDimensionedSeriesRLCPortStateEquiv, finiteDimensionedSeriesRLCCurrentAt,
      finiteSeriesRLCCurrentAt, SIQuantity.sub_value, SIQuantity.add_value, add_sub_cancel_left]
    rfl

theorem recover_total (initial : FiniteDimensionedSeriesRLCPortState) (time : SISecond) :
    recoverInitial source frequencyAt driveAt
      (drivenTotalPortStateAt source frequencyAt driveAt initial time) time = initial := by
  unfold recoverInitial
  rw [residual_total, Equiv.symm_apply_apply]
  dsimp only
  rw [flow_left_inverse]
  change RLCStateError.shift (drivenPeriodicPortStateAt source frequencyAt driveAt 0)
    (finiteDimensionedSeriesRLCPortStateOfNormalized _
      (drivenHomogeneousInitialAt source frequencyAt driveAt initial)).voltageAt
    (finiteDimensionedSeriesRLCPortStateOfNormalized _
      (drivenHomogeneousInitialAt source frequencyAt driveAt initial)).currentAt = initial
  rw [drivenHomogeneousInitial_portState_exact]
  apply FiniteDimensionedSeriesRLCPortState.ext <;> funext channel <;> apply SIQuantity.ext <;>
    simp only [RLCStateError.shift, drivenPeriodicPortStateAt, drivenInitialPortResidualAt,
      SIQuantity.add_value, SIQuantity.sub_value] <;> ring

end
end RLCSourceInverse
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
