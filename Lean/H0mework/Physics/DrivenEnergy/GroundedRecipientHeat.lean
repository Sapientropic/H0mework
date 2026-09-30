import H0mework.Physics.DrivenEnergy.RLCBankWork
import H0mework.Physics.ReceiverActuation.CommonRecipient
import H0mework.Physics.ReceiverActuation.CommonRecovery

/-!
# Actual grounded-recipient heat during common recovery

The already generated common load endpoint seeds the existing homogeneous RLC solver.
Its physical half-energy derivative is exactly minus actual resistor power. The complete
ten-channel heat is independently integrated and consumes the source-generated common clock.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Units.Interface Physical.Interface Cells.Conductance MeasureTheory
open Netlist.Dissipative.Dimensioned.Producer Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section
namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
  {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {clockMax : Nat} {technology : AIGCellTechnology}
  (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
  (current : FiniteADCWholeJointCurrent hardware clockMax technology)

/-- The actual series-current projection pays resistor heat; there is no driving voltage here. -/
def commonRecipientHeatPowerAt (channel : FiniteEmbodimentChannel) (time : ℝ) : SIWatt :=
  ⟨((compileFiniteDimensionedSeriesRLCNetlistRun
      (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)).seriesResistanceAt
      channel).value *
    ((commonRecipientRecoveryAt downstreamTechnology downstreamGraph current time).currentAt channel).value ^ 2⟩

theorem commonRecipientHeatPowerAt_nonneg (channel : FiniteEmbodimentChannel) (time : ℝ) :
    0 ≤ (commonRecipientHeatPowerAt downstreamTechnology downstreamGraph current channel time).value :=
  mul_nonneg (compiledFiniteDimensionedSeriesRLC_resistance_pos
    (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource) channel).le (sq_nonneg _)

/-- The old energy convention has derivative `-2 R I²`; its installed physical half pays `-R I²`. -/
theorem commonRecipientRecoveryEnergyAt_power_balance (channel : FiniteEmbodimentChannel) (time : ℝ) :
    HasDerivAt (fun t => (commonRecipientRecoveryEnergyAt downstreamTechnology downstreamGraph current channel t).value)
      (-(commonRecipientHeatPowerAt downstreamTechnology downstreamGraph current channel time).value) time := by
  have derivative := (compiledFiniteDimensionedSeriesRLC_energy_hasSIQuantityDerivAt
    (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
    (normalizeFiniteDimensionedSeriesRLCPortState
      (compileFiniteDimensionedSeriesRLCNetlistRun
        (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource))
      (commonOutputLoadRecipient downstreamTechnology downstreamGraph current)) channel ⟨time⟩).valueHasDerivAt.const_mul
        (1 / 2 : ℝ)
  convert derivative using 1 <;> first | rfl | (
    simp only [commonRecipientHeatPowerAt, commonRecipientRecoveryAt,
      finiteDimensionedSeriesRLCEnergyDissipationAt, SIQuantity.smul_value, resistivePower_value]
    ring_nf
    rfl)

theorem commonRecipientHeatPowerAt_continuous (channel : FiniteEmbodimentChannel) :
    Continuous (fun t => (commonRecipientHeatPowerAt downstreamTechnology downstreamGraph current channel t).value) := by
  have currentContinuous : Continuous (fun t =>
      ((commonRecipientRecoveryAt downstreamTechnology downstreamGraph current t).currentAt channel).value) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (finiteDimensionedSeriesRLCCurrent_hasSIQuantityDerivAt _ _ channel ⟨t⟩).valueHasDerivAt.continuousAt)
  exact continuous_const.mul (currentContinuous.pow 2)

def commonRecipientRecoveryTotalEnergyAt (time : ℝ) : SIJoule :=
  ⟨∑ channel, (commonRecipientRecoveryEnergyAt downstreamTechnology downstreamGraph current channel time).value⟩

def commonRecipientRecoveryTotalHeatPowerAt (time : ℝ) : SIWatt :=
  ⟨∑ channel, (commonRecipientHeatPowerAt downstreamTechnology downstreamGraph current channel time).value⟩

theorem commonRecipientRecoveryTotalEnergyAt_eq_physical (time : ℝ) :
    commonRecipientRecoveryTotalEnergyAt downstreamTechnology downstreamGraph current time =
      drivenRLCBankStoredEnergy
        (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
        (commonRecipientRecoveryAt downstreamTechnology downstreamGraph current time) := by
  apply SIQuantity.ext
  exact Finset.sum_congr (rfl : (Finset.univ : Finset FiniteEmbodimentChannel) = Finset.univ) (fun channel _ =>
    commonRecipientRecoveryEnergyAt_eq_physical downstreamTechnology downstreamGraph current channel time)

theorem commonRecipientRecoveryTotalEnergyAt_initial :
    commonRecipientRecoveryTotalEnergyAt downstreamTechnology downstreamGraph current 0 =
      drivenRLCBankStoredEnergy
        (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
        (commonOutputLoadRecipient downstreamTechnology downstreamGraph current) := by
  rw [commonRecipientRecoveryTotalEnergyAt_eq_physical, commonRecipientRecoveryAt_initial]

theorem commonRecipientRecoveryTotalHeatPowerAt_continuous :
    Continuous (fun t => (commonRecipientRecoveryTotalHeatPowerAt downstreamTechnology downstreamGraph current t).value) :=
  continuous_finsetSum Finset.univ (fun channel _ =>
    commonRecipientHeatPowerAt_continuous downstreamTechnology downstreamGraph current channel)

theorem commonRecipientRecoveryTotalEnergyAt_power_balance (time : ℝ) :
    HasDerivAt (fun t => (commonRecipientRecoveryTotalEnergyAt downstreamTechnology downstreamGraph current t).value)
      (-(commonRecipientRecoveryTotalHeatPowerAt downstreamTechnology downstreamGraph current time).value) time := by
  have channels := HasDerivAt.fun_sum (u := Finset.univ)
    (fun channel (_ : channel ∈ (Finset.univ : Finset FiniteEmbodimentChannel)) =>
      commonRecipientRecoveryEnergyAt_power_balance downstreamTechnology downstreamGraph current channel time)
  convert channels using 1 <;> first | rfl | (
    dsimp only [commonRecipientRecoveryTotalHeatPowerAt]
    rw [Finset.sum_neg_distrib])

/-- Independently integrated actual whole-recipient heat on any finite interval. -/
def commonRecipientRecoveryHeatBetween (start stop : ℝ) : SIJoule :=
  ⟨∫ t in start..stop, (commonRecipientRecoveryTotalHeatPowerAt downstreamTechnology downstreamGraph current t).value⟩

theorem commonRecipientRecoveryHeatBetween_nonneg (start stop : ℝ) (ordered : start ≤ stop) :
    0 ≤ (commonRecipientRecoveryHeatBetween downstreamTechnology downstreamGraph current start stop).value :=
  intervalIntegral.integral_nonneg_of_forall ordered (fun t =>
    Finset.sum_nonneg (s := Finset.univ) (fun channel _ =>
      commonRecipientHeatPowerAt_nonneg downstreamTechnology downstreamGraph current channel t))

/-- Exact heat settlement from the original common-load `(V,I)` without resetting any channel. -/
theorem commonRecipientRecoveryTotalEnergyAt_integrated_balance (start stop : ℝ) :
    (commonRecipientRecoveryTotalEnergyAt downstreamTechnology downstreamGraph current stop).value -
      (commonRecipientRecoveryTotalEnergyAt downstreamTechnology downstreamGraph current start).value =
        -(commonRecipientRecoveryHeatBetween downstreamTechnology downstreamGraph current start stop).value := by
  have paid := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ Set.uIcc start stop) =>
      commonRecipientRecoveryTotalEnergyAt_power_balance downstreamTechnology downstreamGraph current t)
    ((commonRecipientRecoveryTotalHeatPowerAt_continuous downstreamTechnology downstreamGraph current).neg.intervalIntegrable start stop)
  rw [intervalIntegral.integral_neg] at paid
  exact paid.symm

theorem commonRecipientRecovery_generated_time_paid :
    let time := (commonRecoverySampleTime downstreamTechnology downstreamGraph current).value
    (commonRecipientRecoveryTotalEnergyAt downstreamTechnology downstreamGraph current time).value -
      (drivenRLCBankStoredEnergy
        (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
        (commonOutputLoadRecipient downstreamTechnology downstreamGraph current)).value =
      -(commonRecipientRecoveryHeatBetween downstreamTechnology downstreamGraph current 0 time).value := by
  have paid := commonRecipientRecoveryTotalEnergyAt_integrated_balance downstreamTechnology downstreamGraph current
    0 (commonRecoverySampleTime downstreamTechnology downstreamGraph current).value
  rw [commonRecipientRecoveryTotalEnergyAt_initial] at paid
  exact paid

theorem commonRecipientHeatPowerAt_pos_of_current_ne_zero
    (channel : FiniteEmbodimentChannel) (time : ℝ)
    (nonzero : ((commonRecipientRecoveryAt downstreamTechnology downstreamGraph current time).currentAt channel).value ≠ 0) :
    0 < (commonRecipientHeatPowerAt downstreamTechnology downstreamGraph current channel time).value :=
  mul_pos (compiledFiniteDimensionedSeriesRLC_resistance_pos
    (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource) channel) (sq_pos_of_ne_zero nonzero)

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
