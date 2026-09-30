import H0mework.Physics.ConductanceCell.PacketLineEnergy
import H0mework.Physics.ConductanceCell.CellWork

/-! # Actual input-driver work continues while output capacitors are held -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Std.Sat Units.Interface

variable {α : Type} [DecidableEq α] [Hashable α]

noncomputable section

variable (technology : AIGCellTechnology) (graph : AIG α) (assignment : α → Bool) (initial : α → SIVolt)

theorem packetLinesPowerFunctions_continuous :
    Continuous (fun t => (packetLinesSupplyPowerAt technology graph assignment initial t).value) ∧
    Continuous (fun t => (packetLinesDissipatedPowerAt technology graph assignment initial t).value) := by
  have line (atom : α) :=
    (compilePacketLineDriver technology graph atom).powerFunctions_continuous
      (fun _ => packetLineControl (compilePacketLineDriver technology graph atom) (assignment atom))
      (fun _ => packetLineControl (compilePacketLineDriver technology graph atom) (assignment atom))
      (packetLineInputWave technology graph assignment initial atom)
      continuous_const continuous_const (packetLineInputWave_continuous _ _ _ _ atom)
  exact ⟨continuous_finsetSum (aigRegisteredInputAtoms graph) (fun atom _ => (line atom).1),
    continuous_finsetSum (aigRegisteredInputAtoms graph) (fun atom _ => (line atom).2)⟩

def packetLinesWorkAt (time : ℝ) : SIJoule :=
  ⟨∫ t in (0 : ℝ)..time, (packetLinesSupplyPowerAt technology graph assignment initial t).value⟩

def packetLinesHeatAt (time : ℝ) : SIJoule :=
  ⟨∫ t in (0 : ℝ)..time, (packetLinesDissipatedPowerAt technology graph assignment initial t).value⟩

theorem packetLinesHeatAt_nonneg (time : ℝ) (nonnegative : 0 ≤ time) :
    0 ≤ (packetLinesHeatAt technology graph assignment initial time).value :=
  intervalIntegral.integral_nonneg_of_forall nonnegative
    (fun t => packetLinesDissipatedPowerAt_nonneg _ _ _ _ t)

theorem packetLinesStoredEnergyAt_integrated_balance (time : ℝ) :
    (packetLinesStoredEnergyAt technology graph assignment initial time).value -
        (packetLinesStoredEnergyAt technology graph assignment initial 0).value =
      (packetLinesWorkAt technology graph assignment initial time).value -
        (packetLinesHeatAt technology graph assignment initial time).value := by
  obtain ⟨supplyContinuous, heatContinuous⟩ :=
    packetLinesPowerFunctions_continuous technology graph assignment initial
  have paid := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ Set.uIcc (0 : ℝ) time) =>
      packetLinesStoredEnergyAt_power_balance technology graph assignment initial t)
    ((supplyContinuous.sub heatContinuous).intervalIntegrable 0 time)
  rw [intervalIntegral.integral_sub (supplyContinuous.intervalIntegrable 0 time)
    (heatContinuous.intervalIntegrable 0 time)] at paid
  exact paid.symm

end
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical

