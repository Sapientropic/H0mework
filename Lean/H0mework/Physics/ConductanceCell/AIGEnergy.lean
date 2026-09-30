import H0mework.Physics.ConductanceCell.AIGCapacitorKCL
import H0mework.Physics.ConductanceCell.PacketLineEnergy
import H0mework.Physics.ConductanceCell.CellWork

/-! # One complete energy account for the actual driven graph before output isolation -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Std.Sat Units.Interface Storage

variable {α : Type} [DecidableEq α] [Hashable α]

noncomputable section

variable (technology : AIGCellTechnology) (graph : AIG α) (assignment : α → Bool)
  (inputInitial : α → SIVolt) (initial : Fin graph.decls.size → Bool → SIVolt)

def aigDrivenStoredEnergyAt (time : ℝ) : SIJoule :=
  ⟨(packetLinesStoredEnergyAt technology graph assignment inputInitial time).value +
    ∑ address : AIGCapacitorAddress graph,
      (aigCapacitorStoredEnergyAt technology graph
        (packetLineInputWave technology graph assignment inputInitial) initial address time).value⟩

def aigDrivenSupplyPowerAt (time : ℝ) : SIWatt :=
  ⟨(packetLinesSupplyPowerAt technology graph assignment inputInitial time).value +
    ∑ address : AIGCapacitorAddress graph,
      (aigCapacitorSupplyPowerAt technology graph
        (packetLineInputWave technology graph assignment inputInitial) initial address time).value⟩

def aigDrivenDissipatedPowerAt (time : ℝ) : SIWatt :=
  ⟨(packetLinesDissipatedPowerAt technology graph assignment inputInitial time).value +
    ∑ address : AIGCapacitorAddress graph,
      (aigCapacitorDissipatedPowerAt technology graph
        (packetLineInputWave technology graph assignment inputInitial) initial address time).value⟩

theorem aigDrivenStoredEnergyAt_nonneg (time : ℝ) :
    0 ≤ (aigDrivenStoredEnergyAt technology graph assignment inputInitial initial time).value :=
  add_nonneg (packetLinesStoredEnergyAt_nonneg _ _ _ _ _)
    (Finset.sum_nonneg fun address _ => aigCapacitorStoredEnergyAt_nonneg _ _ _ _ address time)

theorem aigDrivenDissipatedPowerAt_nonneg (time : ℝ) :
    0 ≤ (aigDrivenDissipatedPowerAt technology graph assignment inputInitial initial time).value :=
  add_nonneg (packetLinesDissipatedPowerAt_nonneg _ _ _ _ _)
    (Finset.sum_nonneg fun address _ => aigCapacitorDissipatedPowerAt_nonneg _ _ _ _ address time)

/-- All source work and heat rows read literal currents; neither is defined as the energy difference. -/
theorem aigDrivenStoredEnergyAt_power_balance (time : ℝ) :
    HasDerivAt (fun t => (aigDrivenStoredEnergyAt technology graph assignment inputInitial initial t).value)
      ((aigDrivenSupplyPowerAt technology graph assignment inputInitial initial time).value -
        (aigDrivenDissipatedPowerAt technology graph assignment inputInitial initial time).value) time := by
  have cells := HasDerivAt.fun_sum (u := Finset.univ)
    (fun address (_ : address ∈ (Finset.univ : Finset (AIGCapacitorAddress graph))) =>
      aigCapacitorStoredEnergyAt_power_balance technology graph
        (packetLineInputWave technology graph assignment inputInitial) initial
        (fun _ atom _ => packetLineInputWave_continuous _ _ _ _ atom) address time)
  convert (packetLinesStoredEnergyAt_power_balance technology graph assignment inputInitial time).add cells using 1
  all_goals first | rfl | (
    dsimp only [aigDrivenSupplyPowerAt, aigDrivenDissipatedPowerAt]
    rw [Finset.sum_sub_distrib]
    ring)

theorem aigDrivenPowerFunctions_continuous :
    Continuous (fun t => (aigDrivenSupplyPowerAt technology graph assignment inputInitial initial t).value) ∧
    Continuous (fun t => (aigDrivenDissipatedPowerAt technology graph assignment inputInitial initial t).value) := by
  have lines (atom : α) :=
    (compilePacketLineDriver technology graph atom).powerFunctions_continuous
      (fun _ => packetLineControl (compilePacketLineDriver technology graph atom) (assignment atom))
      (fun _ => packetLineControl (compilePacketLineDriver technology graph atom) (assignment atom))
      (packetLineInputWave technology graph assignment inputInitial atom)
      continuous_const continuous_const (packetLineInputWave_continuous _ _ _ _ atom)
  have cells (address : AIGCapacitorAddress graph) :=
    (compileDualRailCell technology graph address.val.1 address.val.2).powerFunctions_continuous
      (aigCapacitorControl technology graph (packetLineInputWave technology graph assignment inputInitial) initial address false)
      (aigCapacitorControl technology graph (packetLineInputWave technology graph assignment inputInitial) initial address true)
      (aigCapacitorVoltageAt technology graph (packetLineInputWave technology graph assignment inputInitial) initial address)
      (aigCapacitorControl_continuous _ _ _ _ (fun _ atom _ => packetLineInputWave_continuous _ _ _ _ atom) _ _)
      (aigCapacitorControl_continuous _ _ _ _ (fun _ atom _ => packetLineInputWave_continuous _ _ _ _ atom) _ _)
      (aigCapacitorVoltageAt_continuous _ _ _ _ (fun _ atom _ => packetLineInputWave_continuous _ _ _ _ atom) _)
  exact ⟨
    (continuous_finsetSum (aigRegisteredInputAtoms graph) (fun atom _ => (lines atom).1)).add
      (continuous_finsetSum Finset.univ (fun address _ => (cells address).1)),
    (continuous_finsetSum (aigRegisteredInputAtoms graph) (fun atom _ => (lines atom).2)).add
      (continuous_finsetSum Finset.univ (fun address _ => (cells address).2))⟩

def aigDrivenWorkAt (time : ℝ) : SIJoule :=
  ⟨∫ t in (0 : ℝ)..time, (aigDrivenSupplyPowerAt technology graph assignment inputInitial initial t).value⟩

def aigDrivenHeatAt (time : ℝ) : SIJoule :=
  ⟨∫ t in (0 : ℝ)..time, (aigDrivenDissipatedPowerAt technology graph assignment inputInitial initial t).value⟩

theorem aigDrivenHeatAt_nonneg (time : ℝ) (nonnegative : 0 ≤ time) :
    0 ≤ (aigDrivenHeatAt technology graph assignment inputInitial initial time).value :=
  intervalIntegral.integral_nonneg_of_forall nonnegative
    (fun t => aigDrivenDissipatedPowerAt_nonneg _ _ _ _ _ t)

theorem aigDrivenStoredEnergyAt_integrated_balance (time : ℝ) :
    (aigDrivenStoredEnergyAt technology graph assignment inputInitial initial time).value -
        (aigDrivenStoredEnergyAt technology graph assignment inputInitial initial 0).value =
      (aigDrivenWorkAt technology graph assignment inputInitial initial time).value -
        (aigDrivenHeatAt technology graph assignment inputInitial initial time).value := by
  obtain ⟨supplyContinuous, heatContinuous⟩ :=
    aigDrivenPowerFunctions_continuous technology graph assignment inputInitial initial
  have paid := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ Set.uIcc (0 : ℝ) time) =>
      aigDrivenStoredEnergyAt_power_balance technology graph assignment inputInitial initial t)
    ((supplyContinuous.sub heatContinuous).intervalIntegrable 0 time)
  rw [intervalIntegral.integral_sub (supplyContinuous.intervalIntegrable 0 time)
    (heatContinuous.intervalIntegrable 0 time)] at paid
  exact paid.symm

end
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
