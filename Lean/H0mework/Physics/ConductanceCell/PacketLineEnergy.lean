import H0mework.Physics.ConductanceCell.PacketLineDriver
import H0mework.Physics.ConductanceCell.Energy

/-! # One energy/power row per actual registered input driver -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Std.Sat Units.Interface

variable {α : Type} [DecidableEq α] [Hashable α]

def aigRegisteredInputAtoms (graph : AIG α) : Finset α :=
  (Finset.univ : Finset (Fin graph.decls.size)).biUnion fun node =>
    match graph.decls[node.val] with
    | .atom atom => {atom}
    | _ => ∅

theorem mem_aigRegisteredInputAtoms_iff (graph : AIG α) (atom : α) :
    atom ∈ aigRegisteredInputAtoms graph ↔
      ∃ node : Fin graph.decls.size, graph.decls[node.val] = .atom atom := by
  simp only [aigRegisteredInputAtoms, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨node, selected⟩
    cases declaration : graph.decls[node.val] with
    | false => simp [declaration] at selected
    | atom name =>
      simp only [declaration, Finset.mem_singleton] at selected
      exact ⟨node, selected ▸ declaration⟩
    | gate left right => simp [declaration] at selected
  · rintro ⟨node, selected⟩
    exact ⟨node, by simp [selected]⟩

noncomputable section

variable (technology : AIGCellTechnology) (graph : AIG α)
  (assignment : α → Bool) (initial : α → SIVolt)

def packetLineStoredEnergyAt (atom : α) (time : ℝ) : SIJoule :=
  ⟨(compilePacketLineDriver technology graph atom).capacitance.value / 2 *
    (packetLineInputWave technology graph assignment initial atom time).value ^ 2⟩

def packetLineSupplyPowerAt (atom : α) (time : ℝ) : SIWatt :=
  let driver := compilePacketLineDriver technology graph atom
  let control := packetLineControl driver (assignment atom)
  driver.supplyPower control control (packetLineInputWave technology graph assignment initial atom time)

def packetLineDissipatedPowerAt (atom : α) (time : ℝ) : SIWatt :=
  let driver := compilePacketLineDriver technology graph atom
  let control := packetLineControl driver (assignment atom)
  driver.dissipatedPower control control (packetLineInputWave technology graph assignment initial atom time)

theorem packetLineStoredEnergyAt_nonneg (atom : α) (time : ℝ) :
    0 ≤ (packetLineStoredEnergyAt technology graph assignment initial atom time).value :=
  mul_nonneg (div_nonneg (compilePacketLineDriver technology graph atom).capacitance_pos.le
    (by norm_num)) (sq_nonneg _)

theorem packetLineDissipatedPowerAt_nonneg (atom : α) (time : ℝ) :
    0 ≤ (packetLineDissipatedPowerAt technology graph assignment initial atom time).value :=
  (compilePacketLineDriver technology graph atom).dissipatedPower_nonneg _ _ _

theorem packetLineStoredEnergyAt_power_balance (atom : α) (time : ℝ) :
    HasDerivAt (fun t => (packetLineStoredEnergyAt technology graph assignment initial atom t).value)
      ((packetLineSupplyPowerAt technology graph assignment initial atom time).value -
        (packetLineDissipatedPowerAt technology graph assignment initial atom time).value) time :=
  (compilePacketLineDriver technology graph atom).storedEnergyAt_power_balance _ _ _ _

/-- Duplicate graph declarations share one driver; their loads have already
been summed in its source capacitance. No unregistered atom owns a ledger row. -/
def packetLinesStoredEnergyAt (time : ℝ) : SIJoule :=
  ⟨∑ atom ∈ aigRegisteredInputAtoms graph,
    (packetLineStoredEnergyAt technology graph assignment initial atom time).value⟩

def packetLinesSupplyPowerAt (time : ℝ) : SIWatt :=
  ⟨∑ atom ∈ aigRegisteredInputAtoms graph,
    (packetLineSupplyPowerAt technology graph assignment initial atom time).value⟩

def packetLinesDissipatedPowerAt (time : ℝ) : SIWatt :=
  ⟨∑ atom ∈ aigRegisteredInputAtoms graph,
    (packetLineDissipatedPowerAt technology graph assignment initial atom time).value⟩

theorem packetLinesStoredEnergyAt_nonneg (time : ℝ) :
    0 ≤ (packetLinesStoredEnergyAt technology graph assignment initial time).value :=
  Finset.sum_nonneg fun atom _ => packetLineStoredEnergyAt_nonneg _ _ _ _ atom time

theorem packetLinesDissipatedPowerAt_nonneg (time : ℝ) :
    0 ≤ (packetLinesDissipatedPowerAt technology graph assignment initial time).value :=
  Finset.sum_nonneg fun atom _ => packetLineDissipatedPowerAt_nonneg _ _ _ _ atom time

theorem packetLinesStoredEnergyAt_power_balance (time : ℝ) :
    HasDerivAt (fun t => (packetLinesStoredEnergyAt technology graph assignment initial t).value)
      ((packetLinesSupplyPowerAt technology graph assignment initial time).value -
        (packetLinesDissipatedPowerAt technology graph assignment initial time).value) time := by
  have generated := HasDerivAt.fun_sum (u := aigRegisteredInputAtoms graph)
    (fun atom _ => packetLineStoredEnergyAt_power_balance technology graph assignment initial atom time)
  simpa only [packetLinesStoredEnergyAt, packetLinesSupplyPowerAt,
    packetLinesDissipatedPowerAt, Finset.sum_sub_distrib] using generated

end
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
