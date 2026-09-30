import H0mework.Computation.AIGHold.HeldCapacitorWork
import H0mework.Computation.AIGHold.InputWork

/-! # Nonnegative interval heat and exact two-endpoint work for the same held memory run -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells

open Std.Sat Units.Interface Conductance Storage Set MeasureTheory
open Netlist.Dissipative.Dimensioned.Driven.Producer

noncomputable section

private theorem nonnegative_power_integral_monotone (power : ℝ → ℝ)
    (continuous : Continuous power) (nonnegative : ∀ time, 0 ≤ power time) (origin : ℝ) :
    Monotone (fun time => ∫ t in origin..time, power t) := by
  intro earlier later ordered
  have joined := intervalIntegral.integral_add_adjacent_intervals
    (continuous.intervalIntegrable (μ := volume) origin earlier) (continuous.intervalIntegrable earlier later)
  have heat := intervalIntegral.integral_nonneg_of_forall (μ := volume) ordered nonnegative
  linarith

theorem Conductance.LoadedConductanceCellSource.drivenHeatAt_monotone
    (source : LoadedConductanceCellSource) (left right : ℝ → SIVolt) (initial : SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value)) :
    Monotone (fun time => (source.drivenHeatAt left right initial time).value) := by
  have continuous := (source.powerFunctions_continuous left right
    (fun t => ⟨source.drivenVoltageAt left right initial t⟩) leftContinuous rightContinuous
    (source.drivenVoltageAt_continuous left right initial leftContinuous rightContinuous)).2
  exact nonnegative_power_integral_monotone _ continuous
    (fun t => source.drivenDissipatedPowerAt_nonneg left right initial t) 0

/-- Only the actual post-switch power is required to be integrable. -/
theorem Storage.ClockedLeakyHoldSource.heatAt_monotoneOn
    {source : LoadedConductanceCellSource} (hold : ClockedLeakyHoldSource source)
    (input : ℝ → SIVolt) (capture : ℝ) :
    MonotoneOn (fun time => (hold.heatAt input capture time).value) (Ici capture) := by
  intro earlier afterEarlier later afterLater ordered
  have continuous : ContinuousOn (fun t => (hold.dissipatedPowerAt input capture t).value) (Ici capture) :=
    ((hold.voltageAt_continuousOn_after input capture).pow 2).div_const _
  have beforeIntegral := (continuous.mono
    (show Icc capture earlier ⊆ Ici capture from fun _ ht => ht.1)).intervalIntegrable_of_Icc (μ := volume) afterEarlier
  have segmentIntegrable := (continuous.mono
    (show Icc earlier later ⊆ Ici capture from fun _ ht => afterEarlier.trans ht.1)).intervalIntegrable_of_Icc (μ := volume) ordered
  have joined := intervalIntegral.integral_add_adjacent_intervals beforeIntegral segmentIntegrable
  have heat := intervalIntegral.integral_nonneg_of_forall (μ := volume) ordered
    (fun t => hold.dissipatedPowerAt_nonneg input capture t)
  change (∫ t in capture..earlier, _) ≤ ∫ t in capture..later, _
  linarith

namespace Conductance

variable {α : Type} [DecidableEq α] [Hashable α]
variable (technology : AIGCellTechnology) (graph : AIG α) (assignment : α → Bool) (initial : α → SIVolt)

theorem packetLinesHeatAt_monotone :
    Monotone (fun time => (packetLinesHeatAt technology graph assignment initial time).value) :=
  nonnegative_power_integral_monotone _
    (packetLinesPowerFunctions_continuous technology graph assignment initial).2
    (fun t => packetLinesDissipatedPowerAt_nonneg technology graph assignment initial t) 0

theorem packetLinesStoredEnergyAt_interval_balance (start finish : ℝ) :
    (packetLinesStoredEnergyAt technology graph assignment initial finish).value -
        (packetLinesStoredEnergyAt technology graph assignment initial start).value =
      ((packetLinesWorkAt technology graph assignment initial finish).value -
        (packetLinesWorkAt technology graph assignment initial start).value) -
      ((packetLinesHeatAt technology graph assignment initial finish).value -
        (packetLinesHeatAt technology graph assignment initial start).value) := by
  have first := packetLinesStoredEnergyAt_integrated_balance technology graph assignment initial start
  have last := packetLinesStoredEnergyAt_integrated_balance technology graph assignment initial finish
  linarith

theorem packetLinesHeatAt_interval_nonneg (start finish : ℝ) (ordered : start ≤ finish) :
    0 ≤ (packetLinesHeatAt technology graph assignment initial finish).value -
      (packetLinesHeatAt technology graph assignment initial start).value :=
  sub_nonneg.mpr (packetLinesHeatAt_monotone technology graph assignment initial ordered)

end Conductance
namespace Storage

variable {α β : Type} [DecidableEq α] [Hashable α] [DecidableEq β] [Hashable β] {width : Nat}
variable (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
  (memory : AIGCapacitorMemory technology (aigOutputBank entry).aig) (assignment : α → Bool)
  (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
  (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)
  (address : AIGCapacitorAddress (aigOutputBank entry).aig)

/-- The source cutoff and leakage restart are both monotone restrictions of actual power integrals. -/
theorem aigMemoryCapacitorHeatAt_monotone :
    Monotone (fun time => (aigMemoryCapacitorHeatAt technology entry memory assignment
      downstreamTechnology downstreamGraph clock code address time).value) := by
  let cell := compileDualRailCell technology (aigOutputBank entry).aig address.val.1 address.val.2
  have inputs : ∀ (node : Fin (aigOutputBank entry).aig.decls.size) atom,
      (aigOutputBank entry).aig.decls[node.val] = .atom atom →
        Continuous (fun t => (aigMemoryInputWave technology entry memory assignment atom t).value) :=
    fun _ atom _ => packetLineInputWave_continuous technology (aigOutputBank entry).aig assignment memory.inputInitial atom
  have driven := cell.drivenHeatAt_monotone
    (aigCapacitorControl technology (aigOutputBank entry).aig
      (aigMemoryInputWave technology entry memory assignment) memory.gateInitial address false)
    (aigCapacitorControl technology (aigOutputBank entry).aig
      (aigMemoryInputWave technology entry memory assignment) memory.gateInitial address true)
    (memory.gateInitial address.val.1 address.val.2)
    (aigCapacitorControl_continuous _ _ _ _ inputs address false)
    (aigCapacitorControl_continuous _ _ _ _ inputs address true)
  intro earlier later ordered
  by_cases held : aigMemoryCapacitorIsHeld entry address
  · simp only [aigMemoryCapacitorHeatAt, if_pos held]
    exact add_le_add (driven (min_le_min ordered le_rfl))
      ((compileHoldLeaseForGraph cell downstreamTechnology downstreamGraph clock code).heatAt_monotoneOn
        _ _ (Set.mem_Ici.mpr (le_max_left (aigMemoryCaptureTime technology entry clock code).value earlier))
        (Set.mem_Ici.mpr (le_max_left (aigMemoryCaptureTime technology entry clock code).value later))
        (max_le_max le_rfl ordered))
  · simp only [aigMemoryCapacitorHeatAt, if_neg held, add_zero]
    exact driven ordered

theorem aigMemoryCapacitorStoredEnergyAt_interval_balance (start finish : ℝ) :
    (aigMemoryCapacitorStoredEnergyAt technology entry memory assignment downstreamTechnology downstreamGraph
        clock code address finish).value -
      (aigMemoryCapacitorStoredEnergyAt technology entry memory assignment downstreamTechnology downstreamGraph
        clock code address start).value =
      ((aigMemoryCapacitorWorkAt technology entry memory assignment clock code address finish).value -
        (aigMemoryCapacitorWorkAt technology entry memory assignment clock code address start).value) -
      ((aigMemoryCapacitorHeatAt technology entry memory assignment downstreamTechnology downstreamGraph
          clock code address finish).value -
        (aigMemoryCapacitorHeatAt technology entry memory assignment downstreamTechnology downstreamGraph
          clock code address start).value) := by
  have first := aigMemoryCapacitorStoredEnergyAt_integrated_balance technology entry memory assignment
    downstreamTechnology downstreamGraph clock code address start
  have last := aigMemoryCapacitorStoredEnergyAt_integrated_balance technology entry memory assignment
    downstreamTechnology downstreamGraph clock code address finish
  linarith

theorem aigMemoryCapacitorHeatAt_interval_nonneg (start finish : ℝ) (ordered : start ≤ finish) :
    0 ≤ (aigMemoryCapacitorHeatAt technology entry memory assignment downstreamTechnology downstreamGraph
        clock code address finish).value -
      (aigMemoryCapacitorHeatAt technology entry memory assignment downstreamTechnology downstreamGraph
        clock code address start).value :=
  sub_nonneg.mpr (aigMemoryCapacitorHeatAt_monotone technology entry memory assignment
    downstreamTechnology downstreamGraph clock code address ordered)

end Storage
end
end Cells
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
