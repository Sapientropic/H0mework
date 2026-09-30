import H0mework.Physics.ConductanceCell.AIGMemoryEnergy
import H0mework.Computation.AIGHold.LeakyHoldWork

/-! # Every stored capacitor is the exact raw or isolated restriction of the existing memory run -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Storage

open Std.Sat Units.Interface Conductance
open Netlist.Dissipative.Dimensioned.Driven.Producer

variable {α β : Type} [DecidableEq α] [Hashable α] [DecidableEq β] [Hashable β] {width : Nat}

noncomputable section

def aigMemoryCaptureTime (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode) : SISecond :=
  aigInputSampledTime technology (aigOutputBank entry).aig
    (packetLineReadyTime technology (aigOutputBank entry).aig).value clock code

theorem aigMemoryCaptureTime_nonneg (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode) :
    0 ≤ (aigMemoryCaptureTime technology entry clock code).value := by
  change 0 ≤ (finiteSamplingClockTickCount clock code _ : ℝ) *
    (finiteSamplingClockTickPeriod clock code).value
  exact mul_nonneg (Nat.cast_nonneg _) (finiteSamplingClockTickPeriod_pos clock code).le

/-- This is the existing state compiler's branch test, not a new source selector. -/
def aigMemoryCapacitorIsHeld (entry : AIG.RefVecEntry α width)
    (address : AIGCapacitorAddress (aigOutputBank entry).aig) : Prop :=
  entry.aig.decls.size ≤ address.val.1.val ∧ address.val.2 = false

instance (entry : AIG.RefVecEntry α width) (address : AIGCapacitorAddress (aigOutputBank entry).aig) :
    Decidable (aigMemoryCapacitorIsHeld entry address) := inferInstanceAs (Decidable (_ ∧ _))

variable (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
  (memory : AIGCapacitorMemory technology (aigOutputBank entry).aig) (assignment : α → Bool)
  (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
  (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)

/-- No voltage is generated here: both branches project the original compiler occurrence. -/
theorem aigMemoryCapacitor_actual_restriction
    (address : AIGCapacitorAddress (aigOutputBank entry).aig) (time : ℝ) :
    let raw := aigCapacitorVoltageAt technology (aigOutputBank entry).aig
      (aigMemoryInputWave technology entry memory assignment) memory.gateInitial address
    let hold := compileHoldLeaseForGraph
      (compileDualRailCell technology (aigOutputBank entry).aig address.val.1 address.val.2)
      downstreamTechnology downstreamGraph clock code
    aigMemoryStateAt technology entry memory assignment downstreamTechnology downstreamGraph clock code
      address.val.1 address.val.2 time =
      if aigMemoryCapacitorIsHeld entry address then
        hold.wave raw (aigMemoryCaptureTime technology entry clock code).value time
      else raw time := by
  dsimp only
  by_cases held : aigMemoryCapacitorIsHeld entry address
  · rw [if_pos held]
    change entry.aig.decls.size ≤ address.val.1.val ∧ address.val.2 = false at held
    rw [aigMemoryStateAt, aigHeldBankStateAt, dif_pos held]
    let index : Fin width := ⟨address.val.1.val - entry.aig.decls.size, by
      have bound := address.val.1.isLt
      have size := aigOutputBank_size entry
      omega⟩
    have sameNode : (⟨((aigOutputBank entry).vec.get index.val index.isLt).gate,
        ((aigOutputBank entry).vec.get index.val index.isLt).hgate⟩ : Fin (aigOutputBank entry).aig.decls.size) =
        address.val.1 := by
      apply Fin.ext
      dsimp only
      rw [aigOutputBank_ref_gate]
      dsimp only [index]
      omega
    change aigBankHoldWave technology entry _ memory.gateInitial downstreamTechnology downstreamGraph
      (packetLineReadyTime technology (aigOutputBank entry).aig).value clock code index time = _
    unfold aigBankHoldWave aigBankCell aigBankVoltage
    rw [sameNode, ← held.2]
    rfl
  · rw [if_neg held]
    exact dif_neg held

end
end Cells.Storage
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
