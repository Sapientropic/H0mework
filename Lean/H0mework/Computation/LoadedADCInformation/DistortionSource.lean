import H0mework.Computation.LoadedADCInformation.ConditionalActionConsumer

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Distortion

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

noncomputable section

def phase (frame : Nat) : Fin 2 := ⟨frame % 2, Nat.mod_lt _ (by decide)⟩

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

theorem drive_even_shift (first repeats : Nat) :
    driveAt downstreamTechnology downstreamGraph seed (first + 2 * repeats) =
      driveAt downstreamTechnology downstreamGraph seed first := by
  induction repeats with
  | zero => simp
  | succ repeats previous =>
      rw [Nat.mul_succ, ← Nat.add_assoc, driveAt_two, previous]

theorem drive_phase (frame : Nat) :
    driveAt downstreamTechnology downstreamGraph seed frame =
      driveAt downstreamTechnology downstreamGraph seed (phase frame).val := by
  have generated := drive_even_shift downstreamTechnology downstreamGraph seed (frame % 2) (frame / 2)
  rw [Nat.mod_add_div] at generated
  exact generated

theorem phase_drive_injective :
    Function.Injective (fun side : Fin 2 => driveAt downstreamTechnology downstreamGraph seed side.val) := by
  intro left right same
  fin_cases left <;> fin_cases right
  · rfl
  · exact False.elim ((driveAt_distinct downstreamTechnology downstreamGraph seed 0) same.symm)
  · exact False.elim ((driveAt_distinct downstreamTechnology downstreamGraph seed 0) same)
  · rfl

theorem drive_fibre (left right : Nat) :
    driveAt downstreamTechnology downstreamGraph seed left = driveAt downstreamTechnology downstreamGraph seed right ↔
      phase left = phase right := by
  rw [drive_phase downstreamTechnology downstreamGraph seed left,
    drive_phase downstreamTechnology downstreamGraph seed right]
  exact (phase_drive_injective downstreamTechnology downstreamGraph seed).eq_iff

theorem query_fibre (bound : Nat) (left right : Fin (bound + 1)) :
    query downstreamTechnology downstreamGraph seed bound left = query downstreamTechnology downstreamGraph seed bound right ↔
      phase left.val = phase right.val :=
  drive_fibre downstreamTechnology downstreamGraph seed left.val right.val

theorem complete_future_fibre (left right : Nat) :
    (∀ future, driveAt downstreamTechnology downstreamGraph seed (left + future) =
      driveAt downstreamTechnology downstreamGraph seed (right + future)) ↔ phase left = phase right :=
  (drive_future_iff downstreamTechnology downstreamGraph seed left right).trans
    (drive_fibre downstreamTechnology downstreamGraph seed left right)

theorem original_weight (bound : Nat) (actor : Fin (bound + 1)) :
    (historyPMF bound actor).toReal = 1 / (bound + 1 : ℝ) := history_weight bound actor

def tick : ℝ :=
  (finiteSamplingClockTickPeriod hardware.meteredSource.fixture.coreSource hardware.clockCode).value

theorem tick_pos : 0 < tick (hardware := hardware) :=
  finiteSamplingClockTickPeriod_pos hardware.meteredSource.fixture.coreSource hardware.clockCode

theorem charge_ge_tick (frame : Nat) :
    tick (hardware := hardware) ≤ charge downstreamTechnology downstreamGraph
      (loadedAfter downstreamTechnology downstreamGraph seed frame) :=
  loadedStepDuration_ge_tick downstreamTechnology downstreamGraph _

end
end FiniteADCWholeJointCurrent.Information.Distortion
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
