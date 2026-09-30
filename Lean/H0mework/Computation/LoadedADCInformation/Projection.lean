import H0mework.Computation.LoadedADCInformation.Source

/-! Actual received feedback determines every future drive; its two-cycle does not identify the history. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

def driveAt (frame : Nat) : FiniteBinaryDrive :=
  (loadedAfter downstreamTechnology downstreamGraph seed frame).plant.val.drive

theorem drive_semiconj :
    Function.Semiconj (fun current : FiniteADCWholeJointCurrent hardware
      (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology => current.plant.val.drive)
      (loadedStep downstreamTechnology downstreamGraph)
      (fun drive channel => !(drive channel)) :=
  fun current => loadedStep_feedback downstreamTechnology downstreamGraph current

theorem drive_iterate (frame : Nat) :
    driveAt downstreamTechnology downstreamGraph seed frame =
      ((fun drive : FiniteBinaryDrive => fun channel => !(drive channel))^[frame]) seed.plant.val.drive :=
  (drive_semiconj downstreamTechnology downstreamGraph).iterate_right frame seed

theorem driveAt_next (frame : Nat) :
    driveAt downstreamTechnology downstreamGraph seed (frame + 1) =
      fun channel => !(driveAt downstreamTechnology downstreamGraph seed frame channel) := by
  unfold driveAt
  rw [loadedAfter_succ, loadedStep_feedback]

theorem driveAt_two (frame : Nat) :
    driveAt downstreamTechnology downstreamGraph seed (frame + 2) =
      driveAt downstreamTechnology downstreamGraph seed frame := by
  rw [show frame + 2 = (frame + 1) + 1 by omega, driveAt_next, driveAt_next]
  funext channel
  exact Bool.not_not _

theorem driveAt_distinct (frame : Nat) :
    driveAt downstreamTechnology downstreamGraph seed (frame + 1) ≠
      driveAt downstreamTechnology downstreamGraph seed frame := by
  rw [driveAt_next]
  intro same
  have read := congrFun same Physical.Interface.FiniteEmbodimentChannel.sourceBound
  exact (Bool.not_eq_self _).mp read

theorem drive_future_iff (left right : Nat) :
    (∀ depth, driveAt downstreamTechnology downstreamGraph seed (left + depth) =
      driveAt downstreamTechnology downstreamGraph seed (right + depth)) ↔
        driveAt downstreamTechnology downstreamGraph seed left =
          driveAt downstreamTechnology downstreamGraph seed right := by
  constructor
  · intro same
    simpa using same 0
  · intro same depth
    induction depth with
    | zero => simpa using same
    | succ depth induction =>
        rw [← Nat.add_assoc, ← Nat.add_assoc, driveAt_next, driveAt_next, induction]

theorem no_drive_time_decoder :
    ¬ ∃ decoder : FiniteBinaryDrive → ℝ, ∀ frame,
      decoder (driveAt downstreamTechnology downstreamGraph seed frame) =
        loadedElapsed downstreamTechnology downstreamGraph seed frame := by
  rintro ⟨decoder, recovers⟩
  have same := (recovers 0).symm.trans ((congrArg decoder
    (driveAt_two downstreamTechnology downstreamGraph seed 0)).symm.trans (recovers 2))
  exact (loadedElapsed_strictMono downstreamTechnology downstreamGraph seed (by decide : 0 < 2)).ne same

theorem drive_repetition_retains_distinct_material (frame : Nat) :
    driveAt downstreamTechnology downstreamGraph seed (frame + 2) =
        driveAt downstreamTechnology downstreamGraph seed frame ∧
      loadedExposure downstreamTechnology downstreamGraph seed (frame + 2) ≠
        loadedExposure downstreamTechnology downstreamGraph seed frame := by
  exact ⟨driveAt_two downstreamTechnology downstreamGraph seed frame,
    fun same => (by omega : frame + 2 ≠ frame)
      (exposure_injective downstreamTechnology downstreamGraph seed same)⟩

end
end FiniteADCWholeJointCurrent.Information
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
