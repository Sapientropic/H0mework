import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositiveContinuation.Dyadic

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1PositiveContinuation
noncomputable section
open CPS1Deformation CPS1ElectronicSource CPS1PositivePulse
variable {frame : CPS1Recycling.Frame}

def trajectory (state : Material frame) (ready : PulseReady state) :
    Nat → { current : Material frame // PulseReady current } :=
  Nat.rec ⟨state,ready⟩ (fun _ current =>
    ⟨(renewingResult current.val current.property).1,renewing_ready current.val current.property⟩)

def timeAt (state : Material frame) (ready : PulseReady state) (depth : Nat) : ℝ :=
  renewingTime (trajectory state ready depth).val (trajectory state ready depth).property

def responseAt (state : Material frame) (ready : PulseReady state) (depth : Nat) :
    Material frame × ElectronicPulse :=
  renewingResult (trajectory state ready depth).val (trajectory state ready depth).property

theorem trajectory_zero (state : Material frame) (ready : PulseReady state) :
    (trajectory state ready 0).val = state := rfl

theorem trajectory_response (state : Material frame) (ready : PulseReady state) (depth : Nat) :
    (trajectory state ready (depth+1)).val = (responseAt state ready depth).1 := rfl

theorem trajectory_actual (state : Material frame) (ready : PulseReady state) (depth : Nat) :
    (trajectory state ready depth).val.pulse? (timeAt state ready depth) = .ok (responseAt state ready depth) :=
  renewing_actual _ _

theorem trajectory_ready (state : Material frame) (ready : PulseReady state) (depth : Nat) :
    PulseReady (trajectory state ready depth).val := (trajectory state ready depth).property

theorem trajectory_positive_time (state : Material frame) (ready : PulseReady state) (depth : Nat) :
    0 < timeAt state ready depth := renewing_time_positive _ _

theorem trajectory_paid (state : Material frame) (ready : PulseReady state) (depth : Nat) :
    (trajectory state ready depth).val.energy+(trajectory state ready depth).val.reserve =
      state.energy+state.reserve := by
  induction depth with
  | zero => rfl
  | succ depth previous =>
    rw [trajectory_response]
    exact (renewing_paid (trajectory state ready depth).val (trajectory state ready depth).property).2.trans previous

theorem trajectory_same_source (state : Material frame) (ready : PulseReady state) (depth : Nat) :
    (trajectory state ready depth).val.reference = state.reference := by
  induction depth with
  | zero => rfl
  | succ depth previous =>
    rw [trajectory_response]
    exact (pulse_same_source _ _ _ (trajectory_actual state ready depth)).1.trans previous

def elapsed (state : Material frame) (ready : PulseReady state) : Nat → ℝ :=
  Nat.rec 0 (fun depth previous => previous+timeAt state ready depth)

theorem elapsed_strict (state : Material frame) (ready : PulseReady state) (depth : Nat) :
    elapsed state ready depth < elapsed state ready (depth+1) := by
  change _ < _+timeAt state ready depth
  exact lt_add_of_pos_right _ (trajectory_positive_time state ready depth)

theorem elapsed_nonnegative (state : Material frame) (ready : PulseReady state) (depth : Nat) :
    0 ≤ elapsed state ready depth := by
  induction depth with
  | zero => exact le_rfl
  | succ depth previous => exact previous.trans (elapsed_strict state ready depth).le

theorem elapsed_positive (state : Material frame) (ready : PulseReady state) (depth : Nat) :
    0 < elapsed state ready (depth+1) :=
  (elapsed_nonnegative state ready depth).trans_lt (elapsed_strict state ready depth)

end
end CPS1PositiveContinuation
