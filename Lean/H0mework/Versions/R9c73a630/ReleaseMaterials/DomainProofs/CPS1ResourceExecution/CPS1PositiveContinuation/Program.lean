import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositiveContinuation.Trajectory
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Source

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1PositiveContinuation.NativeSource
noncomputable section
open CPS1Deformation CPS1Deformation.Source CPS1PositivePulse
variable {frame : CPS1Recycling.Frame}

def rawBlock (state : Material frame) (ready : PulseReady state) (start : Nat) : Nat → List RawAction :=
  fun depth =>
    Nat.rec (motive := fun _ => Nat → List RawAction)
      (fun _ => [])
      (fun _ previous current => .pulse (timeAt state ready current) :: previous (current+1))
      depth start

def reactionBlock (state : Material frame) (ready : PulseReady state) (start : Nat) :
    Nat → List (Reaction frame) :=
  fun depth =>
    Nat.rec (motive := fun _ => Nat → List (Reaction frame))
      (fun _ => [])
      (fun _ previous current =>
        .pulse (trajectory state ready current).val (timeAt state ready current) :: previous (current+1))
      depth start


theorem raw_block_length (state : Material frame) (ready : PulseReady state) (start depth : Nat) :
    (rawBlock state ready start depth).length = depth := by
  induction depth generalizing start with
  | zero => rfl
  | succ depth previous =>
    change (rawBlock state ready (start+1) depth).length + 1 = depth + 1
    exact congrArg (fun count => count+1) (previous (start+1))

theorem reaction_block_length (state : Material frame) (ready : PulseReady state) (start depth : Nat) :
    (reactionBlock state ready start depth).length = depth := by
  induction depth generalizing start with
  | zero => rfl
  | succ depth previous =>
    change (reactionBlock state ready (start+1) depth).length + 1 = depth + 1
    exact congrArg (fun count => count+1) (previous (start+1))


theorem program_block (state : Material frame) (ready : PulseReady state)
    (start depth : Nat) (pending : List RawAction) :
    CPS1Deformation.Source.program frame (some (.deformed (trajectory state ready start).val))
      (rawBlock state ready start depth ++ pending) =
        reactionBlock state ready start depth ++
          CPS1Deformation.Source.program frame
            (some (.deformed (trajectory state ready (start+depth)).val)) pending := by
  induction depth generalizing start with
  | zero => rfl
  | succ depth previous =>
    change (RawAction.pulse (timeAt state ready start)).reaction frame
      (some (.deformed (trajectory state ready start).val)) ::
        CPS1Deformation.Source.program frame
          ((RawAction.pulse (timeAt state ready start)).next frame
            (some (.deformed (trajectory state ready start).val)))
          (rawBlock state ready (start+1) depth ++ pending) = _
    simp only [RawAction.reaction,RawAction.next,trajectory_actual]
    rw [← trajectory_response]
    rw [previous]
    simp only [reactionBlock,List.cons_append,Nat.add_comm,Nat.add_left_comm]

end
end CPS1PositiveContinuation.NativeSource
