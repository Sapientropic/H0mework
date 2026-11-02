import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Residual
set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Residual.Joint
open Institutions.Capitalism.Universal.Source.Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)
structure Frame where
  state : State code
  programs : List (Schedule code)
variable (frames : List (Frame code))
def keys : List (Key code) := (frames.flatMap fun frame => Residual.keys code frame.state frame.programs).dedup
abbrev Table := ∀ key ∈ keys code frames,Move code
def tables : List (Table code frames) := List.pi (keys code frames) (fun _ => moves code)
def respond (table : Table code frames) : Opponent code := fun history past frame =>
  if member : (history,past,frame) ∈ keys code frames then table _ member else none
def restrict (rival : Opponent code) : Table code frames := fun key _ => rival key.1 key.2.1 key.2.2

theorem restriction_is_generated (rival : Opponent code) : restrict code frames rival ∈ tables code frames := by
  apply (List.mem_pi _ _).mpr
  intro _ _
  exact every_move_is_generated code _
theorem frame_keys_are_included (frame : Frame code) (member : frame ∈ frames) :
    ∀ key ∈ Residual.keys code frame.state frame.programs,key ∈ keys code frames := by
  intro key inside
  exact List.mem_dedup.mpr (List.mem_flatMap.mpr ⟨frame,member,inside⟩)
theorem restriction_agrees (rival : Opponent code) (state : State code)
    (inside : Residual.key code state ∈ keys code frames) :
    respond code frames (restrict code frames rival) state.history state.past state.frame =
      rival state.history state.past state.frame := by
  dsimp only [Residual.key] at inside
  simp only [respond,dif_pos inside,restrict]
theorem one_table_preserves_each_full_run (frame : Frame code) (member : frame ∈ frames)
    (schedule : Schedule code) (generated : schedule ∈ frame.programs)
    (input : Input code) (n : Nat) (bounded : n ≤ frame.state.remaining) :
    run code schedule ⟨respond code frames (restrict code frames input.opponent),input.budget⟩ frame.state n =
      run code schedule input frame.state n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [run]
      rw [ih (by omega),advance_is_its_actual_choice,advance_is_its_actual_choice code (schedule n) input]
      exact congrArg (fun move => forced code (schedule n) move (run code schedule input frame.state n))
        (restriction_agrees code frames input.opponent _ (frame_keys_are_included code frames frame member _
          (every_remaining_decision_is_generated code frame.state frame.programs schedule generated input n (by omega))))
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Residual.Joint
