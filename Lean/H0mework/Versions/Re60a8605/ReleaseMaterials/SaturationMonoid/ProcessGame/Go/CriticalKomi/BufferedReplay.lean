import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.HistoryKernel
import Mathlib.Data.List.GetD

/-! Materialized source replay with exact restoration to the original rule/history carrier. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.BufferedReplay

/-- Materialized matrix storage between original native rule steps. -/
structure Buffer (n : Nat) where
  signature : BoardSignature n
  toMove : Polarity
  consecutivePasses : Nat
  status : Status
  positionHistory : List (Situation n)

def signatureBoard {n : Nat} (signature : BoardSignature n) : Board n :=
  fun point => (signature.getD point.1.val []).getD point.2.val none

theorem signatureBoard_boardSignature {n : Nat} (board : Board n) :
    signatureBoard (boardSignature board) = board := by
  funext point
  unfold signatureBoard boardSignature
  rw [List.getD_eq_getElem _ [] (by simp)]
  simp only [List.getElem_ofFn]
  rw [List.getD_eq_getElem _ none (by simp)]
  simp only [List.getElem_ofFn]

def restore {n : Nat} (buffer : Buffer n) : Frame n where
  visible := {
    board := signatureBoard buffer.signature
    toMove := buffer.toMove
    consecutivePasses := buffer.consecutivePasses
    status := buffer.status
  }
  positionHistory := buffer.positionHistory

/-- Keep matrix materialization at the step boundary instead of fusing it
back into repeated point reads of the preceding function-valued board. -/
@[noinline] def capture {n : Nat} (frame : Frame n) : Buffer n where
  signature := boardSignature frame.visible.board
  toMove := frame.visible.toMove
  consecutivePasses := frame.visible.consecutivePasses
  status := frame.visible.status
  positionHistory := frame.positionHistory

@[simp] theorem restore_capture {n : Nat} (frame : Frame n) :
    restore (capture frame) = frame := by
  change Frame.mk (restore (capture frame)).visible frame.positionHistory =
    Frame.mk frame.visible frame.positionHistory
  apply congrArg (fun visible => Frame.mk visible frame.positionHistory)
  apply VisiblePosition.ext
  · exact signatureBoard_boardSignature frame.visible.board
  · rfl
  · rfl
  · rfl

private def generateFrom? {n : Nat} (law : Law) (buffer : Buffer n) :
    (moves : List (Move n)) → Option (GeneratedReplay law (restore buffer) moves)
  | [] => some (.nil (restore buffer))
  | move :: moves =>
      match generated : nativeStep? law (restore buffer) move with
      | none => none
      | some next =>
          let nextBuffer := capture next
          match generateFrom? law nextBuffer moves with
          | none => none
          | some tail =>
              some (.cons move (by
                change nativeStep? law (restore buffer) move = some (restore nextBuffer)
                rw [show restore nextBuffer = next from restore_capture next]
                exact generated) tail)

/-- The public result retains the original initial frame, native legal-step
proofs, exact position history and original occurrence projection. -/
def generate? (law : Law) (n : Nat) (moves : List (Move n)) :
    Option (GeneratedReplay law (Frame.initial n) moves) :=
  (generateFrom? law (capture (Frame.initial n)) moves).map
    (fun replay => (restore_capture (Frame.initial n)) ▸ replay)

end SaturationMonoid.ProcessGame.Go.CriticalKomi.BufferedReplay
