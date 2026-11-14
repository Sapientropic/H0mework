import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.HookSource
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.ChamberRecognize

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.EarlierSourceSearch.Eleven

/-- One original Black event enters the source-generated thirteen-ply family.
The whole successor certificate is supplied by its uniform source theorem. -/
def after31? (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  let material := BufferedReplay.restore (BufferedReplay.capture frame)
  have same : material = frame := BufferedReplay.restore_capture frame
  if owned : material.visible.toMove = .positive then
    match generated : nativeStep? (Law.positionalSuperko 0) material (.play (3, 1)) with
    | none => none
    | some raw =>
        let target := BufferedReplay.restore (BufferedReplay.capture raw)
        have targetSame : target = raw := BufferedReplay.restore_capture raw
        if source : HookSource.Source target then
          (HookSource.certificate? source).map (fun child =>
            let reply : ScoringReply material :=
              ⟨.play (3, 1), target, by simp, by rw [targetSame]; exact generated⟩
            same ▸ .choose owned reply (child.weaken (-345) (by decide)))
        else none
  else none

end SaturationMonoid.ProcessGame.Go.CriticalKomi.EarlierSourceSearch.Eleven
