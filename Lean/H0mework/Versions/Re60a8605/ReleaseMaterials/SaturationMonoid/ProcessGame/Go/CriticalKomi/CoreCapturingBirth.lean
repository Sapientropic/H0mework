import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.RetainedCoreHistory
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CapturingBirth

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.CoreCapturingBirth

def afterOpponent {n : Nat} {frame target : Frame n} {colour : Polarity} {move : Move n}
    (plan : CapturingBirth.Plan frame.visible.board colour)
    (fresh : CoreHistory.Fresh frame colour plan.geometry.core)
    (opponent : frame.visible.toMove = colour.other) (passes : frame.visible.consecutivePasses = 0)
    (scoring : move ≠ .resign) (step : LegalStep (Law.positionalSuperko 0) frame move target)
    (threshold : Int) (accepted : acceptsMargin colour threshold (EyeCoalition.bound plan.geometry colour) = true) :
    Certificate colour threshold target :=
  let material := BufferedReplay.restore (BufferedReplay.capture target)
  have same : material = target := BufferedReplay.restore_capture target
  have native : LegalStep (Law.positionalSuperko 0) frame move material := by rw [same]; exact step
  let ready := CapturingBirth.afterOpponent_ready plan opponent passes scoring native
  have retained : CoreHistory.Fresh material colour plan.geometry.core :=
    CoreHistory.step fresh native ⟨plan.point, plan.participates, by rw [ready.2.2.1]; simp⟩
  have legal : stoneHasLiberty (boardAfterPlay material.visible.board colour plan.point) plan.point := by
    have reserve := EyeCoalition.reserve ready.2.2.2 plan.participates
    obtain ⟨liberty, member⟩ := Finset.card_pos.mp
      (show 0 < (LibertyReserve.liberties (boardAfterPlay material.visible.board colour plan.point)
        plan.point).card from by omega)
    obtain ⟨⟨stone, groupMember, adjacent⟩, empty⟩ := LibertyReserve.mem_liberties.mp member
    exact ⟨stone, groupMember, liberty, adjacent, empty⟩
  let reply := CoreHistory.reply material colour plan.geometry.core retained plan.point
    ready.1 ready.2.1 ready.2.2.1 ready.2.2.2.1 legal
  let certificate : Certificate colour threshold material :=
    .choose ready.2.1 reply (.eyeCoalition ⟨plan.geometry, ready.2.2.2⟩ (.inl rfl) accepted)
  same ▸ certificate

def certificate {n : Nat} {frame : Frame n} {colour : Polarity}
    (plan : CapturingBirth.Plan frame.visible.board colour)
    (fresh : CoreHistory.Fresh frame colour plan.geometry.core)
    (playing : frame.visible.status = .playing) (opponent : frame.visible.toMove = colour.other)
    (passes : frame.visible.consecutivePasses = 0) (threshold : Int)
    (accepted : acceptsMargin colour threshold (EyeCoalition.bound plan.geometry colour) = true) :
    Certificate colour threshold frame :=
  let delayed : Thunk (List (Move n × Frame n)) := ⟨fun _ => scoringExpansion frame⟩
  .all playing (by rw [opponent]; exact Polarity.other_ne colour) (fun port =>
    let expansion := delayed.get
    have native := mem_scoringExpansion_iff.mp (List.get_mem expansion port)
    afterOpponent plan fresh opponent passes native.2 native.1 threshold accepted)

def recognizeAt? {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int)
    (point : Point n) : Option (Certificate colour threshold frame) :=
  if playing : frame.visible.status = .playing then
    if opponent : frame.visible.toMove = colour.other then
      if passes : frame.visible.consecutivePasses = 0 then
        (CapturingBirth.plan? frame.visible.board colour point).bind (fun plan =>
          if retained : CoreHistory.covered (CoreHistory.retain colour frame.positionHistory) plan.geometry.core = false then
            have fresh : CoreHistory.Fresh frame colour plan.geometry.core :=
              (CoreHistory.fresh_iff_retained frame colour plan.geometry.core).mpr retained
            if accepted : acceptsMargin colour threshold (EyeCoalition.bound plan.geometry colour) = true then
              some (certificate plan fresh playing opponent passes threshold accepted)
            else none
          else none)
      else none
    else none
  else none

def recognize? {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int) :
    Option (Certificate colour threshold frame) :=
  if frame.visible.status = .playing ∧ frame.visible.toMove = colour.other ∧
      frame.visible.consecutivePasses = 0 then
    (CapturingBirth.candidatePoints frame.visible.board colour).findSome?
      (recognizeAt? frame colour threshold)
  else none

end SaturationMonoid.ProcessGame.Go.CriticalKomi.CoreCapturingBirth
