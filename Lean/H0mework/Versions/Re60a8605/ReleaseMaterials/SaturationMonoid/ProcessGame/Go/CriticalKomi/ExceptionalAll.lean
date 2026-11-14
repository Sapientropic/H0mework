import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CoalitionBirth

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.ExceptionalAll

/-- Compile the legal successor of one designated event and a source-derived uniform response
to all other original events. This is a consumer of the supplied response
producer; it contributes no future guarantee as a source fact. -/
def certificateWithStep? (frame : Frame 19) (event : Move 19)
    (response : (move : Move 19) → (target : Frame 19) →
      move ≠ .resign → LegalStep (Law.positionalSuperko 0) frame move target →
      move ≠ event → Certificate .positive (-345) target)
    (exception : (target : Frame 19) → LegalStep (Law.positionalSuperko 0) frame event target →
      Option (Certificate .positive (-345) target)) :
    Option (Certificate .positive (-345) frame) :=
  if playing : frame.visible.status = .playing then
    if opponent : frame.visible.toMove ≠ .positive then
      let delayed : Thunk (List (Move 19 × Frame 19)) := ⟨fun _ => scoringExpansion frame⟩
      match generated : nativeStep? (Law.positionalSuperko 0) frame event with
      | none =>
          some (.all playing opponent (fun port =>
            let expansion := delayed.get
            let facts := mem_scoringExpansion_iff.mp (List.get_mem expansion port)
            response (expansion.get port).1 (expansion.get port).2 facts.2 facts.1 (by
              intro same
              have actual : nativeStep? (Law.positionalSuperko 0) frame event =
                  some (expansion.get port).2 := by simpa only [LegalStep, same] using facts.1
              rw [generated] at actual
              cases actual)))
      | some raw =>
          let target := BufferedReplay.restore (BufferedReplay.capture raw)
          have targetSame : target = raw := BufferedReplay.restore_capture raw
          have actual : nativeStep? (Law.positionalSuperko 0) frame event = some target := by
            rw [targetSame]
            exact generated
          (exception target actual).map (fun child =>
            .all playing opponent (fun port =>
              let expansion := delayed.get
              let facts := mem_scoringExpansion_iff.mp (List.get_mem expansion port)
              if hit : (expansion.get port).1 = event then
                have same : target = (expansion.get port).2 :=
                  Option.some.inj (actual.symm.trans (by simpa only [LegalStep, hit] using facts.1))
                same ▸ child
              else response (expansion.get port).1 (expansion.get port).2 facts.2 facts.1 hit))
    else none
  else none

def certificate? (frame : Frame 19) (event : Move 19)
    (response : (move : Move 19) → (target : Frame 19) →
      move ≠ .resign → LegalStep (Law.positionalSuperko 0) frame move target →
      move ≠ event → Certificate .positive (-345) target)
    (exception : (target : Frame 19) → Option (Certificate .positive (-345) target)) :
    Option (Certificate .positive (-345) frame) :=
  certificateWithStep? frame event response (fun target _ => exception target)

end SaturationMonoid.ProcessGame.Go.CriticalKomi.ExceptionalAll
