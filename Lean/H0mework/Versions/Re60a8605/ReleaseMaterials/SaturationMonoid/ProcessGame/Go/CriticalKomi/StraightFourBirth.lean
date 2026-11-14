import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CapturingBirth

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.StraightFourBirth

def core : Finset (Point 19) := {(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (0, 4)}
def room : Finset (Point 19) := {(0, 0), (0, 1), (0, 2), (0, 3)}

/-- A present-board stencil; full legality and PSK are still read from the original frame. -/
def Source (frame : Frame 19) : Prop :=
  frame.visible.status = .playing ∧ frame.visible.toMove = .negative ∧
  frame.visible.consecutivePasses = 0 ∧
  (∀ point ∈ core, frame.visible.board point = some .positive) ∧
  (∀ point ∈ ({(0, 1), (0, 2)} : Finset (Point 19)), frame.visible.board point = none) ∧
  (∀ point ∈ ({(0, 0), (0, 3)} : Finset (Point 19)),
    frame.visible.board point = none ∨ frame.visible.board point = some .negative)

instance (frame : Frame 19) : Decidable (Source frame) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

private def collect? : (count : Nat) → (family : Fin count → Type) →
    ((index : Fin count) → Option (family index)) → Option ((index : Fin count) → family index)
  | 0, _, _ => some (fun index => Fin.elim0 index)
  | count + 1, family, read => do
      let first ← read 0
      let rest ← collect? count (fun index => family index.succ) (fun index => read index.succ)
      -- Fin.cases uses induction and would recompute preceding continuations.
      pure (fun index => match index with
        | ⟨0, _⟩ => first
        | ⟨later + 1, bound⟩ => rest ⟨later, Nat.lt_of_succ_lt_succ bound⟩)

private def reply? (frame : Frame 19) (point : Point 19) : Option (ScoringReply frame) :=
  match generated : nativeStep? (Law.positionalSuperko 0) frame (.play point) with
  | none => none
  | some target => some ⟨.play point, target, by simp, generated⟩

def miaiAt? (frame : Frame 19) (left right : Point 19) : Option (Certificate .positive (-341) frame) :=
  if playing : frame.visible.status = .playing then
    if opponent : frame.visible.toMove = Polarity.positive.other then
      if passes : frame.visible.consecutivePasses = 0 then
        let seen := CoalitionBirth.retained frame .positive
        (CoalitionBirth.candidate? frame .positive (-341) seen left).bind (fun first =>
          (CoalitionBirth.candidate? frame .positive (-341) seen right).bind (fun second =>
            if distinct : first.plan.point ≠ second.plan.point then
              if savedFirst : CoalitionBirth.SavedCore first.plan then
                if savedSecond : CoalitionBirth.SavedCore second.plan then
                  some (CoalitionBirth.miaiCertificate seen (CoalitionBirth.retained_tracked frame .positive)
                    first.plan second.plan distinct savedFirst savedSecond first.virgin second.virgin
                    playing opponent passes (-341) first.accepted second.accepted)
                else none
              else none
            else none))
      else none
    else none
  else none

/-- The response is selected only after observing the actual White event. -/
def replyPoint (observed : Move 19) : Point 19 :=
  if observed = .play (0, 1) ∨ observed = .play (0, 3) then (0, 2) else (0, 1)

def continuation? (frame : Frame 19) (observed : Move 19) : Option (Certificate .positive (-341) frame) :=
  -- An occupied endpoint can be captured by the first reply. The actual
  -- resulting board decides whether the next program is capture or miai.
  if observed = .play (0, 1) then
    CapturingBirth.recognizeAt? frame .positive (-341) (0, 0) <|> miaiAt? frame (0, 0) (0, 1)
  else if observed = .play (0, 2) then
    CapturingBirth.recognizeAt? frame .positive (-341) (0, 3) <|> miaiAt? frame (0, 2) (0, 3)
  else if observed = .play (0, 3) then
    miaiAt? frame (0, 0) (0, 1) <|> CapturingBirth.recognizeAt? frame .positive (-341) (0, 1)
  else
    miaiAt? frame (0, 2) (0, 3) <|> CapturingBirth.recognizeAt? frame .positive (-341) (0, 2)

@[noinline] def response? (frame : Frame 19) (observed : Move 19) : Option (Certificate .positive (-341) frame) :=
  let material := BufferedReplay.restore (BufferedReplay.capture frame)
  have same : material = frame := BufferedReplay.restore_capture frame
  if owned : material.visible.toMove = .positive then
    (reply? material (replyPoint observed)).bind (fun reply =>
      let target := BufferedReplay.restore (BufferedReplay.capture reply.target)
      have targetSame : target = reply.target := BufferedReplay.restore_capture reply.target
      let retained : ScoringReply material :=
        ⟨reply.move, target, reply.notResign, by rw [targetSame]; exact reply.step⟩
      (continuation? target observed).map (fun child => same ▸ .choose owned retained child))
  else none

/-- Evaluate the first original AND layer once, retaining each generated
continuation. No supplied port coverage or future choice enters the source. -/
@[noinline] def certificate? (frame : Frame 19) : Option (Certificate .positive (-341) frame) :=
  if source : Source frame then
    let expansion := scoringExpansion frame
    (collect? expansion.length (fun port => Certificate .positive (-341) (expansion.get port).2)
      (fun port => response? (expansion.get port).2 (expansion.get port).1)).map
      (fun children => .all source.1 (by rw [source.2.1]; decide) children)
  else none

/-- Pull the generated opponent closure through its actual native sealing move. -/
def seal? (frame : Frame 19) : Option (Certificate .positive (-341) frame) :=
  if owned : frame.visible.toMove = .positive then
    if ∀ point ∈ core, point ≠ (0, 4) → frame.visible.board point = some .positive then
      let material := BufferedReplay.restore (BufferedReplay.capture frame)
      have same : material = frame := BufferedReplay.restore_capture frame
      have materialOwned : material.visible.toMove = .positive := by rw [same]; exact owned
      (reply? material (0, 4)).bind (fun reply =>
        let target := BufferedReplay.restore (BufferedReplay.capture reply.target)
        have targetSame : target = reply.target := BufferedReplay.restore_capture reply.target
        -- The choice itself carries the materialized target; downstream
        -- dependent readers must not reconstruct it from the raw board closure.
        let retained : ScoringReply material :=
          ⟨reply.move, target, reply.notResign, by rw [targetSame]; exact reply.step⟩
        (certificate? target).map (fun child => same ▸ .choose materialOwned retained child))
    else none
  else none

def recognize? (frame : Frame 19) : Option (Certificate .positive (-341) frame) :=
  certificate? frame <|> seal? frame

end SaturationMonoid.ProcessGame.Go.CriticalKomi.StraightFourBirth
