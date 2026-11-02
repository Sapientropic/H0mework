import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Trace

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Evolution.Native

private def join {first middle last : Packet} {entry : ChallengeCohort first.1.scope}
    (earlier : ChallengeTransport entry middle)
    (later : (entry : ChallengeCohort middle.1.scope) → entry ∈ middle.2.pastChallenges → ChallengeTransport entry last) :
    ChallengeTransport entry last :=
  let final := later earlier.row earlier.member
  ⟨final.saved,final.later,final.member,.append earlier.extension final.extension⟩

def challenge : {first last : Packet} → (trace : Evolution first last) →
    (entry : ChallengeCohort first.1.scope) → entry ∈ first.2.pastChallenges → ChallengeTransport entry last
  | _,_,.same _,entry,member => ⟨entry.saved,entry.later,member,.same entry.saved⟩
  | _,_,.submit saved word,entry,member =>
      ⟨entry.saved.consume (boundarySource _ (saved.inputs ++ [word])) entry.later (World.receipts saved word),
        entry.later,List.mem_map.mpr ⟨entry,member,rfl⟩,.consume ..⟩
  | _,_,.handoff saved fresh,entry,member =>
      ⟨entry.saved.consume (Handoff.Challenge.occurrence fresh)
        (lt_of_lt_of_le entry.later (World.window_follows saved fresh)) (World.nextReceipts saved fresh),
        lt_of_lt_of_le entry.later (World.window_follows saved fresh),
        List.mem_append_left _ (List.mem_map.mpr ⟨entry,member,rfl⟩),.consume ..⟩
  | _,_,.handoffAt saved fresh actualInputs,entry,member =>
      ⟨entry.saved.consume (World.openingBoundary saved fresh actualInputs)
        (lt_of_lt_of_le entry.later (World.window_follows saved fresh))
        (World.openingReceipts saved fresh actualInputs),
        lt_of_lt_of_le entry.later (World.window_follows saved fresh),
        List.mem_append_left _ (List.mem_map.mpr ⟨entry,member,rfl⟩),.consume ..⟩
  | _,_,.append earlier later,entry,member =>
      join (challenge earlier entry member) (challenge later)

theorem challenge_exact {first last : Packet} (trace : Evolution first last)
    (entry : ChallengeCohort first.1.scope) (member : entry ∈ first.2.pastChallenges) :
    challenge trace entry member = trace.challenge entry member := by
  induction trace with
  | same => rfl
  | submit => rfl
  | handoff => rfl
  | handoffAt => rfl
  | append earlier later first second =>
      change join (challenge earlier entry member) (challenge later) =
        join (earlier.challenge entry member) (Evolution.challenge later)
      have last : challenge later = Evolution.challenge later := by
        funext entry member
        exact second entry member
      rw [first,last]

@[csimp] theorem challenge_codegen : @Evolution.challenge = @challenge := by
  funext first last trace entry member
  exact (challenge_exact trace entry member).symm

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Evolution.Native
