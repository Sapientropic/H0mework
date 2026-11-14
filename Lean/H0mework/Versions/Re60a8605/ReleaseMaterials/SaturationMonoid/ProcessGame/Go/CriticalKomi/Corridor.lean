import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.StraightFourBirth
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalChambers
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalBirth
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalBirthCapturing
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.ExceptionalAll
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CorridorSource
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CorridorContinuation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CorridorPreparation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.Corridor

attribute [local instance 2000] Finset.decidableDforallFinset Finset.decidableDExistsFinset

def leaf? (g : VitalChambers.Geometry 19) (frame : Frame 19) :
    Option (Certificate .positive (-345) frame) :=
  if playing : frame.visible.status = .playing then
    if holds : VitalChambers.Holds g .positive frame.visible.board then
      if accepted : acceptsMargin .positive (-345) (VitalChambers.bound g .positive) = true then
        some (.vitalChambers ⟨g, holds⟩ (.inl playing) accepted)
      else none
    else none
  else none

def collect? : (count : Nat) → (family : Fin count → Type) →
    ((index : Fin count) → Option (family index)) → Option ((index : Fin count) → family index)
  | 0, _, _ => some (fun index => Fin.elim0 index)
  | count + 1, family, read => do
      let first ← read 0
      let rest ← collect? count (fun index => family index.succ) (fun index => read index.succ)
      pure (fun index => match index with
        | ⟨0, _⟩ => first
        | ⟨later + 1, bound⟩ => rest ⟨later, Nat.lt_of_succ_lt_succ bound⟩)

/-- Each retained child belongs to the actual native port that generated it. -/
def all? (frame : Frame 19)
    (read : (observed : Move 19) → (target : Frame 19) → Option (Certificate .positive (-345) target)) :
    Option (Certificate .positive (-345) frame) :=
  if playing : frame.visible.status = .playing then
    if opponent : frame.visible.toMove ≠ .positive then
      let expansion := scoringExpansion frame
      (collect? expansion.length (fun port => Certificate .positive (-345) (expansion.get port).2)
        (fun port => read (expansion.get port).1 (expansion.get port).2)).map
        (fun children => .all playing opponent children)
    else none
  else none

def choose? (frame : Frame 19) (played : Point 19)
    (read : (target : Frame 19) → Option (Certificate .positive (-345) target)) :
    Option (Certificate .positive (-345) frame) :=
  let material := BufferedReplay.restore (BufferedReplay.capture frame)
  have same : material = frame := BufferedReplay.restore_capture frame
  if owned : material.visible.toMove = .positive then
    match generated : nativeStep? (Law.positionalSuperko 0) material (.play played) with
    | none => none
    | some raw =>
        let target := BufferedReplay.restore (BufferedReplay.capture raw)
        have targetSame : target = raw := BufferedReplay.restore_capture raw
        let reply : ScoringReply material :=
          ⟨.play played, target, by simp, by rw [targetSame]; exact generated⟩
        (read target).map (fun child => same ▸ .choose owned reply child)
  else none

/-- The geometry and the old stones' liberties are paid once at the source;
the opponent's actual event generates the required capture or empty-room reply. -/
def sealAgainstOthersWithStep? (frame : Frame 19) (played : Point 19) (geometry : VitalChambers.Geometry 19)
    (exception : (target : Frame 19) → LegalStep (Law.positionalSuperko 0) frame (.play played) target →
      Option (Certificate .positive (-345) target)) :
    Option (Certificate .positive (-345) frame) :=
  if opponent : frame.visible.toMove = Polarity.positive.other then
    if passes : frame.visible.consecutivePasses = 0 then
      let seen := CoalitionBirth.retained frame .positive
      (VitalBirthCapturing.candidate? frame .positive (-345) seen played geometry).bind (fun candidate =>
        if same : candidate.plan.point = played then
          if saved : VitalBirthCapturing.SavedCore candidate.plan then
            ExceptionalAll.certificateWithStep? frame (.play played)
              (fun _move _target scoring step avoided =>
                VitalBirthCapturing.afterOpponent seen (CoalitionBirth.retained_tracked frame .positive)
                  candidate.plan saved candidate.virgin opponent passes scoring step
                  (by simpa only [same] using avoided) (-345) candidate.accepted)
              exception
          else none
        else none)
    else none
  else none

def sealAgainstOthers? (frame : Frame 19) (played : Point 19) (geometry : VitalChambers.Geometry 19)
    (exception : (target : Frame 19) → Option (Certificate .positive (-345) target)) :
    Option (Certificate .positive (-345) frame) :=
  sealAgainstOthersWithStep? frame played geometry (fun target _ => exception target)

/-- The original eighteenth column is the only boundary exit. Every other
White event seals immediately; only occupation of the current seal recurses. -/
def fromSource? {j divider : Nat} {frame : Frame 19} (source : Source frame j divider) :
    Option (Certificate .positive (-345) frame) :=
  match generated : sealedGeometry? j divider with
  | none => none
  | some geometry =>
      if edge : j = 18 then
        have sourceAtEdge : Source frame 18 divider := edge ▸ source
        have generatedAtEdge : sealedGeometry? 18 divider = some geometry := edge ▸ generated
        have base := CorridorPreparation.base sourceAtEdge geometry generatedAtEdge
        have playing : frame.visible.status = .playing := by
          rcases source with ⟨_, _, _, _, _, playing, _⟩
          exact playing
        some (.vitalChambers ⟨geometry, base.1⟩ (.inl playing) base.2)
      else
        have beforeEdge : j < 18 := by have upper := source.2.1; omega
        let prepared := CorridorPreparation.prepare source beforeEdge geometry generated
        have opponent : frame.visible.toMove = Polarity.positive.other := by
          rcases source with ⟨_, _, _, _, _, _, opponent, _⟩
          exact opponent
        have passes : frame.visible.consecutivePasses = 0 := by
          rcases source with ⟨_, _, _, _, _, _, _, passes, _⟩
          exact passes
        ExceptionalAll.certificateWithStep? frame (.play (point 0 j))
          (fun _move _target scoring step avoided =>
            VitalBirthCapturing.afterOpponent (CoalitionBirth.retained frame .positive)
              (CoalitionBirth.retained_tracked frame .positive)
              prepared.candidate.plan prepared.saved prepared.candidate.virgin
              opponent passes scoring step
              (by simpa only [prepared.point_eq] using avoided) (-345) prepared.candidate.accepted)
          (fun target step =>
            let next := CorridorContinuation.continuation source beforeEdge step
            have owned : target.visible.toMove = .positive := by
              have actual := (CoalitionBirth.play_data step).2.2.2
              rw [actual, opponent]; rfl
            (fromSource? next.next_source).map (fun child => .choose owned next.reply child))
termination_by 18 - j
decreasing_by omega

def certificate? (j divider : Nat) (frame : Frame 19) :
    Option (Certificate .positive (-345) frame) :=
  if source : Source frame j divider then fromSource? source else none

def enter? (frame : Frame 19) (j divider : Nat) :
    Option (Certificate .positive (-345) frame) :=
  choose? frame (point 0 divider) (certificate? j divider)

def middleInvasionResponse? (frame : Frame 19) :
    Option (Certificate .positive (-345) frame) :=
  enter? frame 4 2

end SaturationMonoid.ProcessGame.Go.CriticalKomi.Corridor
