import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.HookSourceGeometry
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CorridorContinuation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.HookSource

attribute [local instance 2000] Finset.decidableDforallFinset Finset.decidableDExistsFinset

structure Source (frame : Frame 19) : Prop where
  playing : frame.visible.status = .playing
  opponent : frame.visible.toMove = .negative
  passes : frame.visible.consecutivePasses = 0
  occupied : ∀ p ∈ core, frame.visible.board p = some .positive
  invader : frame.visible.board (0,1) = some .negative
  empty : ∀ p ∈ air, frame.visible.board p = none
  virgin : Disjoint fresh (CoalitionBirth.retained frame .positive)

instance (frame : Frame 19) : Decidable (Source frame) :=
  if facts : frame.visible.status = .playing ∧ frame.visible.toMove = .negative ∧
      frame.visible.consecutivePasses = 0 ∧
      (∀ p ∈ core, frame.visible.board p = some .positive) ∧
      frame.visible.board (0,1) = some .negative ∧
      (∀ p ∈ air, frame.visible.board p = none) ∧
      Disjoint fresh (CoalitionBirth.retained frame .positive) then
    isTrue ⟨facts.1, facts.2.1, facts.2.2.1, facts.2.2.2.1,
      facts.2.2.2.2.1, facts.2.2.2.2.2.1, facts.2.2.2.2.2.2⟩
  else isFalse (fun source => facts ⟨source.playing, source.opponent, source.passes,
    source.occupied, source.invader, source.empty, source.virgin⟩)

theorem Source.notOwn {frame : Frame 19} (source : Source frame) :
    ∀ p ∈ roomPoints, frame.visible.board p ≠ some .positive := by
  intro p member
  rcases Finset.mem_insert.mp member with same | empty
  · subst p; rw [source.invader]; decide
  · rw [source.empty p empty]; simp

theorem Source.reserve {frame : Frame 19} (source : Source frame) :
    ∀ p ∈ core, 2 ≤ (LibertyReserve.liberties frame.visible.board p).card :=
  reserve_of_top_pair core_touches source.occupied (left := (0,0)) (right := (0,2))
    (by decide) (by decide) (by decide) (source.empty _ (by decide)) (source.empty _ (by decide))

structure WhiteFacts (frame : Frame 19) (move : Move 19) (seen : Finset (Point 19)) : Prop where
  playing : frame.visible.status = .playing
  owned : frame.visible.toMove = .positive
  occupied : ∀ p ∈ core, frame.visible.board p = some .positive
  empty : ∀ p ∈ air, move ≠ .play p → frame.visible.board p = none
  notOwn : ∀ p ∈ roomPoints, frame.visible.board p ≠ some .positive
  tracked : VirginHistory.Tracked frame .positive seen

theorem afterWhite {frame target : Frame 19} {move : Move 19} (source : Source frame)
    (scoring : move ≠ .resign) (step : LegalStep (Law.positionalSuperko 0) frame move target) :
    WhiteFacts target move (CoalitionBirth.retained frame .positive) := by
  have tracked := VirginHistory.step (CoalitionBirth.retained_tracked frame .positive) scoring step
  have occupied : ∀ p ∈ core, target.visible.board p = some .positive :=
    fun p member => (LibertyReserve.opponent_legalStep (source.occupied p member)
      (source.reserve p member) source.opponent scoring step).1
  cases move with
  | resign => exact False.elim (scoring rfl)
  | pass =>
      have facts := pass_step_facts step
      refine ⟨?_, ?_, occupied, ?_, ?_, ?_⟩
      · simpa only [source.passes, Nat.zero_add, show ¬ 2 ≤ (1 : Nat) from by omega, ↓reduceIte]
          using facts.2.2.2
      · rw [CoalitionBirth.pass_turn step, source.opponent]; rfl
      · intro p member _; rw [facts.2.1]; exact source.empty p member
      · intro p member; rw [facts.2.1]; exact source.notOwn p member
      · simpa only [VirginHistory.nextSeen] using tracked
  | play played =>
      have facts := CoalitionBirth.play_data step
      have boardEq : target.visible.board = boardAfterPlay frame.visible.board .negative played := by
        rw [facts.2.2.1, source.opponent]
      refine ⟨(play_step_facts step).2.1, ?_, occupied, ?_, ?_, ?_⟩
      · rw [facts.2.2.2, source.opponent]; rfl
      · intro p member different
        rw [boardEq]
        exact CoalitionBirth.empty_after_other (source.empty p member)
          (fun same => different (congrArg Move.play same.symm))
      · intro p member; rw [boardEq]
        exact CorridorContinuation.opponent_not_own (board := frame.visible.board)
          (colour := .positive) (played := played) (p := p) (source.notOwn p member)
      · simpa only [VirginHistory.nextSeen, source.opponent, reduceCtorEq, ↓reduceIte] using tracked

theorem Foot.top_ne (foot : Foot) {p : Point 19} (member : p ∈ tops) : p ≠ foot.point := by
  have disjoint : Disjoint tops ({foot.point} : Finset (Point 19)) := by cases foot <;> decide
  intro same
  exact Finset.disjoint_left.mp disjoint member (Finset.mem_singleton.mpr same)

theorem Foot.air (foot : Foot) : foot.point ∈ air := by cases foot <;> decide
theorem Foot.fresh (foot : Foot) : foot.point ∈ fresh := by cases foot <;> decide
theorem Foot.eye_room (foot : Foot) : foot.eye ∈ roomPoints := by cases foot <;> decide
theorem Foot.eye_ne (foot : Foot) : foot.eye ≠ foot.point := by cases foot <;> decide
theorem Foot.eye_adjacent (foot : Foot) : foot.eye ∈ adjacentPoints foot.point := by cases foot <;> decide
theorem Foot.eye_boundary (foot : Foot) : adjacentPoints foot.eye ⊆ foot.core := by cases foot <;> decide

theorem placed_core {frame : Frame 19} {move : Move 19} {seen : Finset (Point 19)}
    (facts : WhiteFacts frame move seen) (foot : Foot) :
    ∀ p ∈ foot.core, boardAfterPlay frame.visible.board .positive foot.point p = some .positive := by
  intro p member
  rcases Finset.mem_insert.mp member with same | old
  · subst p; exact TwoEye.Growth.placed_survives _ _ _
  · exact TwoEye.Growth.own_stone_survives (facts.occupied p old) foot.point

theorem placed_empty {frame : Frame 19} {move : Move 19} {seen : Finset (Point 19)}
    (facts : WhiteFacts frame move seen) (foot : Foot) {p : Point 19}
    (member : p ∈ air) (avoided : move ≠ .play p) (different : p ≠ foot.point) :
    boardAfterPlay frame.visible.board .positive foot.point p = none :=
  CoalitionBirth.empty_after_other (facts.empty p member avoided) different

theorem placed_reserve {frame : Frame 19} {move : Move 19} {seen : Finset (Point 19)}
    (facts : WhiteFacts frame move seen) (foot : Foot) :
    ∀ p ∈ foot.core, 2 ≤ (LibertyReserve.liberties
      (boardAfterPlay frame.visible.board .positive foot.point) p).card := by
  apply reserve_after_one (foot_touches foot) (placed_core facts foot) move
  intro p member avoided
  exact placed_empty facts foot ((show tops ⊆ air by decide) member) avoided (foot.top_ne member)

theorem placed_legal {frame : Frame 19} {move : Move 19} {seen : Finset (Point 19)}
    (facts : WhiteFacts frame move seen) (foot : Foot) :
    stoneHasLiberty (boardAfterPlay frame.visible.board .positive foot.point) foot.point := by
  have reserve := placed_reserve facts foot foot.point (Finset.mem_insert_self _ _)
  obtain ⟨liberty, member⟩ := Finset.card_pos.mp (show 0 < (LibertyReserve.liberties
    (boardAfterPlay frame.visible.board .positive foot.point) foot.point).card from by omega)
  obtain ⟨⟨stone, inside, adjacent⟩, empty⟩ := LibertyReserve.mem_liberties.mp member
  exact ⟨stone, inside, liberty, adjacent, empty⟩

def reply {frame target : Frame 19} {move : Move 19} (source : Source frame)
    (scoring : move ≠ .resign) (step : LegalStep (Law.positionalSuperko 0) frame move target)
    (foot : Foot) (avoided : move ≠ .play foot.point) : ScoringReply target :=
  let facts := afterWhite source scoring step
  have virgin : foot.point ∉ CoalitionBirth.retained frame .positive :=
    fun member => Finset.disjoint_left.mp source.virgin foot.fresh member
  VirginHistory.reply target .positive (CoalitionBirth.retained frame .positive) facts.tracked
    foot.point virgin facts.playing facts.owned (facts.empty _ foot.air avoided) (placed_legal facts foot)

structure BlackFacts (frame : Frame 19) (move : Move 19) (foot : Foot)
    (seen : Finset (Point 19)) : Prop where
  playing : frame.visible.status = .playing
  opponent : frame.visible.toMove = .negative
  passes : frame.visible.consecutivePasses = 0
  occupied : ∀ p ∈ foot.core, frame.visible.board p = some .positive
  empty : ∀ p ∈ air, move ≠ .play p → p ≠ foot.point → frame.visible.board p = none
  notOwn : ∀ p ∈ roomPoints, p ≠ foot.point → frame.visible.board p ≠ some .positive
  eye : frame.visible.board foot.eye = none
  reserve : ∀ p ∈ foot.core, 2 ≤ (LibertyReserve.liberties frame.visible.board p).card
  tracked : VirginHistory.Tracked frame .positive (insert foot.point seen)

theorem afterBlack {frame target : Frame 19} {move : Move 19} (source : Source frame)
    (scoring : move ≠ .resign) (step : LegalStep (Law.positionalSuperko 0) frame move target)
    (foot : Foot) (avoided : move ≠ .play foot.point) :
    BlackFacts (reply source scoring step foot avoided).target move foot
      (CoalitionBirth.retained frame .positive) := by
  let facts := afterWhite source scoring step
  refine ⟨rfl, rfl, rfl, placed_core facts foot, ?_, ?_, ?_, placed_reserve facts foot, ?_⟩
  · intro p member notPlayed different
    exact placed_empty facts foot member notPlayed different
  · intro p member different
    exact CorridorContinuation.own_not_own (facts.notOwn p member) different
  · apply empty_surrounded_after (facts.notOwn _ foot.eye_room) foot.eye_ne foot.eye_adjacent
    intro p member
    rcases Finset.mem_insert.mp (foot.eye_boundary member) with same | old
    · subst p; exact Board.set_self _ _ _
    · by_cases same : p = foot.point
      · subst p; exact Board.set_self _ _ _
      · rw [Board.set_other _ _ same]; exact facts.occupied p old
  · exact VirginHistory.reply_tracked target .positive (CoalitionBirth.retained frame .positive)
      facts.tracked foot.point
      (fun member => Finset.disjoint_left.mp source.virgin foot.fresh member)
      facts.playing facts.owned (facts.empty _ foot.air avoided) (placed_legal facts foot)

def Available (shape : Shape) (move : Move 19) : Prop :=
  match shape with
  | .leftTwo | .rightTwo => move ≠ .play (0,0) ∧ move ≠ .play (0,2)
  | .leftThree | .rightThree => move ≠ .play (0,3) ∧
      (move ≠ .play (0,0) ∨ move ≠ .play (0,2))
  | .leftLower => move ≠ .play (2,2) ∧ move ≠ .play (3,2)

theorem cap_available {shape : Shape} {move : Move 19} (available : Available shape move) :
    move ≠ .play shape.cap := by
  cases shape with
  | leftTwo => exact available.2
  | leftThree => exact available.1
  | leftLower => exact available.2
  | rightTwo => exact available.2
  | rightThree => exact available.1

theorem Shape.cap_air (shape : Shape) : shape.cap ∈ air := by cases shape <;> decide
theorem Shape.cap_fresh (shape : Shape) : shape.cap ∈ fresh := by cases shape <;> decide
theorem Shape.cap_ne (shape : Shape) : shape.cap ≠ shape.foot.point := by cases shape <;> decide

theorem Shape.room_fields (shape : Shape) : ∀ room ∈ shape.rooms,
    room ⊆ roomPoints ∧ shape.cap ∉ room ∧ shape.foot.point ∉ room := by cases shape <;> decide

theorem room_vacancy {shape : Shape} {move : Move 19} (available : Available shape move) :
    ∀ room ∈ shape.rooms, ∃ p ∈ room,
      (p = shape.foot.eye ∨ (p ∈ air ∧ move ≠ .play p)) ∧ p ≠ shape.cap ∧ p ≠ shape.foot.point := by
  cases shape with
  | leftTwo =>
      intro room member
      rcases Finset.mem_insert.mp member with rfl | last
      · exact ⟨(0,0), by decide, Or.inr ⟨by decide, available.1⟩, by decide, by decide⟩
      · have same := Finset.mem_singleton.mp last; subst room
        exact ⟨(2,0), by decide, Or.inl rfl, by decide, by decide⟩
  | leftThree =>
      intro room member
      rcases Finset.mem_insert.mp member with rfl | last
      · rcases available.2 with zero | two
        · exact ⟨(0,0), by decide, Or.inr ⟨by decide, zero⟩, by decide, by decide⟩
        · exact ⟨(0,2), by decide, Or.inr ⟨by decide, two⟩, by decide, by decide⟩
      · have same := Finset.mem_singleton.mp last; subst room
        exact ⟨(2,0), by decide, Or.inl rfl, by decide, by decide⟩
  | leftLower =>
      intro room member
      rcases Finset.mem_insert.mp member with rfl | last
      · exact ⟨(2,0), by decide, Or.inl rfl, by decide, by decide⟩
      · have same := Finset.mem_singleton.mp last; subst room
        exact ⟨(2,2), by decide, Or.inr ⟨by decide, available.1⟩, by decide, by decide⟩
  | rightTwo =>
      intro room member
      rcases Finset.mem_insert.mp member with rfl | last
      · exact ⟨(0,0), by decide, Or.inr ⟨by decide, available.1⟩, by decide, by decide⟩
      · have same := Finset.mem_singleton.mp last; subst room
        exact ⟨(2,2), by decide, Or.inl rfl, by decide, by decide⟩
  | rightThree =>
      intro room member
      rcases Finset.mem_insert.mp member with rfl | last
      · rcases available.2 with zero | two
        · exact ⟨(0,0), by decide, Or.inr ⟨by decide, zero⟩, by decide, by decide⟩
        · exact ⟨(0,2), by decide, Or.inr ⟨by decide, two⟩, by decide, by decide⟩
      · have same := Finset.mem_singleton.mp last; subst room
        exact ⟨(2,2), by decide, Or.inl rfl, by decide, by decide⟩

def plan {frame : Frame 19} {move : Move 19} {shape : Shape} {seen : Finset (Point 19)}
    (facts : BlackFacts frame move shape.foot seen) (available : Available shape move)
    (data : Compiled shape) : VitalBirth.Plan frame.visible.board .positive where
  point := shape.cap
  empty := facts.empty _ shape.cap_air (cap_available available) shape.cap_ne
  detected := ⟨data.geometry, by
    refine ⟨?_, ?_, ?_⟩
    · intro p member
      rw [data.fields.1] at member
      rcases Finset.mem_insert.mp member with same | old
      · subst p; exact Board.set_self _ _ _
      · by_cases same : p = shape.cap
        · subst p; exact Board.set_self _ _ _
        · rw [Board.set_other _ _ same]; exact facts.occupied p old
    · intro room member p inside
      rw [data.fields.2] at member
      have fields := shape.room_fields room member
      have different : p ≠ shape.cap := fun same => fields.2.1 (same ▸ inside)
      rw [Board.set_other _ _ different]
      exact facts.notOwn p (fields.1 inside) (fun same => fields.2.2 (same ▸ inside))
    · intro room member
      rw [data.fields.2] at member
      obtain ⟨p, inside, vacant, capDifferent, footDifferent⟩ := room_vacancy available room member
      refine ⟨p, inside, ?_⟩
      rw [Board.set_other _ _ capDifferent]
      rcases vacant with same | old
      · rw [same]; exact facts.eye
      · exact facts.empty p old.1 old.2 footDifferent⟩
  participates := by rw [data.fields.1]; exact Finset.mem_insert_self _ _

theorem plan_saved {frame : Frame 19} {move : Move 19} {shape : Shape} {seen : Finset (Point 19)}
    (facts : BlackFacts frame move shape.foot seen) (available : Available shape move)
    (data : Compiled shape) : VitalBirth.SavedCore (plan facts available data) := by
  intro p member different
  change p ∈ data.geometry.core at member
  change p ≠ shape.cap at different
  rw [data.fields.1] at member
  rcases Finset.mem_insert.mp member with same | old
  · exact False.elim (different same)
  · exact facts.reserve p old

def miai {frame : Frame 19} {move : Move 19} {foot : Foot} {seen : Finset (Point 19)}
    (facts : BlackFacts frame move foot seen) (virgin : Disjoint fresh seen)
    (left right : Shape) (leftFoot : left.foot = foot) (rightFoot : right.foot = foot)
    (different : left.cap ≠ right.cap) (leftAvailable : Available left move)
    (rightAvailable : Available right move) (leftData : Compiled left) (rightData : Compiled right) :
    Certificate .positive (-341) frame :=
  let leftFacts : BlackFacts frame move left.foot seen := leftFoot.symm ▸ facts
  let rightFacts : BlackFacts frame move right.foot seen := rightFoot.symm ▸ facts
  let leftPlan := plan leftFacts leftAvailable leftData
  let rightPlan := plan rightFacts rightAvailable rightData
  have unused (shape : Shape) (sameFoot : shape.foot = foot) :
      shape.cap ∉ insert foot.point seen := by
    intro member
    rcases Finset.mem_insert.mp member with same | old
    · exact shape.cap_ne (same.trans (congrArg Foot.point sameFoot).symm)
    · exact Finset.disjoint_left.mp virgin shape.cap_fresh old
  VitalBirth.miaiCertificate (insert foot.point seen) facts.tracked leftPlan rightPlan different
    (plan_saved leftFacts leftAvailable leftData) (plan_saved rightFacts rightAvailable rightData)
    (unused left leftFoot) (unused right rightFoot) facts.playing facts.opponent facts.passes
    (-341) leftData.accepted rightData.accepted

inductive Pattern where
  | atThirty
  | atZero
  | atTwo
  | atThree
  | away

def Pattern.matches : Pattern → Move 19 → Prop
  | .atThirty, move => move = .play (3,0)
  | .atZero, move => move = .play (0,0)
  | .atTwo, move => move = .play (0,2)
  | .atThree, move => move = .play (0,3)
  | .away, move => move ≠ .play (3,0) ∧ move ≠ .play (0,0) ∧ move ≠ .play (0,2) ∧ move ≠ .play (0,3)

def classify (move : Move 19) : {pattern : Pattern // pattern.matches move} :=
  if thirty : move = .play (3,0) then ⟨.atThirty, thirty⟩
  else if zero : move = .play (0,0) then ⟨.atZero, zero⟩
  else if two : move = .play (0,2) then ⟨.atTwo, two⟩
  else if three : move = .play (0,3) then ⟨.atThree, three⟩
  else ⟨.away, thirty, zero, two, three⟩

def Pattern.foot : Pattern → Foot
  | .atThirty => .right
  | _ => .left

def Pattern.left : Pattern → Shape
  | .atThirty => .rightTwo
  | .atZero | .atTwo => .leftThree
  | .atThree | .away => .leftTwo

def Pattern.right : Pattern → Shape
  | .atThirty => .rightThree
  | .atZero | .atTwo | .atThree => .leftLower
  | .away => .leftThree

theorem Pattern.fields (pattern : Pattern) : pattern.left.foot = pattern.foot ∧
    pattern.right.foot = pattern.foot ∧ pattern.left.cap ≠ pattern.right.cap := by
  cases pattern <;> decide

theorem Pattern.avoids {pattern : Pattern} {move : Move 19} (actual : pattern.matches move) :
    move ≠ .play pattern.foot.point := by
  cases pattern <;> simp_all [Pattern.matches, Pattern.foot, Foot.point]

theorem Pattern.available {pattern : Pattern} {move : Move 19} (actual : pattern.matches move) :
    Available pattern.left move ∧ Available pattern.right move := by
  cases pattern <;> simp_all [Pattern.matches, Pattern.left, Pattern.right, Available]

def response {frame target : Frame 19} {move : Move 19} (source : Source frame)
    (data : (shape : Shape) → Compiled shape) (scoring : move ≠ .resign)
    (step : LegalStep (Law.positionalSuperko 0) frame move target) : Certificate .positive (-341) target :=
  let material := BufferedReplay.restore (BufferedReplay.capture target)
  have same : material = target := BufferedReplay.restore_capture target
  have actual : LegalStep (Law.positionalSuperko 0) frame move material := by rw [same]; exact step
  let pattern := classify move
  let raw := reply source scoring actual pattern.val.foot (Pattern.avoids pattern.property)
  let next := BufferedReplay.restore (BufferedReplay.capture raw.target)
  have nextSame : next = raw.target := BufferedReplay.restore_capture raw.target
  let stored : ScoringReply material :=
    ⟨raw.move, next, raw.notResign, by rw [nextSame]; exact raw.step⟩
  have facts : BlackFacts next move pattern.val.foot (CoalitionBirth.retained frame .positive) := by
    rw [nextSame]; exact afterBlack source scoring actual _ (Pattern.avoids pattern.property)
  let fields := pattern.val.fields
  let available := Pattern.available pattern.property
  let child := miai facts source.virgin pattern.val.left pattern.val.right
    fields.1 fields.2.1 fields.2.2 available.1 available.2 (data _) (data _)
  same ▸ .choose (afterWhite source scoring actual).owned stored child

/-- The source compiles five fixed room geometries once. Every original
opponent port then generates its native lower completion and universal miai. -/
def certificate? {frame : Frame 19} (source : Source frame) : Option (Certificate .positive (-341) frame) :=
  compiled.get.map (fun data =>
    let delayed : Thunk (List (Move 19 × Frame 19)) := ⟨fun _ => scoringExpansion frame⟩
    .all source.playing (by rw [source.opponent]; decide) (fun port =>
      let expansion := delayed.get
      let facts := mem_scoringExpansion_iff.mp (List.get_mem expansion port)
      response source data facts.2 facts.1))

end SaturationMonoid.ProcessGame.Go.CriticalKomi.HookSource
