import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEyeGrowth
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEyeFamily

/-!
A two-point chamber attached to a living core admits a source-generated
response to invasion.  Filling the other point captures the invader under the
original rules, enlarges the core, and turns the vacated point into an extra
permanent eye.  No dead-stone removal convention is added to area scoring.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoPointChamber

open TwoEye

structure Geometry {n : Nat} (g : TwoEye.Geometry n) where
  first : Point n
  second : Point n
  distinct : first ≠ second
  adjacent : second ∈ adjacentPoints first
  boundaryFirst : adjacentPoints first ⊆ insert second g.core
  boundarySecond : adjacentPoints second ⊆ insert first g.core
  attachedFirst : Growth.Attached g first
  attachedSecond : Growth.Attached g second
  firstEye₁ : first ≠ g.eye₁
  firstEye₂ : first ≠ g.eye₂
  secondEye₁ : second ≠ g.eye₁
  secondEye₂ : second ≠ g.eye₂

def Geometry.swap {n : Nat} {g : TwoEye.Geometry n} (chamber : Geometry g) : Geometry g where
  first := chamber.second
  second := chamber.first
  distinct := chamber.distinct.symm
  adjacent := mem_adjacentPoints_iff_orthogonallyAdjacent.mpr
    (orthogonallyAdjacent_symm (mem_adjacentPoints_iff_orthogonallyAdjacent.mp chamber.adjacent))
  boundaryFirst := chamber.boundarySecond
  boundarySecond := chamber.boundaryFirst
  attachedFirst := chamber.attachedSecond
  attachedSecond := chamber.attachedFirst
  firstEye₁ := chamber.secondEye₁
  firstEye₂ := chamber.secondEye₂
  secondEye₁ := chamber.firstEye₁
  secondEye₂ := chamber.firstEye₂

private theorem no_liberty_surrounded {n : Nat} {board : Board n} {colour : Polarity}
    {seed : Point n} (occupied : board seed = some colour)
    (surrounded : ∀ point ∈ adjacentPoints seed, board point = some colour.other) :
    ¬ stoneHasLiberty board seed := by
  have singleton : ∀ point ∈ componentAt board seed, point = seed := by
    apply componentAt_minimal (predicate := fun point => point = seed) rfl
    intro current _ currentEq candidate adjacent same
    subst current
    have opposite := surrounded candidate
      (by simpa only [adjacentPoints, List.mem_toFinset] using adjacent)
    rw [occupied] at same
    exact False.elim (Polarity.other_ne colour (Option.some.inj (opposite.symm.trans same)))
  rintro ⟨stone, member, liberty, adjacent, empty⟩
  have same : stone = seed := singleton stone (by simpa only [groupAt, occupied] using member)
  subst stone
  rw [surrounded liberty adjacent] at empty
  cases empty

theorem invader_captured {n : Nat} {g : TwoEye.Geometry n} (chamber : Geometry g)
    {colour : Polarity} {board : Board n} (inside : TwoEye.Holds g colour board)
    (invader : board chamber.first = some colour.other) :
    chamber.first ∈ capturedStonesAfterPlay board colour chamber.second := by
  have occupied : Board.set board chamber.second (some colour) chamber.first =
      some colour.other := by
    rw [Board.set_other _ _ chamber.distinct]
    exact invader
  have noLiberty : ¬ stoneHasLiberty
      (Board.set board chamber.second (some colour)) chamber.first := by
    apply no_liberty_surrounded occupied
    intro point adjacent
    rw [Polarity.other_other]
    rcases Finset.mem_insert.mp (chamber.boundaryFirst adjacent) with same | member
    · subst point
      exact Board.set_self _ _ _
    · have old := TwoEye.core_colour inside member
      by_cases same : point = chamber.second
      · subst point
        exact Board.set_self _ _ _
      · rw [Board.set_other _ _ same]
        exact old
  unfold capturedStonesAfterPlay
  apply Finset.mem_biUnion.mpr
  refine ⟨chamber.first, chamber.swap.adjacent, ?_⟩
  rw [if_pos ⟨occupied, noLiberty⟩]
  exact occupied_point_mem_groupAt occupied

/-- The captured point is now a third permanent eye on the enlarged core. -/
def extraEye {n : Nat} {g : TwoEye.Geometry n} (chamber : Geometry g) : TwoEye.Geometry n where
  seed := g.seed
  core := insert chamber.second g.core
  eye₁ := g.eye₁
  eye₂ := chamber.first
  distinct := chamber.firstEye₁.symm
  boundary₁ := g.boundary₁.trans (Finset.subset_insert _ _)
  boundary₂ := chamber.boundaryFirst
  neighbour₁ := g.neighbour₁
  neighbour₂ := ⟨chamber.second, chamber.adjacent⟩

def securedFamily {n : Nat} {g : TwoEye.Geometry n} (chamber : Geometry g) : TwoEyeFamily.Family n :=
  [Growth.enlarge g chamber.second, extraEye chamber]

theorem capture_secures {n : Nat} {g : TwoEye.Geometry n} (chamber : Geometry g)
    {colour : Polarity} {board : Board n} (inside : TwoEye.Holds g colour board)
    (invader : board chamber.first = some colour.other) (empty : board chamber.second = none) :
    TwoEyeFamily.Holds (securedFamily chamber) colour
      (boardAfterPlay board colour chamber.second) := by
  have grown := Growth.own_enlarges inside chamber.second empty
    chamber.secondEye₁ chamber.secondEye₂ chamber.attachedSecond
  have extra : TwoEye.Holds (extraEye chamber) colour (boardAfterPlay board colour chamber.second) :=
    ⟨grown.1, grown.2.1, grown.2.2.1,
      boardAfterPlay_eq_none_of_mem_captured (invader_captured chamber inside invader)⟩
  intro geometry member
  simp only [securedFamily, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact grown
  · exact extra

theorem unplayed_empty {n : Nat} {board : Board n} {colour : Polarity}
    {played point : Point n} (empty : board point = none) (different : point ≠ played) :
    boardAfterPlay board colour played point = none := by
  unfold boardAfterPlay
  split
  · rfl
  · rw [Board.set_other _ _ different]
    exact empty

/-- The same response seals an empty chamber or removes its single invader. -/
theorem seal_secures {n : Nat} {g : TwoEye.Geometry n} (chamber : Geometry g)
    {colour : Polarity} {board : Board n} (inside : TwoEye.Holds g colour board)
    (first : board chamber.first = none ∨ board chamber.first = some colour.other)
    (empty : board chamber.second = none) :
    TwoEyeFamily.Holds (securedFamily chamber) colour
      (boardAfterPlay board colour chamber.second) := by
  rcases first with emptyFirst | invader
  · have grown := Growth.own_enlarges inside chamber.second empty
      chamber.secondEye₁ chamber.secondEye₂ chamber.attachedSecond
    have extra : TwoEye.Holds (extraEye chamber) colour
        (boardAfterPlay board colour chamber.second) :=
      ⟨grown.1, grown.2.1, grown.2.2.1, unplayed_empty emptyFirst chamber.distinct⟩
    intro geometry member
    simp only [securedFamily, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact grown
    · exact extra
  · exact capture_secures chamber inside invader empty

theorem secured_points {n : Nat} {g : TwoEye.Geometry n} (chamber : Geometry g) :
    TwoEyeFamily.points (securedFamily chamber) =
      insert chamber.first (insert chamber.second (g.core ∪ {g.eye₁, g.eye₂})) := by
  ext point
  simp [securedFamily, TwoEyeFamily.points, TwoEyeFamily.groupPoints,
    Growth.enlarge, extraEye, Finset.mem_insert, or_left_comm, or_comm]

theorem secured_area_count {n : Nat} {g : TwoEye.Geometry n} (chamber : Geometry g)
    {colour : Polarity} {board : Board n} (inside : TwoEye.Holds g colour board)
    (first : board chamber.first = none ∨ board chamber.first = some colour.other)
    (empty : board chamber.second = none) :
    (TwoEyeFamily.points (securedFamily chamber)).card = g.core.card + 4 := by
  have firstNotCore : chamber.first ∉ g.core := by
    intro member
    have occupied := TwoEye.core_colour inside member
    rcases first with vacant | opposite
    · rw [vacant] at occupied
      cases occupied
    · exact Polarity.other_ne colour (Option.some.inj (opposite.symm.trans occupied))
  have secondNotCore : chamber.second ∉ g.core := by
    intro member
    have occupied := TwoEye.core_colour inside member
    rw [empty] at occupied
    cases occupied
  have firstFresh : chamber.first ∉ insert chamber.second (g.core ∪ {g.eye₁, g.eye₂}) := by
    simp [chamber.distinct, firstNotCore, chamber.firstEye₁, chamber.firstEye₂]
  have secondFresh : chamber.second ∉ g.core ∪ {g.eye₁, g.eye₂} := by
    simp [secondNotCore, chamber.secondEye₁, chamber.secondEye₂]
  rw [secured_points, Finset.card_insert_of_notMem firstFresh,
    Finset.card_insert_of_notMem secondFresh, TwoEye.Score.core_two_eyes_card inside]

def bound {n : Nat} (g : TwoEye.Geometry n) : Polarity → Int
  | .positive => 2 * ((g.core.card + 4 : Nat) : Int) - ((n * n : Nat) : Int)
  | .negative => ((n * n : Nat) : Int) - 2 * ((g.core.card + 4 : Nat) : Int)

theorem secured_bound {n : Nat} {g : TwoEye.Geometry n} (chamber : Geometry g)
    {colour : Polarity} {board : Board n} (inside : TwoEye.Holds g colour board)
    (first : board chamber.first = none ∨ board chamber.first = some colour.other)
    (empty : board chamber.second = none) :
    TwoEyeFamily.bound (securedFamily chamber) colour = bound g colour := by
  have count := secured_area_count chamber inside first empty
  cases colour <;> simp only [TwoEyeFamily.bound, bound, count]

/-- Original legal response followed by a score closure that covers every later opponent. -/
def captureReply {n : Nat} {g : TwoEye.Geometry n} (chamber : Geometry g)
    {colour : Polarity} (frame : Frame n) (playing : frame.visible.status = .playing)
    (owned : frame.visible.toMove = colour) (inside : TwoEye.Holds g colour frame.visible.board)
    (empty : frame.visible.board chamber.second = none)
    (virgin : Growth.Virgin g colour chamber.second frame.positionHistory) : ScoringReply frame :=
  Growth.reply frame playing owned inside chamber.second empty
    chamber.secondEye₁ chamber.secondEye₂ chamber.attachedSecond virgin

theorem captureReply_secures {n : Nat} {g : TwoEye.Geometry n} (chamber : Geometry g)
    {colour : Polarity} (frame : Frame n) (playing : frame.visible.status = .playing)
    (owned : frame.visible.toMove = colour) (inside : TwoEye.Holds g colour frame.visible.board)
    (invader : frame.visible.board chamber.first = some colour.other)
    (empty : frame.visible.board chamber.second = none)
    (virgin : Growth.Virgin g colour chamber.second frame.positionHistory) :
    TwoEyeFamily.Holds (securedFamily chamber) colour
      (captureReply chamber frame playing owned inside empty virgin).target.visible.board :=
  capture_secures chamber inside invader empty

end SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoPointChamber
