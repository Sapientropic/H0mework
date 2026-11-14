import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CorridorPreparation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.HookSource

attribute [local instance 2000] Finset.decidableDforallFinset Finset.decidableDExistsFinset

def core : Finset (Point 19) := {(1,0), (1,1), (1,2), (1,3), (2,1), (2,3), (3,1)}
def air : Finset (Point 19) := {(0,0), (0,2), (0,3), (2,0), (2,2), (3,0), (3,2)}
def fresh : Finset (Point 19) := {(0,2), (0,3), (3,0), (3,2)}
def roomPoints : Finset (Point 19) := insert (0,1) air
def tops : Finset (Point 19) := {(0,0), (0,2), (0,3)}

inductive Foot where
  | left
  | right
  deriving DecidableEq

def Foot.point : Foot → Point 19
  | .left => (3,0)
  | .right => (3,2)

def Foot.eye : Foot → Point 19
  | .left => (2,0)
  | .right => (2,2)

def Foot.core (foot : Foot) : Finset (Point 19) := insert foot.point HookSource.core

def touches (stones : Finset (Point 19)) : Prop :=
  ∀ seed ∈ stones, tops ⊆ (groupAt (EyeCoalition.mask stones) seed).biUnion adjacentPoints

instance (stones : Finset (Point 19)) : Decidable (touches stones) :=
  inferInstanceAs (Decidable (∀ seed ∈ stones, tops ⊆
    (groupAt (EyeCoalition.mask stones) seed).biUnion adjacentPoints))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem core_touches : touches core := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem foot_touches (foot : Foot) : touches foot.core := by cases foot <;> decide

theorem reserve_of_top_pair {board : Board 19} {stones : Finset (Point 19)}
    (support : touches stones) (occupied : ∀ p ∈ stones, board p = some .positive)
    {left right : Point 19} (leftTop : left ∈ tops) (rightTop : right ∈ tops)
    (different : left ≠ right) (leftEmpty : board left = none) (rightEmpty : board right = none) :
    ∀ seed ∈ stones, 2 ≤ (LibertyReserve.liberties board seed).card := by
  intro seed inside
  have member {point : Point 19} (top : point ∈ tops) (empty : board point = none) :
      point ∈ LibertyReserve.liberties board seed := by
    obtain ⟨stone, group, adjacent⟩ := Finset.mem_biUnion.mp (support seed inside top)
    exact LibertyReserve.mem_liberties.mpr
      ⟨⟨stone, EyeCoalition.mask_component_subset inside occupied group, adjacent⟩, empty⟩
  have included : ({left, right} : Finset (Point 19)) ⊆ LibertyReserve.liberties board seed := by
    intro p hp
    rcases Finset.mem_insert.mp hp with same | last
    · simpa only [same] using member leftTop leftEmpty
    · simpa only [Finset.mem_singleton.mp last] using member rightTop rightEmpty
  simpa only [Finset.card_pair different] using Finset.card_le_card included

theorem reserve_after_one {board : Board 19} {stones : Finset (Point 19)}
    (support : touches stones) (occupied : ∀ p ∈ stones, board p = some .positive)
    (move : Move 19) (empty : ∀ p ∈ tops, move ≠ .play p → board p = none) :
    ∀ seed ∈ stones, 2 ≤ (LibertyReserve.liberties board seed).card := by
  by_cases first : move = .play (0,0)
  · apply reserve_of_top_pair support occupied (left := (0,2)) (right := (0,3))
      (by decide) (by decide) (by decide)
    · exact empty _ (by decide) (by simp [first])
    · exact empty _ (by decide) (by simp [first])
  · by_cases second : move = .play (0,2)
    · apply reserve_of_top_pair support occupied (left := (0,0)) (right := (0,3))
        (by decide) (by decide) (by decide)
      · exact empty _ (by decide) first
      · exact empty _ (by decide) (by simp [second])
    · exact reserve_of_top_pair support occupied (left := (0,0)) (right := (0,2))
        (by decide) (by decide) (by decide) (empty _ (by decide) first) (empty _ (by decide) second)

theorem empty_surrounded_after {board : Board 19} {played point : Point 19}
    (notOwn : board point ≠ some .positive) (different : point ≠ played)
    (touching : point ∈ adjacentPoints played)
    (boundary : ∀ p ∈ adjacentPoints point, Board.set board played (some .positive) p = some .positive) :
    boardAfterPlay board .positive played point = none := by
  cases value : board point with
  | none => exact CoalitionBirth.empty_after_other value different
  | some colour =>
      cases colour with
      | positive => exact False.elim (notOwn value)
      | negative =>
          have occupied : Board.set board played (some .positive) point = some .negative := by
            rw [Board.set_other _ _ different]; exact value
          have noLiberty := CoalitionBirth.no_liberty_surrounded occupied boundary
          apply boardAfterPlay_eq_none_of_mem_captured
          unfold capturedStonesAfterPlay
          apply Finset.mem_biUnion.mpr
          exact ⟨point, touching, by
            rw [if_pos ⟨occupied, noLiberty⟩]
            exact occupied_point_mem_groupAt occupied⟩

inductive Shape where
  | leftTwo
  | leftThree
  | leftLower
  | rightTwo
  | rightThree
  deriving DecidableEq

def Shape.foot : Shape → Foot
  | .leftTwo | .leftThree | .leftLower => .left
  | .rightTwo | .rightThree => .right

def Shape.cap : Shape → Point 19
  | .leftTwo | .rightTwo => (0,2)
  | .leftThree | .rightThree => (0,3)
  | .leftLower => (3,2)

def Shape.rooms : Shape → Finset (Finset (Point 19))
  | .leftTwo => {{(0,0), (0,1)}, {(2,0)}}
  | .leftThree => {{(0,0), (0,1), (0,2)}, {(2,0)}}
  | .leftLower => {{(2,0)}, {(2,2)}}
  | .rightTwo => {{(0,0), (0,1)}, {(2,2)}}
  | .rightThree => {{(0,0), (0,1), (0,2)}, {(2,2)}}

def Shape.core (shape : Shape) : Finset (Point 19) := insert shape.cap shape.foot.core
def Shape.geometry? (shape : Shape) : Option (VitalChambers.Geometry 19) :=
  VitalChambers.geometry? shape.core shape.rooms

structure Compiled (shape : Shape) where
  geometry : VitalChambers.Geometry 19
  generated : shape.geometry? = some geometry

def compile? (shape : Shape) : Option (Compiled shape) :=
  match generated : shape.geometry? with
  | none => none
  | some geometry => some ⟨geometry, generated⟩

def compiled : Thunk (Option ((shape : Shape) → Compiled shape)) := ⟨fun _ => do
  let leftTwo ← compile? .leftTwo
  let leftThree ← compile? .leftThree
  let leftLower ← compile? .leftLower
  let rightTwo ← compile? .rightTwo
  let rightThree ← compile? .rightThree
  pure (fun shape => match shape with
    | .leftTwo => leftTwo
    | .leftThree => leftThree
    | .leftLower => leftLower
    | .rightTwo => rightTwo
    | .rightThree => rightThree)⟩

theorem Compiled.fields {shape : Shape} (data : Compiled shape) :
    data.geometry.core = shape.core ∧ data.geometry.rooms = shape.rooms :=
  CorridorPreparation.geometry_fields data.generated

theorem Compiled.accepted {shape : Shape} (data : Compiled shape) :
    acceptsMargin .positive (-341) (VitalChambers.bound data.geometry .positive) = true := by
  obtain ⟨core, rooms⟩ := data.fields
  cases shape <;>
    simp only [VitalChambers.bound, VitalChambers.points, VitalChambers.eyes, core, rooms] <;> decide

end SaturationMonoid.ProcessGame.Go.CriticalKomi.HookSource
