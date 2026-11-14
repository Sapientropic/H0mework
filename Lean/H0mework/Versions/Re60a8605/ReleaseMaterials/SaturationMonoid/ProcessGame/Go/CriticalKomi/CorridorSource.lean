import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CoalitionBirth

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.Corridor

attribute [local instance 2000] Finset.decidableDforallFinset Finset.decidableDExistsFinset

def point (row column : Nat) : Point 19 := (Fin.ofNat 19 row, Fin.ofNat 19 column)

def rowRange (row first past : Nat) : Finset (Point 19) :=
  Finset.univ.filter (fun p => p.1.val = row ∧ first ≤ p.2.val ∧ p.2.val < past)

def floor (j : Nat) : Finset (Point 19) := rowRange 1 0 (j + 1)

def leftRoom (divider : Nat) : Finset (Point 19) := rowRange 0 0 divider

def rightRoom (j divider : Nat) : Finset (Point 19) := rowRange 0 (divider + 1) j

def frontier (j : Nat) : Finset (Point 19) := rowRange 0 j 19 ∪ rowRange 1 (j + 1) 19

/-- The current wall and both complete original-board frontiers are source
resources. Historical Black occupancy is retained even if those stones died. -/
def Source (frame : Frame 19) (j divider : Nat) : Prop :=
  4 ≤ j ∧ j ≤ 18 ∧ 1 ≤ divider ∧ divider ≤ 3 ∧ divider + 1 < j ∧
  frame.visible.status = .playing ∧ frame.visible.toMove = .negative ∧
  frame.visible.consecutivePasses = 0 ∧
  (∀ p ∈ insert (point 0 divider) (floor j), frame.visible.board p = some .positive) ∧
  (∀ p ∈ leftRoom divider ∪ rightRoom j divider, frame.visible.board p ≠ some .positive) ∧
  (∃ p ∈ leftRoom divider, frame.visible.board p = none) ∧
  (∀ p ∈ frontier j, frame.visible.board p = none) ∧
  Disjoint (frontier j) (CoalitionBirth.retained frame .positive)

instance (frame : Frame 19) (j divider : Nat) : Decidable (Source frame j divider) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def sealedGeometry? (j divider : Nat) : Option (VitalChambers.Geometry 19) :=
  let core := insert (point 0 divider) (floor j)
  if j = 18 then
    VitalChambers.geometry? core {leftRoom divider, rowRange 0 (divider + 1) 19}
  else
    VitalChambers.geometry? (insert (point 0 j) core) {leftRoom divider, rightRoom j divider}

end SaturationMonoid.ProcessGame.Go.CriticalKomi.Corridor
