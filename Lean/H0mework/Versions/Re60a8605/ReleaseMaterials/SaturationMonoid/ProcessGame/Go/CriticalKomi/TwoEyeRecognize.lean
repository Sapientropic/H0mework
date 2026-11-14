import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEyeClosure

/-! Source-only recognition of two-eye geometry and its executable score guarantee. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEye

def EyeAt {n : Nat} (board : Board n) (core : Finset (Point n)) (eye : Point n) : Prop :=
  board eye = none ∧ (adjacentPoints eye).Nonempty ∧ adjacentPoints eye ⊆ core

instance {n : Nat} (board : Board n) (core : Finset (Point n)) (eye : Point n) :
    Decidable (EyeAt board core eye) := inferInstanceAs (Decidable (_ ∧ _))

structure Detected {n : Nat} (board : Board n) (colour : Polarity) where
  geometry : Geometry n
  holds : Holds geometry colour board

/-- Every certificate field comes from the current group and finite eye tests. -/
def recognizeSeed? {n : Nat} (board : Board n) (colour : Polarity) (seed : Point n) :
    Option (Detected board colour) :=
  if occupied : board seed = some colour then
    let core := groupAt board seed
    match first : (allPoints n).find? (fun eye => decide (EyeAt board core eye)) with
    | none => none
    | some eye₁ =>
        match second : (allPoints n).find?
          (fun eye => decide (eye ≠ eye₁ ∧ EyeAt board core eye)) with
        | none => none
        | some eye₂ =>
            have firstFound := List.find?_some first
            have secondFound := List.find?_some second
            have firstFacts : EyeAt board core eye₁ := of_decide_eq_true firstFound
            have secondFacts : eye₂ ≠ eye₁ ∧ EyeAt board core eye₂ :=
              of_decide_eq_true secondFound
            let geometry : Geometry n := {
              seed := seed
              core := core
              eye₁ := eye₁
              eye₂ := eye₂
              distinct := Ne.symm secondFacts.1
              boundary₁ := firstFacts.2.2
              boundary₂ := secondFacts.2.2.2
              neighbour₁ := firstFacts.2.1
              neighbour₂ := secondFacts.2.2.1
            }
            some ⟨geometry, occupied, Finset.Subset.refl _, firstFacts.1, secondFacts.2.1⟩
  else none

/-- The resulting strategy is generated from the recognized source geometry. -/
def Detected.policy {n : Nat} {board : Board n} {colour : Polarity}
    (detected : Detected board colour) : ExecutablePolicy n :=
  (closure detected.geometry colour).policy

theorem Detected.guarantee {n : Nat} (frame : Frame n) (colour : Polarity)
    (detected : Detected frame.visible.board colour) (scoring : ScoringStatus frame)
    (opponent : ExecutablePolicy n) :
    acceptsMargin colour (bound detected.geometry colour)
      (areaMargin (executePolicies (versus colour detected.policy opponent)
        frame scoring).replay.final.visible.board) = true :=
  against_every_policy detected.geometry colour frame detected.holds scoring opponent

end SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEye
