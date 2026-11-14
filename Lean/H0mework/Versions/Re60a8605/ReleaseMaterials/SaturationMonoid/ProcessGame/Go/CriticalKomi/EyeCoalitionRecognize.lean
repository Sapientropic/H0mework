import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.EyeCoalition

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.EyeCoalition

structure Detected {n : Nat} (board : Board n) (colour : Polarity) where
  geometry : Geometry n
  holds : Holds geometry colour board

def candidateEyes {n : Nat} (board : Board n) (core : Finset (Point n)) : Finset (Point n) :=
  Finset.univ.filter (fun eye => board eye = none ∧
    (adjacentPoints eye).Nonempty ∧ adjacentPoints eye ⊆ core)

/-- Every pruning pass consumes only the current source geometry.  A returned
object contains the checked fixed core; fuel exhaustion asserts no game outcome. -/
def recognizeCore? {n : Nat} (board : Board n) (colour : Polarity) :
    Nat → (core : Finset (Point n)) → (∀ point ∈ core, board point = some colour) →
      Option (Detected board colour)
  | 0, _, _ => none
  | fuel + 1, core, occupied =>
      let eyes := candidateEyes board core
      if support : ∀ seed ∈ core, 2 ≤ (touching core eyes seed).card then
        some {
          geometry := {
            core := core
            eyes := eyes
            boundary := by
              intro eye member
              exact (Finset.mem_filter.mp member).2.2.2
            neighbours := by
              intro eye member
              exact (Finset.mem_filter.mp member).2.2.1
            support := support
          }
          holds := ⟨occupied, fun _eye member => (Finset.mem_filter.mp member).2.1⟩
        }
      else
        let next := core.filter (fun seed => 2 ≤ (touching core eyes seed).card)
        recognizeCore? board colour fuel next
          (fun point member => occupied point (Finset.mem_filter.mp member).1)

def recognize? {n : Nat} (board : Board n) (colour : Polarity) : Option (Detected board colour) :=
  recognizeCore? board colour (n * n + 1) (RegionAction.stones board colour)
    (fun _point member => (Finset.mem_filter.mp member).2)

end SaturationMonoid.ProcessGame.Go.CriticalKomi.EyeCoalition
