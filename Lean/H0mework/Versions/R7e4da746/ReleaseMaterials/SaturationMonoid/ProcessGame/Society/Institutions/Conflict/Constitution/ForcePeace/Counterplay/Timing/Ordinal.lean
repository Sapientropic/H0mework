import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Timing.Address

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay

noncomputable section

universe u v w

/-- Choose the first original visit, then the first item at that visit
within a specified family. The same selector is used for a clock fibre. -/
structure FirstVisitItem (Witness : Type w) (within : Witness → Prop) (visit position : Witness → Nat) where
  breach : Witness
  belongs : within breach
  firstVisit : ∀ other, within other → visit breach ≤ visit other
  firstItem : ∀ other, within other → visit other = visit breach → position breach ≤ position other

def firstVisitItem {Witness : Type w} {within : Witness → Prop} (visit position : Witness → Nat)
    (reached : ∃ witness, within witness) : FirstVisitItem Witness within visit position := by
  classical
  let hasVisit (n : Nat) := ∃ witness, within witness ∧ visit witness = n
  have visits : ∃ n, hasVisit n := by
    obtain ⟨witness, here⟩ := reached
    exact ⟨visit witness, witness, here, rfl⟩
  let n := Nat.find visits
  let hasItem (k : Nat) := ∃ witness, (within witness ∧ visit witness = n) ∧ position witness = k
  have items : ∃ k, hasItem k := by
    obtain ⟨witness, atVisit⟩ := Nat.find_spec visits
    exact ⟨position witness, witness, atVisit, rfl⟩
  let found := Classical.choose (Nat.find_spec items)
  obtain ⟨⟨here, atVisit⟩, atItem⟩ := Classical.choose_spec (Nat.find_spec items)
  refine ⟨found, here, ?_, ?_⟩
  · intro other present
    exact atVisit.trans_le (Nat.find_min' visits (show hasVisit (visit other) from ⟨other, present, rfl⟩))
  · intro other present sameVisit
    exact atItem.trans_le (Nat.find_min' items
      (show hasItem (position other) from ⟨other, ⟨present, sameVisit.trans atVisit⟩, rfl⟩))

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community] {CivilView : Type u} {OpponentView : Type v}

namespace Game

variable (game : Game Party Good Port Technology Instrument Community CivilView OpponentView)
  (allowed : Position Party Good Port Technology Instrument CivilView OpponentView →
    Turn → Reparation.Actual.Input Party Good Port Technology Instrument → Prop)
  (plan : CivilPlan Party Good Port Technology Instrument CivilView)

local notation "Hit" => game.JointBreach allowed plan

inductive JointWaitingFrontier
  | unbounded (safe : ∀ limit, game.jointSafeBefore allowed plan limit)
  | finite (first : FirstVisitItem Hit (fun _ => True) JointBreach.tick JointBreach.position)
      (tight : ∀ limit, game.jointSafeBefore allowed plan limit ↔ limit ≤ first.breach.tick)

def jointWaitingFrontier : game.JointWaitingFrontier allowed plan := by
  classical
  by_cases reached : Nonempty Hit
  · let first : FirstVisitItem Hit (fun _ => True) JointBreach.tick JointBreach.position :=
      firstVisitItem JointBreach.tick JointBreach.position ⟨Classical.choice reached, trivial⟩
    refine .finite first (fun limit => ?_)
    rw [game.joint_safety_before_iff_no_earlier_original_breach]
    exact ⟨fun all => all first.breach, fun waits breach => waits.trans (first.firstVisit breach trivial)⟩
  · refine .unbounded (fun limit => (game.joint_safety_before_iff_no_earlier_original_breach allowed plan limit).mpr ?_)
    intro breach
    exact (reached ⟨breach⟩).elim

end Game

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay
