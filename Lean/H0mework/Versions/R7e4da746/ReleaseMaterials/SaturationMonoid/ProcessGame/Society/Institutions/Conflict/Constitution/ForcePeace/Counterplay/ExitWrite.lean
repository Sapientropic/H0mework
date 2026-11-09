import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Ledger

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence (ExitAtCut)

noncomputable section

universe u v

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community] {CivilView : Type u} {OpponentView : Type v}

namespace Game

variable (game : Game Party Good Port Technology Instrument Community CivilView OpponentView)
  (plan : CivilPlan Party Good Port Technology Instrument CivilView)
  (opponent : List OpponentView → Reparation.Actual.Input Party Good Port Technology Instrument)
  (arbitrate : Nat → Root.Cut Party Good Port Technology Instrument → Turn)

/-- Exercise the already checked exit at the chosen cut, on its existing
ledger. Evaluating the option does not spend that exit on the main play. -/
def takeExit (tick : Nat) (_checked : game.exitGoodAt plan opponent arbitrate tick) :=
  Reparation.Actual.publishAfter (game.ledger plan.submit opponent arbitrate tick)
    (game.exitAt plan opponent arbitrate tick)

theorem the_independent_exit_consumes_the_original_ledger_at_every_safe_cut
    (safe : game.Safe plan opponent arbitrate) (tick : Nat) :
    let past := game.prefixAt plan opponent arbitrate tick
    let exit := game.exitAt plan opponent arbitrate tick
    let written := game.takeExit plan opponent arbitrate tick (safe tick).2
    ExitAtCut game.seed game.command game.community (Quantities.Execution.endAt game.seed past) exit ∧
      Quantities.Recorded game.seed (past ++ exit) ∧
      written.next = Reparation.Actual.run game.seed game.community (past ++ exit) ∧
      ∀ victim ∈ Reparation.Actual.originalLosses game.seed game.community past,
        ∃ balance, ∃ row, written.next.read row = .inr (victim, balance) := by
  refine ⟨?_, (game.takeExit plan opponent arbitrate tick (safe tick).2).recorded, ?_, ?_⟩
  · rw [← game.play_is_the_original_current plan.submit opponent arbitrate tick]
    exact (safe tick).2
  · exact Reparation.Actual.publication_consumes_the_retained_visit _ _ _ _
  · exact Reparation.Actual.publication_keeps_every_previous_loss _ _ _ _

end Game

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay
