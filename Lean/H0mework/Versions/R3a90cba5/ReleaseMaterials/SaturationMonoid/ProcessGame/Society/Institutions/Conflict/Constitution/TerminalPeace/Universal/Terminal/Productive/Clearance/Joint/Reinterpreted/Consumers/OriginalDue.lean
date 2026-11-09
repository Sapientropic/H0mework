import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Scheduled.History
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalPayment

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material.Continuation
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Joint.OriginalExchange (claim)
open Supply.Consumers (refillWord)
open TerminalPeace.Supply (personalWord)
open FixedPoint.OpenPeace.Operational (RecipeConditions chooseRecipe)

noncomputable section

def catalogue : Scheduled.MenuAt Bool Bool Bool Unit Unit := by
  classical
  exact fun input raw => if same : input = revised then [codeFor input same raw] else []

theorem catalogue_at (input : ProgrammeSource.Input Bool Bool Bool Unit Unit) (same : input = revised)
    (raw : Original.Raw) : catalogue input raw = [codeFor input same raw] := by
  unfold catalogue
  rw [dif_pos same]

abbrev cycle := payerCut.programme.law.duration payerCut.physical.raw

structure UnsettledEntrance where
  initial : Scheduled.State loss front cycle
  generated : Scheduled.openDue payerCut (catalogue payerCut.programme payerCut.physical.raw) = .inr initial
  original : initial.current = payerCut
  word : initial.recipe.move.word = refillWord

theorem the_original_due_lane_opens_while_six_are_unpaid : Nonempty UnsettledEntrance := by
  have law := actualTrial.revisedProgramme
  have stock := actualTrial.revisedStock
  have paid : RecipeConditions payerCut.programme (originalRaw loss) payerCut.physical.raw (people loss front)
      (codeFor _ law _) := by
    apply checksFor
    · rw [stock]
      decide +kernel
    · intro person
      rw [stock]
      cases person <;> decide +kernel
    · rw [stock]
      decide +kernel
    · rw [stock]
      decide +kernel
  have selected : ∃ initial,
      Scheduled.openDue payerCut (catalogue payerCut.programme payerCut.physical.raw) = .inr initial ∧
        initial.current = payerCut ∧ initial.recipe.move.word = refillWord := by
    unfold Scheduled.openDue
    rw [catalogue_at _ law]
    cases chooseRecipe payerCut.programme (originalRaw loss) payerCut.physical.raw (people loss front)
        [codeFor _ law _] with
    | inr chosen => exact ⟨_, rfl, rfl, chosen.word.trans (by
        have zero : chosen.position = 0 := Fin.ext (Nat.lt_one_iff.mp chosen.position.isLt)
        rw [zero]
        rfl)⟩
    | inl issues => exact ((issues 0).refutes _ _ _ _ _ paid).elim
  obtain ⟨initial, generated, original, word⟩ := selected
  exact ⟨⟨initial, generated, original, word⟩⟩

def originalDue : UnsettledEntrance := Classical.choice the_original_due_lane_opens_while_six_are_unpaid

def offerSix (_ : Nat) (atDue : Current loss front) : Option (Submission atDue) :=
  some (.payment claim 6)

abbrev refusing :=
  Scheduled.history catalogue (reviseReplies true) (signed false) cells allCells originalDue.initial offerSix

abbrev refusingRound :=
  Scheduled.roundAt catalogue (reviseReplies true) (signed false) cells allCells originalDue.initial offerSix

theorem refusal_never_removes_or_delays_the_due_round (n : Nat) :
    (refusing n).current.ledger.stack.balances = [(loss, Original.balance)] := by
  induction n with
  | zero =>
    change originalDue.initial.current.ledger.stack.balances = _
    rw [originalDue.original]
    exact the_original_six_survive_the_new_production.1
  | succ n earlier =>
    let round := refusingRound n
    have denied : ¬ Funding round.due.next.current (signed false) claim 6 := by
      intro paid
      exact Bool.false_ne_true paid.victim
    have kept := Scheduled.refused_funding_keeps_the_paid_due_state
      round.due.next (signed false) claim 6 catalogue cells allCells denied
    change (Scheduled.tryPayment round.due.next (signed false) claim 6 catalogue cells allCells).next.current.ledger.stack.balances = _
    rw [kept.2, round.due.actual, round.due.period.rows]
    exact earlier

theorem the_original_unpaid_six_have_a_cofinal_living_history :
    (∀ n, (refusing n).current.ledger.stack.balances = [(loss, Original.balance)]) ∧
    (∀ n, let due := (refusingRound n).due.period
      due.visit.read.effect.isAccepted = true ∧
        Supply.Period (refusing n).current.programme (originalRaw loss) (refusing n).current.physical.raw
          (people loss front) due.word ∧
        ∀ person ∈ people loss front, ∃ word,
          Supply.Registered (refusing n).current.programme (refusing n).current.physical.raw word ∧
          Supply.Period (refusing n).current.programme (originalRaw loss) (refusing n).current.physical.raw [person] word) ∧
    ∀ start : Nat, ∀ bound : ℚ, ∃ n ≥ start, bound < (refusing n).current.physical.raw.clock :=
  ⟨refusal_never_removes_or_delays_the_due_round, fun n =>
    ⟨(refusingRound n).due.period.accepted, (refusingRound n).due.period.life, (refusingRound n).due.period.exits⟩,
    Scheduled.the_unsettled_clock_is_cofinal catalogue (reviseReplies true) (signed false) cells allCells
      originalDue.initial offerSix⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer
