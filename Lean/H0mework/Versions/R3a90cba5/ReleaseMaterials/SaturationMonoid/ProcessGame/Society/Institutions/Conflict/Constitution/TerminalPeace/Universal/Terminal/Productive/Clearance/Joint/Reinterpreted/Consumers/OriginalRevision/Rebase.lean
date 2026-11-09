import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalRevision
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalShortage
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Rebase

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material.Continuation
open FixedPoint.OpenPeace
open FixedPoint.OpenPeace.Network
open FixedPoint.NoFreeProbe (bill)
open FixedPoint.OpenPeace.Network.Runtime.OriginalOrders (quote)
open FixedPoint.OpenPeace.Operational (RecipeConditions checkRecipe chooseRecipe)
open Supply.Consumers (refillWord)
open private start home submit visit posted can_file debit first first_ready initial_ready initial_reads
  from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalRevision
open private tripleMeal readShortage shortageAt actual_roster from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalShortage

noncomputable section

private def afterReview : Original.Raw :=
  FixedPoint.afterCharge revised afterClear refillWord true false [(true, 1/6), (true, 1/6), (true, 1/6)]

private theorem reviewedStock : first.current.physical.raw = afterReview := by
  rw [Runtime.same_physical home namedReplies start (submit 0),
    (visit start 0).same_physical_successor, posted initial_reads initial_ready]
  let funded := (can_file initial_reads initial_ready).budget start.current rfl rfl
  let paid := debit initial_reads initial_ready
  let charge := bill start.lanes.tariff.read (RevisedOrders.proposal home 0).wire
  have native := FixedPoint.charged_native_write start.current.physical start.current.move.paid funded.atCurrent
  have measured := congrArg (fun p : TerminalPeace.Universal.Runtime.Native Bool Bool Bool Unit Unit => p.raw)
    (paid.round.physicalNext.symm.trans native.2.2)
  change paid.round.next.physical.raw = _
  rw [measured]
  change FixedPoint.afterCharge start.current.programme start.current.physical.raw start.current.move.word
    charge.payer charge.port charge.expenses = afterReview
  have word := (start.current.recipe.moveAt_word start.current.physical.raw start.current.reserved).trans initial_ready.2.1
  rw [word, initial_ready.1, actualNetwork.actualStock]
  have terms : (charge.payer, charge.port, charge.expenses) =
      (true, false, [(true, 1/6), (true, 1/6), (true, 1/6)]) := by
    dsimp only [charge]
    rw [initial_reads.1]
    rfl
  rw [show charge.payer = true from congrArg Prod.fst terms,
    show charge.port = false from congrArg (fun t => t.2.1) terms,
    show charge.expenses = _ from congrArg (fun t => t.2.2) terms]
  rfl

private abbrev available :=
  codeFor first.current.programme first_ready.1 first.current.physical.raw

private abbrev offered :=
  tripleMeal first.current.programme first_ready.1 first.current.physical.raw

private abbrev menu := [offered, available]

private theorem availableChecks :
    RecipeConditions first.current.programme (originalRaw loss) first.current.physical.raw (people loss front) available := by
  apply checksFor
  · rw [reviewedStock]
    decide +kernel
  · intro person
    rw [reviewedStock]
    cases person <;> decide +kernel
  · rw [reviewedStock]
    decide +kernel
  · rw [reviewedStock]
    decide +kernel

private theorem checkedShortage (input : Capitalism.Universal.Root.ProgrammeSource.Input Bool Bool Bool Unit Unit)
    (law : input = revised) (raw : Original.Raw) (stock : raw = afterReview) :
    readShortage input law raw (people loss front) = some (2, true, true, 1/2, 1) := by
  subst input raw
  rcases actual_roster with roster | roster <;> rw [roster] <;> decide +kernel

private theorem bound :
    actualNetwork.paid.next.programme.law.duration actualNetwork.paid.next.physical.raw ≤
      first.current.programme.law.duration first.current.physical.raw := by
  have old : actualNetwork.paid.next.programme.law.duration actualNetwork.paid.next.physical.raw = 1 := by
    rw [actualNetwork.paid.sameProgramme.trans actualTrial.revisedProgramme, payment_lands_at_the_actual_stock]
    decide +kernel
  have now : 1 ≤ first.current.programme.law.duration first.current.physical.raw := by
    rw [first_ready.1, reviewedStock]
    decide +kernel
  exact old.le.trans now

/-- The old paid U8 resident supplies the new reserve. The first
registered candidate lacks half a meal; the next pays on that resident. -/
theorem the_original_u8_resident_can_pay_a_replacement_after_a_shortage :
    ∃ replacement,
      Runtime.chooseReplacement first menu home namedReplies = .inr replacement ∧
      replacement.chosen.position.val = 1 ∧
      (∃ issue, checkRecipe first.current.programme (originalRaw loss) first.current.physical.raw
          (people loss front) offered = .inl issue ∧ shortageAt issue = some (2, true, true, 1/2, 1)) ∧
      replacement.next.base.language = first.base.language ∧
      replacement.next.current.ledger.stack.balances = first.current.ledger.stack.balances ∧
      replacement.actual.visit.read.effect.isAccepted = true ∧
      replacement.next.lanes.openPayment.read = first.lanes.openPayment.read := by
  have short := checkedShortage first.current.programme first_ready.1 first.current.physical.raw reviewedStock
  unfold readShortage at short
  cases head : checkRecipe first.current.programme (originalRaw loss) first.current.physical.raw
      (people loss front) offered with
  | inr passed =>
    rw [head] at short
    cases short
  | inl failed =>
    rw [head] at short
    cases tail : checkRecipe first.current.programme (originalRaw loss) first.current.physical.raw
        (people loss front) available with
    | inl unavailable => exact ((unavailable.refutes _ _ _ _ _) availableChecks).elim
    | inr passed =>
      have goes : ∃ replacement, Runtime.chooseReplacement first menu home namedReplies = .inr replacement ∧
          replacement.chosen.position.val = 1 := by
        unfold Runtime.chooseReplacement
        rw [dif_pos bound]
        simp only [menu, chooseRecipe, head, tail]
        exact ⟨_, rfl, rfl⟩
      obtain ⟨replacement, selected, position⟩ := goes
      refine ⟨replacement, selected, position, ⟨failed, rfl, short⟩, replacement.language, ?_, replacement.actual.realWrite, ?_⟩
      · rw [replacement.actualNext]
        exact replacement.actual.rows
      · rw [replacement.keepsLanes]
        exact replacement.reads.keeps first.lanes.openPayment

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer
