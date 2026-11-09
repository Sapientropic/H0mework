import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalDue
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalNetwork

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Joint.OriginalExchange (claim)
open Supply.Consumers (refillWord)
open FixedPoint.OpenPeace.Operational (RecipeConditions)
open FixedPoint.OpenPeace.Network
open FixedPoint.OpenPeace.Network.Runtime.OriginalOrders (quote)
open RevisedOrders (openPayment)
open private original_need_cut from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalSource

noncomputable section

private abbrev due := Scheduled.writeDue originalDue.initial
private abbrev reached := due.next
private def afterDue : Original.Raw := revised.law.next afterTrial refillWord
private def afterSigned : Original.Raw := deliveredRaw afterDue claim 6

private theorem dueLaw : reached.current.programme = revised :=
  due.period.programmeNext.trans ((congrArg Current.programme originalDue.original).trans actualTrial.revisedProgramme)

private theorem dueStock : reached.current.physical.raw = afterDue := by
  rw [due.actual, due.period.exactStock]
  change originalDue.initial.current.programme.law.next originalDue.initial.current.physical.raw
    (originalDue.initial.recipe.moveAt _ originalDue.initial.reserve).word = afterDue
  rw [originalDue.initial.recipe.moveAt_word, originalDue.word, originalDue.original,
    actualTrial.revisedProgramme, actualTrial.revisedStock]
  rfl

private theorem dueRows : reached.current.ledger.stack.balances = [(loss, Original.balance)] := by
  rw [due.actual, due.period.rows, originalDue.original]
  exact the_original_six_survive_the_new_production.1

private theorem dueSix : liveBalance reached.current claim = 6 := by
  unfold liveBalance
  rw [dueRows]
  exact the_original_six_survive_the_new_production.1 ▸ the_original_six_survive_the_new_production.2

private theorem signedAfterDue : Funding reached.current (signed true) claim 6 := by
  refine ⟨Bool.false_ne_true, by norm_num, dueSix.ge, ?_, rfl, rfl, ?_⟩
  · unfold request purpose
    rw [dueLaw, dueStock]
    decide +kernel
  · intro person good
    unfold requiredAt
    rw [dueLaw, dueStock, original_need_cut]
    cases person <;> cases good <;> decide +kernel

private theorem signedStock : deliveredRaw reached.current.physical.raw claim 6 = afterSigned :=
  congrArg (fun raw => deliveredRaw raw claim 6) dueStock

private theorem nextRecipe (input : ProgrammeSource.Input Bool Bool Bool Unit Unit) (law : input = revised)
    (raw : Original.Raw) (stock : raw = afterSigned) :
    RecipeConditions input (originalRaw loss) raw (people loss front) (codeFor input law raw) := by
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

private theorem continuedAfterDue :
    cycle ≤ reached.current.programme.law.duration (deliveredRaw reached.current.physical.raw claim 6) ∧
    ∃ i : Fin (catalogue reached.current.programme (deliveredRaw reached.current.physical.raw claim 6)).length,
      RecipeConditions reached.current.programme (originalRaw loss) (deliveredRaw reached.current.physical.raw claim 6)
        (people loss front) (catalogue reached.current.programme (deliveredRaw reached.current.physical.raw claim 6))[i] := by
  constructor
  · unfold cycle
    rw [dueLaw, signedStock, actualTrial.revisedProgramme, actualTrial.revisedStock]
    decide +kernel
  · let input := reached.current.programme
    let raw := deliveredRaw reached.current.physical.raw claim 6
    have present : codeFor input dueLaw raw ∈ catalogue input raw := by
      rw [catalogue_at input dueLaw]
      exact List.mem_cons_self
    obtain ⟨i, exactCode⟩ := List.mem_iff_get.mp present
    refine ⟨i, ?_⟩
    change RecipeConditions input (originalRaw loss) raw (people loss front) ((catalogue input raw).get i)
    rw [exactCode]
    exact nextRecipe input dueLaw raw signedStock

private abbrev ordered :=
  Scheduled.roundAt catalogue (reviseReplies true) (signed true) cells allCells originalDue.initial offerSix 0

private def installedCode (paid : PaidWrite reached.current (signed true) claim 6) :=
  codeFor _ (paid.sameProgramme.trans dueLaw) paid.next.physical.raw

/-- A signature arriving after the first due period buys the actual
six at that period's successor. The original cleared address and both
parties' newly paid stock then enter the existing signed network. -/
theorem a_later_original_signature_clears_and_enters_the_network :
    ∃ (paid : PaidWrite reached.current (signed true) claim 6)
      (network : NetworkOpening paid.next quote Runtime.OriginalOrders.payment openPayment (installedCode paid).production),
      ordered.motion.event = some (.paid paid) ∧ ordered.next.current = paid.next ∧
      paid.receipt.quantity = 6 ∧ paid.receipt.item.before = afterDue ∧
      (∀ item ∈ paid.visit.read.effect.execution.items, ∀ key,
        Reparation.loss reached.current.programme.law Original.community item key = 0) ∧
      openNetwork paid.next quote Runtime.OriginalOrders.payment openPayment (installedCode paid) = .inr network ∧
      network.state.current.ledger.stack.balances.map Prod.fst = [loss] ∧
      ∀ row ∈ network.state.current.ledger.stack.balances, row.2.remaining = 0 := by
  obtain ⟨paid, exactEvent, actual⟩ :=
    Scheduled.tryPayment_writes_when_funded_and_continued reached (signed true) claim 6 catalogue cells allCells
      signedAfterDue (.inr continuedAfterDue)
  have addresses : paid.next.ledger.stack.balances.map Prod.fst = [loss] := by
    rw [paid.next.origins, ← reached.current.origins, dueRows]
    rfl
  have zero := paid.balances claim
  rw [if_pos rfl, dueSix, sub_self] at zero
  have cleared : ∀ row ∈ paid.next.ledger.stack.balances, row.2.remaining = 0 := by
    intro row listed
    have origin : row.1 = loss := List.mem_singleton.mp (addresses ▸ List.mem_map_of_mem (f := Prod.fst) listed)
    exact every_original_row_is_cleared_when_its_key_has_zero_due claim _ zero row listed
      (congrArg (fun origin => origin.key) origin)
  obtain ⟨network, written⟩ := opens_network_at_the_original_resident paid.next quote
    Runtime.OriginalOrders.payment openPayment (installedCode paid) cleared
    (nextRecipe _ (paid.sameProgramme.trans dueLaw) _ (paid.stock.trans signedStock))
  exact ⟨paid, network, exactEvent, actual, paid.amount,
    (congrArg (fun item : ExecutionItem Bool Bool Bool Unit Unit => item.before) paid.item).trans dueStock,
    paid.noDamage, written, (congrArg (List.map Prod.fst) network.rows).trans addresses, network.paid⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer
