import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Check
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Incidence
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Balance.Check
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Retiming
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Resigning

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Exit.AutonomousProduction (SelfOperation)
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material (ActualAndIndependent withoutControllerConsents)
open Capitalism.Universal.Abolition.Material.Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem OwnOperation.stable_request {request : Request Party Good Port Technology Instrument}
    (owned : OwnOperation request) : Balance.StableRequest request := by
  cases operation : request.operation <;>
    simp_all [OwnOperation, SelfOperation, Balance.StableRequest,
      Capitalism.Universal.Abolition.Root.Settlement.NonFinancialRequest]

variable
  {law : RawLaw Party Good Port Technology Instrument} {roster : List Party}
  {item : ExecutionItem Party Good Port Technology Instrument}

omit [DecidableEq Instrument] in
theorem OwnItem.actual_debit_is_own (own : OwnItem law roster item)
    (lot : (Party × Good) × ℚ) (original : lot ∈ law.actualDebit item.before item.request) :
    lot.1.1 = item.request.signer := by
  rw [RawLaw.actualDebit, if_pos own.valid] at original
  have self := own.operation
  cases operation : item.request.operation with
  | produce person | transfer person _ _ =>
    simp only [OwnOperation, SelfOperation, operation] at self
    simp only [RawLaw.debit, operation, locate, List.mem_map] at original
    obtain ⟨entry, _, rfl⟩ := original
    exact self.symm
  | use person goods purpose =>
    simp only [OwnOperation, SelfOperation, operation] at self
    simp only [RawLaw.debit, operation, locate, List.mem_map] at original
    obtain ⟨entry, _, rfl⟩ := original
    exact self.1.symm
  | present => simp only [RawLaw.debit, operation, List.not_mem_nil] at original
  | _ => simp only [OwnOperation, SelfOperation, operation] at self

omit [DecidableEq Instrument] in
theorem OwnItem.actual_credit_nonnegative (own : OwnItem law roster item) (person : Party) (good : Good) :
    0 ≤ flowAt (law.actualCredit item.before item.request) person good := by
  rw [RawLaw.actualCredit, if_pos own.valid]
  exact amount_nonnegative _ own.valid.2.2.2.2.1 _

omit [DecidableEq Instrument] in
theorem OwnItem.other_debit_is_zero (own : OwnItem law roster item)
    (person : Party) (good : Good) (other : person ≠ item.request.signer) :
    flowAt (law.actualDebit item.before item.request) person good = 0 := by
  apply amount_zero_of_absent
  intro lot listed same
  exact other ((congrArg Prod.fst same).symm.trans (own.actual_debit_is_own lot listed))

theorem OwnItem.other_stock_nondecreasing (own : OwnItem law roster item)
    (person : Party) (good : Good) (other : person ≠ item.request.signer) :
    item.before.stock person good ≤ (law.step item.before item.request).stock person good := by
  have balanced := law.material_step_balance item.before item.request person good
  rw [own.other_debit_is_zero person good other, add_zero] at balanced
  rw [balanced]
  exact le_add_of_nonneg_right (own.actual_credit_nonnegative person good)

omit [DecidableEq Instrument] in
theorem OwnItem.opens_no_coercive_loss {Community : Type} [DecidableEq Community]
    (own : OwnItem law roster item) (community : Party → Community) (address : Reparation.Key Party Good) :
    Reparation.loss law community item address = 0 := by
  unfold Reparation.loss
  split
  · rename_i cross
    have other : address.1 ≠ item.request.signer := by
      intro same
      exact cross.1 (congrArg community (same.trans cross.2.1))
    rw [own.other_debit_is_zero address.1 address.2.2 other, zero_sub,
      max_eq_left (neg_nonpos.mpr (own.actual_credit_nonnegative address.1 address.2.2))]
  · rfl

theorem OwnItem.keeps_original_claims_technology_and_time (own : OwnItem law roster item) :
    let next := law.step item.before item.request
    next.claims = item.before.claims ∧ next.technology = item.before.technology ∧
      next.clock = item.before.clock ∧ next.round = item.before.round := by
  exact Balance.stable_execution_coordinates law item.before 0 [item.request] (by
    intro request listed
    rw [List.mem_singleton.mp listed]
    exact own.operation.stable_request)

variable {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {origin current : RawCurrent Party Good Technology Instrument}
  {word : RawEvent Party Good Port Technology Instrument}

theorem Period.toActualAndIndependent (paid : Period input origin current roster word) :
    ActualAndIndependent input current word := by
  intro item listed
  have owned := paid.own item listed
  have ownConsent : withoutControllerConsents item.request = item.request :=
    Request.resign_self _ owned.noConsent
  refine ⟨owned.valid, ownConsent.symm ▸ owned.valid, fun lot original _ => ?_⟩
  apply owned.actual_debit_is_own lot
  rwa [RawLaw.actualDebit, if_pos owned.valid]

theorem Period.every_personal_item_is_its_original_bearer (person : Party)
    (paid : Period input origin current [person] word) :
    ∀ item ∈ input.law.rawItems current word, item.request.signer = person :=
  fun item listed => List.mem_singleton.mp (paid.own item listed).member

theorem Period.stable_word (paid : Period input origin current roster word) : Balance.StableWord word := by
  intro request listed
  have actual : request ∈ (input.law.rawItems current word).map ExecutionItem.request := by
    rwa [RawLaw.rawItems, RawLaw.inventory_requests_exact]
  obtain ⟨item, present, rfl⟩ := List.mem_map.mp actual
  exact (paid.own item present).operation.stable_request

theorem Period.exact_clock (paid : Period input origin current roster word) :
    (input.law.next current word).clock = current.clock + input.law.duration current := by
  change current.clock + max 0 (input.law.duration current) = _
  rw [max_eq_right paid.positiveClock.le]

theorem Period.exact_successor (paid : Period input origin current roster word) :
    input.law.next current word =
      (current.addReserve (Balance.gain input.law current word)).retime
        (current.clock + input.law.duration current) (current.round + 1) := by
  unfold RawLaw.next
  rw [Balance.generated_gain_endpoint input.law current word paid.stable_word,
    max_eq_right paid.positiveClock.le]
  rfl

theorem Period.exact_accumulating_successor (paid : Period input origin current roster word)
    (accumulating : Balance.FiniteChecks .accumulating input.law current word) :
    input.law.next current word =
      (current.addReserve (Balance.gain input.law current word)).retime
        (current.clock + input.law.duration current) (current.round + 1) ∧
    ∀ person good, 0 ≤ Balance.gain input.law current word person good :=
  ⟨paid.exact_successor, (Balance.checked_productive_period input.law current word accumulating).2⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply
