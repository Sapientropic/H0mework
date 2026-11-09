import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Consumers.Native
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Receipt
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Consumers.OriginalService
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Refusal

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.OriginalExchange

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt endAt_append next)
open Reparation.Actual
open Reparation.Actual.Allocation (Position originalItem)

noncomputable section

private theorem origin_rows :
    (Occurrence.originState loss).stack.balances = [(loss, Original.balance)] :=
  Original.at_its_birth_the_whole_ledger_opens_six

private theorem first_rows (answers : ReceiptAnswers Original.seed) :
    prefixRows loss answers [] = [(loss, Original.balance)] := by
  change (Occurrence.writeAfter answers (Occurrence.originState loss) []).stack.balances = _
  rw [Occurrence.writeAfter_nil_balances]
  exact origin_rows

private theorem initial_balance (answers : ReceiptAnswers Original.seed) :
    (Occurrence.balance answers loss []).remaining = 6 := by
  have listed := Occurrence.balance_is_in_the_reached_rows answers loss []
  change (loss, Occurrence.balance answers loss []) ∈ prefixRows loss answers [] at listed
  rw [first_rows] at listed
  exact (congrArg (fun row : _ × Balance => row.2.remaining) (List.mem_singleton.mp listed)).trans Original.balance_six

private theorem one_row (answers : ReceiptAnswers Original.seed) {front : Original.Word}
    (safe : Occurrence.Eligible answers loss front) :
    prefixRows loss answers front = [(loss, Occurrence.balance answers loss front)] := by
  have origins : (prefixRows loss answers front).map Prod.fst = [loss] := by
    rw [Occurrence.reached_origins]
    have stable := Occurrence.eligible_preserves_the_literal_original_loss_inventory
      Original.community answers start start front safe
    rw [stable, ← Occurrence.originState_origins]
    rw [origin_rows]
    rfl
  have width : (prefixRows loss answers front).length = 1 := by
    simpa only [List.length_map, List.length_cons, List.length_nil] using congrArg List.length origins
  obtain ⟨only, written⟩ := List.length_eq_one_iff.mp width
  have listed := Occurrence.balance_is_in_the_reached_rows answers loss front
  change (loss, Occurrence.balance answers loss front) ∈ prefixRows loss answers front at listed
  rw [written] at listed ⊢
  rw [List.mem_singleton.mp listed]

private theorem base_balance_after_production (answers : Bool) :
    (Occurrence.balance (personalReplies answers) loss beforeSale).remaining = 6 := by
  let respond := personalReplies answers
  have first := Occurrence.either_original_partys_refusal_keeps_the_exact_balance_on_the_successor respond loss [] none
    (fun site => by
      have noItem : Boundary.Actual.items (endAt Original.seed (start ++ [])) none = [] :=
        Original.levy_native_has_no_second_item
      exact (Nat.not_lt_zero _ (site.isLt.trans_eq (congrArg List.length noItem))).elim)
  have middle := Occurrence.either_original_partys_refusal_keeps_the_exact_balance_on_the_successor respond loss [none] production
    (fun site => by
      left
      have original : originalItem Original.seed (start ++ [none]) production site ∈
          Boundary.Actual.items (endAt Original.seed (start ++ [none])) production := List.getElem_mem _
      rw [at_original, grow_item] at original
      change personalReplies answers (start ++ [none]) production site false = false
      unfold personalReplies
      rw [List.mem_singleton.mp original])
  have last := Occurrence.either_original_partys_refusal_keeps_the_exact_balance_on_the_successor
    respond loss [none, production] none (fun site => by
      have noItem : Boundary.Actual.items (endAt Original.seed (start ++ [none, production])) none = [] := by
        rw [show start ++ [none, production] = (start ++ [none]) ++ [production] from
          (List.append_assoc start [none] [production]).symm, endAt_append, at_original]
        exact grow_accounting
      exact (Nat.not_lt_zero _ (site.isLt.trans_eq (congrArg List.length noItem))).elim)
  exact (congrArg Balance.remaining (last.trans (middle.trans first))).trans (initial_balance respond)

theorem before_sale_due : dueFor claim (prefixRows loss replies beforeSale) = 6 := by
  rw [one_row replies (first_production_is_safe true)]
  simpa only [dueFor_is_the_keyed_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    if_pos (show loss.key = claim from rfl), add_zero] using base_balance_after_production true

private theorem transfer_does_not_discharge_claim {front : Original.Word} {key : Reparation.Key Bool Bool} {q : ℚ}
    (delivery : DeliveryAt Original.seed Original.community replies (start ++ front) false key q)
    (distinct : claim ≠ key) :
    dueFor claim (prefixRows loss replies (front ++ installment false key q)) =
      dueFor claim (prefixRows loss replies front) := by
  let body : Input Bool Bool Bool Unit Unit := payment false key q
  let state := Occurrence.reached replies loss front
  have accounting : Boundary.Actual.items (endAt Original.seed (start ++ (front ++ [body]))) none = [] := by
    simpa only [List.append_assoc] using delivery.accounting_empty
  have wrote : prefixRows loss replies (front ++ installment false key q) =
      (Settlement.writeTick replies state body).stack.balances := by
    change (Occurrence.writeAfter replies (Occurrence.originState loss) (front ++ ([body] ++ [none]))).stack.balances = _
    rw [← List.append_assoc front [body] [none], Occurrence.writeAfter_snoc_balances,
      a_material_free_tick_keeps_the_original_balances replies _ accounting, Occurrence.writeAfter_snoc_balances]
    rfl
  have kept := writeTick_keeps_rows_without_receipt_or_delivery replies state body delivery.position
    delivery.positions delivery.noDamage (· = claim) (fun read same =>
      Or.inl (delivery.onlyReceipt read (same.symm ▸ distinct)))
  rw [wrote, dueFor_is_the_sum_of_the_original_rows_of_the_key, kept, ← dueFor_is_the_sum_of_the_original_rows_of_the_key]

theorem actual_debt_still_due_after_both_exchange_legs :
    dueFor claim (prefixRows loss replies beforePayment) = 6 :=
  (transfer_does_not_discharge_claim purchase (by decide)).trans
    ((transfer_does_not_discharge_claim sale (by decide)).trans before_sale_due)

theorem reserveOK : 0 ≤ reserve true false := by norm_num [reserve]

theorem funded_after_delivery : CanInstallment loss replies reserve beforePayment false claim 6 := by
  refine ⟨by norm_num, ?_, ?_, restitutionChannel⟩
  · exact actual_debt_still_due_after_both_exchange_legs.ge
  · rw [before_payment_raw]
    decide +kernel

theorem the_same_restitution_is_refused_before_its_credit_arrives :
    ∃ short : (prefixRaw loss beforeSale).stock true false < reserve true false + 6,
      inspectInstallment loss replies reserve beforeSale false claim 6 first_production_ready reserveOK =
        .inl (.shortage short) ∧
      reserve true false + 6 - (prefixRaw loss beforeSale).stock true false = 6 := by
  have short : (prefixRaw loss beforeSale).stock true false < reserve true false + 6 := by
    rw [first_production_raw]
    decide +kernel
  refine ⟨short, ?_, ?_⟩
  · unfold inspectInstallment
    rw [dif_pos (show (0 : ℚ) < 6 by norm_num),
      dif_pos before_sale_due.ge, dif_neg (not_le_of_gt short)]
  · rw [first_production_raw]
    decide +kernel

theorem actual_arrival_enables_the_same_installment :
    ∃ checked, inspectInstallment loss replies reserve beforePayment false claim 6
      before_payment_ready reserveOK = .inr checked :=
  (inspectInstallment_accepts_iff loss replies reserve beforePayment false claim 6
    before_payment_ready reserveOK).mpr funded_after_delivery

def paid : PaidInstallment loss replies reserve beforePayment false claim 6 :=
  writeInstallment loss replies reserve beforePayment false claim 6 safeBeforePayment before_payment_ready
    reserveOK funded_after_delivery

private theorem victim_refuses_at_the_actual_item
    (position : Position Original.seed (start ++ beforePayment) (payment false claim 6)) :
    personalReplies false (start ++ beforePayment) (payment false claim 6) position false = false := by
  have original : originalItem Original.seed (start ++ beforePayment) (payment false claim 6) position ∈
      Boundary.Actual.items (endAt Original.seed (start ++ beforePayment)) (payment false claim 6) :=
    List.getElem_mem _
  rw [paid.delivery.items] at original
  unfold personalReplies
  rw [List.mem_singleton.mp original]
  decide +kernel

theorem a_funded_delivery_cannot_replace_the_victims_original_reply :
    ¬ CanInstallment loss (personalReplies false) reserve beforePayment false claim 6 := by
  intro accepted
  have signed := accepted.channel.victim paid.delivery.position
  rw [victim_refuses_at_the_actual_item] at signed
  contradiction

theorem the_same_original_item_keeps_the_balance_when_its_victim_refuses :
    Occurrence.balance (personalReplies false) loss (beforePayment ++ [payment false claim 6]) =
      Occurrence.balance (personalReplies false) loss beforePayment :=
  Occurrence.either_original_partys_refusal_keeps_the_exact_balance_on_the_successor
    (personalReplies false) loss beforePayment (payment false claim 6)
    (fun position => Or.inl (victim_refuses_at_the_actual_item position))

theorem whole_original_row_is_paid : WholeCleared loss replies closed := by
  have zero := paid.debts claim
  change dueFor claim (prefixRows loss replies closed) =
    dueFor claim (prefixRows loss replies beforePayment) - (if claim = claim then 6 else 0) at zero
  rw [actual_debt_still_due_after_both_exchange_legs, if_pos rfl, sub_self] at zero
  intro row present
  apply every_original_row_is_cleared_when_its_key_has_zero_due claim _ zero row present
  have listed := present
  change row ∈ prefixRows loss replies closed at listed
  have safe : Occurrence.Eligible replies loss closed := paid.eligible
  rw [one_row replies safe] at listed
  rw [List.mem_singleton.mp listed]
  rfl

theorem payment_keeps_the_original_address :
    (prefixRows loss replies closed).map (fun row => row.1.address) = [(2, 0, (false, true, false))] := by
  have safe : Occurrence.Eligible replies loss closed := paid.eligible
  rw [one_row replies safe]
  rfl

theorem payment_preserves_the_production_floor (person good : Bool) :
    reserve person good ≤ (prefixRaw loss closed).stock person good := by
  apply paid.keepsReserve
  intro bearer material
  rw [before_payment_raw]
  cases bearer <;> cases material <;> decide +kernel

private theorem stock_supports_the_original_renewal : TerminalPeace.Supply.Stocked (prefixRaw loss closed) := by
  intro person
  refine ⟨?_, ?_⟩
  · apply le_trans _ (payment_preserves_the_production_floor person false)
    cases person <;> decide +kernel
  · apply le_trans _ (payment_preserves_the_production_floor person true)
    cases person <;> decide +kernel

def offers : ProductionMenu Bool Bool Bool Unit Unit :=
  ⟨[OriginalService.proposal], fun past _ person =>
    decide (18 ≤ (endAt Original.seed past).raw.stock person false ∧
      0 ≤ (endAt Original.seed past).raw.stock person true)⟩

private abbrev offered : ProductionChoice offers := some ⟨0, Nat.zero_lt_one⟩

theorem original_live_entry : ViableEntry loss replies (fun _ => True) closed offers := by
  let reference := OriginalService.choiceAt (start ++ closed) (fun _ => true)
  have referenceApproved := (OriginalService.approval_reads_both_independent_replies loss closed _).mpr (fun _ => rfl)
  have approved : ProductionApproved Original.seed loss closed offered :=
    fun person _ => decide_eq_true (stock_supports_the_original_renewal person)
  have sameInput : productionInput Original.seed loss closed offered =
      productionInput Original.seed loss closed reference :=
    (production_at_an_authorized_cut Original.seed loss closed _ paid.ready approved).trans
      (production_at_an_authorized_cut Original.seed loss closed _ paid.ready referenceApproved).symm
  have samePeople : productionRoster Original.seed loss closed offered =
      productionRoster Original.seed loss closed reference := rfl
  have found : ∃ pilot : Runtime.Viability.Move
      (productionInput Original.seed loss closed offered) (originalRaw loss)
      (productionRoster Original.seed loss closed offered) (prefixRaw loss closed),
      ProductionStartsWith offered pilot.word ∧ Runtime.Viability.Live
        (productionInput Original.seed loss closed offered) (originalRaw loss)
        (productionRoster Original.seed loss closed offered) pilot.next := by
    rw [sameInput, samePeople]
    exact OriginalService.the_original_carriers_fund_the_pilot loss closed (fun _ => true) _
      stock_supports_the_original_renewal paid.ready referenceApproved
  obtain ⟨pilot, starts, live⟩ := found
  exact ⟨⟨Or.inr trivial, paid.eligible⟩, paid.ready, offered, approved, pilot, starts, live⟩

/-- The old native loss is wholly paid from an actual ordered exchange.
The original approved service installs its cofinal run at the same cut. -/
theorem the_ordered_exchange_generates_the_original_peace :
    ∃ word run minimum shortest all fewest,
      source_generated_terminal_peace loss replies (fun _ => True) offers .wholePortfolio =
        .attained word run minimum shortest ∧
      compileWhole loss replies (fun _ => True) offers = .paid word run all fewest ∧
      word.length ≤ closed.length := by
  obtain ⟨word, run, minimum, shortest, all, fewest, attained, written⟩ :=
    both_portfolio_reports_select_the_same_whole_terminal loss replies (fun _ => True) offers
      ⟨closed, original_live_entry, whole_original_row_is_paid⟩
  exact ⟨word, run, minimum, shortest, all, fewest, attained, written,
    fewest closed original_live_entry whole_original_row_is_paid⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.OriginalExchange
