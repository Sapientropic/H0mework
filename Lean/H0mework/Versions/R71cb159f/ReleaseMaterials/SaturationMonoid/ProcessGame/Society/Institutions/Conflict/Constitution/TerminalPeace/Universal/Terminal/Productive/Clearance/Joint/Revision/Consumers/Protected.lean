import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Revision.Portfolio
import H0mework.Versions.R71cb159f.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Revision.Consumers.Original
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Consumers.Frontier.Inventory

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.SourceReserve.OriginalConsumer

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt endAt_append primitiveScript)
open Reparation.Actual (Occurrence)
open Joint.OriginalExchange
open Conflict.Consumers.Evolving (C R compact sourceInput)
open private beforeSalePays from H0mework.Versions.R71cb159f.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Revision.Consumers.Original
open private birth_raw growth_trace body_same_stock physical_singleton grow_body_cut
  body_keeps_delivery trace_after_delivery from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Consumers.Frontier.Inventory

noncomputable section

private theorem quantitySix : maximumInstallment loss replies beforeSale claim = 6 :=
  the_original_clearing_reads_the_complete_six_from_new_inventory true

theorem exactFunding :
    CanInstallment loss replies (reserveAt loss beforeSale) beforeSale false claim 6 :=
  quantitySix ▸ beforeSalePays

def directDelivery : DeliveryAt Original.seed Original.community replies
    (Occurrence.history loss ++ beforeSale) false claim 6 :=
  executeDelivery first_production_ready.1 first_production_ready.2 exactFunding.positive
    ((le_add_of_nonneg_left (reserveAt_nonnegative _ _ _ _)).trans exactFunding.stock) exactFunding.channel

abbrev directWord := beforeSale ++ installment false claim 6

theorem finalRaw : prefixRaw loss directWord = Original.snapshot 135 107 := by
  have raw := directDelivery.raw
  rw [List.append_assoc] at raw
  change prefixRaw loss directWord = deliveredRaw (prefixRaw loss beforeSale) claim 6 at raw
  rw [raw, first_production_raw]
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;> decide +kernel
  · rfl
  · rfl
  · rfl
  · rfl

private abbrev required := atRaw Original.seed.native.input.law (originalRaw loss)

theorem actual_need_floor (raw : Original.Raw) (person good : Bool) :
    atRaw Original.seed.native.input.law (originalRaw loss) raw person good = if good then 1 else 0 := by
  rw [sourceInput]
  change max 0 (max (amount Bool [(true, 1)] good) (amount Bool [(true, 1)] good)) +
      max 0 (max (amount Bool [] good) (amount Bool [] good)) = _
  cases good <;> decide +kernel

private theorem snapshot_safe (victim debtor : ℚ) (victimOK : 0 ≤ victim) (debtorOK : 0 ≤ debtor)
    (person good : Bool) :
    required (Original.snapshot victim debtor) person good ≤ (Original.snapshot victim debtor).stock person good := by
  change atRaw Original.seed.native.input.law (originalRaw loss) (Original.snapshot victim debtor) person good ≤ _
  rw [actual_need_floor]
  cases good
  · cases person
    · exact victimOK
    · exact debtorOK
  · exact le_rfl

private theorem opening_safe (n : Nat) (inside : n ≤ directWord.length) (person good : Bool) :
    required (prefixRaw loss (directWord.take n)) person good ≤ (prefixRaw loss (directWord.take n)).stock person good := by
  have width : n ≤ 5 := inside
  interval_cases n
  · rw [show directWord.take 0 = ([] : Original.Word) from rfl, birth_raw]
    exact snapshot_safe _ _ (by norm_num) (by norm_num) person good
  · rw [show directWord.take 1 = ([none] : Original.Word) from rfl]
    change required (endAt Original.seed (start ++ [none])).raw person good ≤
      (endAt Original.seed (start ++ [none])).raw.stock person good
    rw [at_original, Original.cut_raw]
    exact snapshot_safe _ _ (by norm_num) (by norm_num) person good
  · rw [show directWord.take 2 = ([none] ++ [some (.primitive grow)] : Original.Word) from rfl,
      body_same_stock [none] grow growth_trace]
    change required (prefixRaw loss beforeSale) person good ≤ (prefixRaw loss beforeSale).stock person good
    rw [first_production_raw]
    exact snapshot_safe _ _ (by norm_num) (by norm_num) person good
  · rw [show directWord.take 3 = beforeSale from rfl, first_production_raw]
    exact snapshot_safe _ _ (by norm_num) (by norm_num) person good
  · rw [show directWord.take 4 = (beforeSale ++ [payment false claim 6]) from rfl,
      body_keeps_delivery directDelivery, finalRaw]
    exact snapshot_safe _ _ (by norm_num) (by norm_num) person good
  · rw [show directWord.take 5 = directWord from rfl, finalRaw]
    exact snapshot_safe _ _ (by norm_num) (by norm_num) person good

private theorem item_safe {source target : C} {request : R}
    (trace : Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime.Trace source [request] target)
    (items : Boundary.Actual.items source (some (.primitive request)) = [⟨0, source.raw, request⟩])
    (item : Original.Item) (present : item ∈ Boundary.Actual.items source (some (.primitive request)))
    (person good : Bool)
    (before : required source.raw person good ≤ source.raw.stock person good)
    (after : required target.raw person good ≤ target.raw.stock person good) :
    required item.before person good ≤ item.before.stock person good ∧
      (let raw := (Boundary.Actual.materialLaw source).step item.before item.request
       required raw person good ≤ raw.stock person good) := by
  rw [items] at present
  rcases List.mem_singleton.mp present with rfl
  refine ⟨before, ?_⟩
  dsimp only
  rw [(physical_singleton trace).2]
  exact after

private theorem literal_item_safe (n : Nat) (inside : n < directWord.length) (item : Original.Item)
    (present : item ∈ Boundary.Actual.items (endAt Original.seed (start ++ directWord.take n)) directWord[n])
    (person good : Bool) :
    required item.before person good ≤ item.before.stock person good ∧
      (let raw := (Boundary.Actual.materialLaw (endAt Original.seed (start ++ directWord.take n))).step item.before item.request
       required raw person good ≤ raw.stock person good) := by
  have width : n ≤ 4 := Nat.le_of_lt_succ inside
  have safe (j : Nat) (h : j ≤ directWord.length) := opening_safe j h person good
  interval_cases n
  · rw [show directWord.take 0 = ([] : Original.Word) from rfl, show directWord[0] = none from rfl] at present
    exact (List.not_mem_nil (Original.levy_native_has_no_second_item ▸ present)).elim
  · rw [show directWord.take 1 = ([none] : Original.Word) from rfl, show directWord[1] = production from rfl] at present
    rw [show directWord.take 1 = ([none] : Original.Word) from rfl]
    have items : Boundary.Actual.items (endAt Original.seed (start ++ [none])) production =
        [⟨0, (endAt Original.seed (start ++ [none])).raw, grow⟩] := by
      rw [at_original, grow_item]
    exact item_safe growth_trace items item present person good (safe 1 (by decide)) (safe 3 (by decide))
  · rw [show directWord.take 2 = ([none, production] : Original.Word) from rfl,
      show directWord[2] = none from rfl, grow_body_cut, grow_accounting] at present
    exact (List.not_mem_nil present).elim
  · rw [show directWord.take 3 = beforeSale from rfl, show directWord[3] = payment false claim 6 from rfl] at present
    rw [show directWord.take 3 = beforeSale from rfl]
    exact item_safe (trace_after_delivery directDelivery) directDelivery.items item present person good
      (safe 3 (by decide)) (safe 5 (by decide))
  · rw [show directWord.take 4 = (beforeSale ++ [payment false claim 6]) from rfl,
      show directWord[4] = none from rfl, ← List.append_assoc start beforeSale [payment false claim 6],
      directDelivery.accounting_empty] at present
    exact (List.not_mem_nil present).elim

theorem every_direct_payment_material_position_keeps_the_source_needs :
    ProtectsNeeds loss directWord := by
  intro cut listed person good
  obtain ⟨n, within, h⟩ := List.mem_flatMap.mp listed
  have opening : n ≤ directWord.length := Nat.le_of_lt_succ (List.mem_range.mp within)
  rcases List.mem_cons.mp h with same | later
  · subst cut
    exact opening_safe n opening person good
  · split at later
    · rename_i inside
      obtain ⟨item, original, exactRead⟩ := List.mem_flatMap.mp later
      rcases List.mem_cons.mp exactRead with same | last
      · subst cut
        exact (literal_item_safe n inside item original person good).1
      · rw [List.mem_singleton] at last
        subst cut
        exact (literal_item_safe n inside item original person good).2
    · exact (List.not_mem_nil later).elim

theorem the_guarded_original_compiler_writes_the_six_unit_payment :
    ∃ paid keepsNeeds,
      compileProtectedPayment loss replies beforeSale claim false (first_production_is_safe true)
        first_production_ready = .written paid keepsNeeds ∧ paid.delivery.receipt.quantity = 6 := by
  have inventory : ProtectsNeeds loss (beforeSale ++
      installment false claim (maximumInstallment loss replies beforeSale claim)) :=
    quantitySix.symm ▸ every_direct_payment_material_position_keeps_the_source_needs
  obtain ⟨paid, keepsNeeds, compiled⟩ :=
    (compileProtectedInstallment_pays_iff loss replies beforeSale claim false _
      (first_production_is_safe true) first_production_ready).mpr ⟨beforeSalePays, inventory⟩
  exact ⟨paid, keepsNeeds, compiled, paid.delivery.exactQuantity.trans quantitySix⟩

theorem the_guarded_payment_clears_the_literal_original_address :
    ∃ paid keepsNeeds,
      compileProtectedPayment loss replies beforeSale claim false (first_production_is_safe true)
        first_production_ready = .written paid keepsNeeds ∧
      let next := paidNext loss replies [none] [grow] false claim paid
      next.stack.balances.map Prod.fst = [Original.occurrence] ∧
        dueFor claim next.stack.balances = 0 := by
  obtain ⟨actual, _⟩ := first_production_is_written true
  obtain ⟨paid, kept, written, _⟩ := the_guarded_original_compiler_writes_the_six_unit_payment
  have exact := the_payment_keeps_all_origins_and_consumes_the_selected_due loss replies [none] [grow]
    false claim (drain_safe true) actual paid
  refine ⟨paid, kept, written, ?_, ?_⟩
  · rw [exact.1]
    change (Reparation.Actual.run Original.seed Original.community Original.born).stack.balances.map Prod.fst = _
    rw [Original.at_its_birth_the_whole_ledger_opens_six]
    rfl
  · have amount := exact.2.1
    change _ = dueFor claim (prefixRows loss replies beforeSale) - maximumInstallment loss replies beforeSale claim at amount
    rw [amount, before_sale_due, quantitySix, sub_self]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.SourceReserve.OriginalConsumer
