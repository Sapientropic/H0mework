import H0mework.Versions.R71cb159f.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Revision.Consumers.Protected

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.OriginalConsumer

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Reparation.Actual (Occurrence)
open Clearance Joint
open Joint.OriginalExchange
open Joint.SourceReserve Joint.SourceReserve.OriginalConsumer
open private Endpoint.after Endpoint.trans Endpoint.at prependCleared from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Revision.Portfolio

noncomputable section

abbrev paidPrefix : Original.Word := directWord

theorem paid_raw : prefixRaw loss paidPrefix = Original.snapshot 135 107 :=
  finalRaw

private theorem cap_is_six : maximumInstallment loss replies beforeSale claim = 6 :=
  the_original_clearing_reads_the_complete_six_from_new_inventory true

theorem all_paid_positions_keep_needs (word : Original.Word) (initial : word.IsPrefix paidPrefix) :
    ProtectsNeeds loss word :=
  every_direct_payment_material_position_keeps_the_source_needs.of_prefix loss initial

private theorem just_one_key : originalKeys loss = [claim] := by
  have rows : (Occurrence.originState loss).stack.balances = [(loss, Original.balance)] :=
    Original.at_its_birth_the_whole_ledger_opens_six
  unfold originalKeys
  rw [rows]
  rfl

private theorem delivery_port : deliveryPort loss beforeSale claim = false := by
  unfold deliveryPort
  rw [Conflict.Consumers.Evolving.sourceInput]
  rfl

private theorem exact_debit : afterDebit loss replies beforeSale claim = paidPrefix := by
  unfold afterDebit
  rw [cap_is_six, delivery_port]

private def endpointIs {front : Original.Word} {pending : List (Reparation.Key Bool Bool)}
    (expected : Original.Word) (result : PortfolioResult loss replies front pending) : Prop :=
  match result with
  | .complete landed _ => landed.word = expected
  | .stopped _ _ _ _ => False

private theorem the_selected_single_payment_is_the_complete_portfolio
    (front : Original.Word) (key : Reparation.Key Bool Bool)
    (safe : Occurrence.Eligible replies loss front)
    (keepsNeeds : ProtectsNeeds loss front) (ready : ReadyEntry loss front)
    (paid : generatedPaid loss replies front key)
    (held : ProtectsNeeds loss (afterDebit loss replies front key))
    (selected : compileProtectedPayment loss replies front key (deliveryPort loss front key) safe ready =
      .written paid held)
    (unpaid : ¬ liveDue loss replies front key = 0)
    (zero : liveDue loss replies (afterDebit loss replies front key) key = 0) :
    endpointIs (afterDebit loss replies front key) (scanOriginalKeys loss replies [key] front safe keepsNeeds ready) := by
  delta scanOriginalKeys
  dsimp only [List.brecOn, scanOriginalKeys._f]
  simp only [dif_neg unpaid, selected]
  have remains : liveDue loss replies (Endpoint.after loss replies front key paid held).word key = 0 := zero
  simp only [dif_pos remains, prependCleared, Endpoint.trans, Endpoint.at, endpointIs]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem the_single_original_key_clears
    (safe : Occurrence.Eligible replies loss beforeSale)
    (keepsNeeds : ProtectsNeeds loss beforeSale) (ready : ReadyEntry loss beforeSale) :
    endpointIs paidPrefix (clearOriginalPortfolio loss replies beforeSale safe keepsNeeds ready) := by
  have fits : InspectablePayment loss replies beforeSale claim (deliveryPort loss beforeSale claim)
      (maximumInstallment loss replies beforeSale claim) := by
    rw [cap_is_six, delivery_port]
    exact ⟨exactFunding, all_paid_positions_keep_needs paidPrefix List.prefix_rfl⟩
  obtain ⟨paid, held, selected⟩ :=
    (compileProtectedInstallment_pays_iff loss replies beforeSale claim (deliveryPort loss beforeSale claim)
      (maximumInstallment loss replies beforeSale claim) safe ready).mpr fits
  have zero : liveDue loss replies (afterDebit loss replies beforeSale claim) claim = 0 := by
    rw [liveDue, paid.debts, before_sale_due, cap_is_six, if_pos rfl, sub_self]
  have initially : ¬ liveDue loss replies beforeSale claim = 0 := by
    rw [liveDue, before_sale_due]
    norm_num
  change endpointIs paidPrefix (scanOriginalKeys loss replies (originalKeys loss) beforeSale safe keepsNeeds ready)
  rw [just_one_key, ← exact_debit]
  exact the_selected_single_payment_is_the_complete_portfolio beforeSale claim safe keepsNeeds ready
    paid held selected initially zero

set_option maxHeartbeats 1000000 in
theorem the_native_portfolio_pays_six
    (safe : Occurrence.Eligible replies loss (openingDrain loss))
    (nonempty : [grow] ≠ []) :
    ∃ started landed closed,
      clearAfterProduction loss replies (openingDrain loss) [grow] safe nonempty = .inr started ∧
        started.clearance = .complete landed closed ∧ landed.word = paidPrefix := by
  obtain ⟨production, _⟩ := first_production_is_written true
  obtain ⟨actual, written⟩ :=
    (inspectProduction_passes_iff replies loss (openingDrain loss) [grow]).mpr
      (original_drain_exact.symm ▸ production)
  have front : openingDrain loss ++ Quantities.Execution.primitiveScript [grow] = beforeSale := by
    rw [original_drain_exact]
    rfl
  unfold clearAfterProduction
  rw [written]
  cases checked : inspectNeeds loss (openingDrain loss ++ Quantities.Execution.primitiveScript [grow]) with
  | inl short =>
    exact (short.refutes loss _ (all_paid_positions_keep_needs _ (front.symm ▸ List.prefix_append _ _))).elim
  | inr stocked =>
    let portfolio := clearOriginalPortfolio loss replies _ (actual.eligibility safe) stocked.down (actual.ready nonempty)
    have same (word : Original.Word) (exact : word = beforeSale)
        (admitted : Occurrence.Eligible replies loss word) (reserve : ProtectsNeeds loss word)
        (ready : ReadyEntry loss word) :
        endpointIs paidPrefix (clearOriginalPortfolio loss replies word admitted reserve ready) := by
      subst word
      exact the_single_original_key_clears _ _ _
    have exactWord : endpointIs paidPrefix portfolio := same _ front _ _ _
    cases result : portfolio with
    | stopped => rw [result] at exactWord; exact exactWord.elim
    | complete landed closed =>
      rw [result] at exactWord
      exact ⟨⟨actual, portfolio⟩, landed, closed, rfl, result, exactWord⟩

end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "the_native_portfolio_pays_six"

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.OriginalConsumer
