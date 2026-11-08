import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Opening
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.InstrumentProjection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Financial.Family Financial.Family.BalanceConservation
open Financial.BalanceConservation (issue_readout_nonissue movement_readout_nonmovement payment_readout_exists)

theorem OpeningReady.compatible {scope : Scope} {before : Current} {account : Finance.Account}
    (ready : OpeningReady scope before account) (input : Finance.Input)
    (sameLaw : input.law = law scope) : Compatible Finance.sources input account.current := by
  intro claim member
  obtain ⟨slot, present, same⟩ := List.mem_map.mp member
  obtain ⟨position, original⟩ := List.get_of_mem present
  subst claim
  have known := ready.denomination position
  unfold NativeDenomination at known
  dsimp only at known
  rw [original] at known
  simpa only [DenominatedAt, Finance.sources, sameLaw] using known

private theorem allocated_payment_uses_the_original_key
    {input : Finance.Input} {origin : Financial.InstructionOrigin input}
    (movement : Financial.Movement input origin)
    (emitted : Financial.readMovement input origin = some movement)
    (state : Finance.Account) (compatible : Compatible Finance.sources input state.current)
    (matched : nativeOwed state = owed movement.instruction.before)
    (instrument : movement.instrument = .delivery) (debtor : movement.debtor = supplier)
    (holder : movement.sender = receiver) (payment : movement.kind = .payment) :
    nativeOwed (allocate Finance.sources ⟨input, origin⟩ state movement.quantity
      (movement.quantity_nonnegative input)).after =
      owed (input.law.step movement.instruction.before movement.instruction.request) := by
  let allocation := allocate Finance.sources ⟨input, origin⟩ state movement.quantity
    (movement.quantity_nonnegative input)
  have covered := movement.accepted.2.2.1
  unfold RawLaw.ClaimGuard at covered
  rw [movement.operation_exact, payment] at covered
  have within : movement.quantity ≤ nativeOwed state := by
    rw [matched]
    simpa only [owed, instrument, debtor, holder] using covered.2.1
  have paid : allocation.remaining = 0 := by
    change (allocate Finance.sources ⟨input, origin⟩ state movement.quantity
      (movement.quantity_nonnegative input)).remaining = 0
    rw [allocate_remaining Finance.sources ⟨input, origin⟩ movement.quantity
      (movement_source_quantity Finance.sources (origin := ⟨input, origin⟩) movement emitted),
      movement_full_capacity Finance.sources (origin := ⟨input, origin⟩) movement emitted _ compatible,
      instrument, debtor, holder]
    exact max_eq_right (sub_nonpos.mpr within)
  have full : allocation.used Finance.sources = movement.quantity := by
    rw [Allocation.used, paid, sub_zero]
  have effects := allocateFrom_ledgerClaims Finance.sources (origin := ⟨input, origin⟩) movement emitted
    state.current.slots.length 0 state
    movement.quantity (movement.quantity_nonnegative input) .delivery supplier receiver
  change nativeOwed allocation.after = nativeOwed state +
    Financial.BalanceConservation.movementDelta input movement (allocation.used Finance.sources) .delivery supplier receiver at effects
  change nativeOwed allocation.after = _
  rw [effects, full, matched, Financial.BalanceConservation.movementDelta_actual]
  unfold owed
  rw [input.law.step_financial_balance, input.law.accepted_delta _ _ movement.accepted]

theorem consume_keeps_the_paid_delivery_key
    (input : Finance.Input) (origin : Financial.InstructionOrigin input) (state : Finance.Account)
    (row : Item) (decoded : origin.instruction? input = some row)
    (paid : input.law.Valid row.before row.request) (retained : RetainsClaims row.request)
    (compatible : Compatible Finance.sources input state.current) (matched : nativeOwed state = owed row.before) :
    nativeOwed ((consume Finance.sources ⟨input, origin⟩ state).next Finance.sources) =
      owed (input.law.step row.before row.request) := by
  cases operation : row.request.operation
  case settle code sourceDebtor targetHolder quantity =>
    have keys : code = .delivery ∧ sourceDebtor = supplier ∧ targetHolder = receiver := by
      simpa only [RetainsClaims, operation] using retained
    obtain ⟨rfl, rfl, rfl⟩ := keys
    have noIssue := issue_readout_nonissue input origin row decoded (by intro i d h q; simp [operation])
    obtain ⟨movement, emitted⟩ := payment_readout_exists input origin row decoded .delivery supplier receiver quantity operation paid
    have same := Option.some.inj (movement.original.symm.trans decoded)
    have shape := movement.operation_exact
    rw [same, operation] at shape
    have coordinates : movement.instrument = .delivery ∧ movement.debtor = supplier ∧ movement.sender = receiver ∧
        movement.kind = .payment := by
      cases kind : movement.kind <;> simp_all [eq_comm]
    change nativeOwed ((consume Finance.sources ⟨input, origin⟩ state).next Finance.sources) = _
    simp only [consume, Finance.sources, noIssue, emitted, InstructionResult.next]
    have sourceMatched : nativeOwed state = owed movement.instruction.before := by rw [same]; exact matched
    simpa only [same] using allocated_payment_uses_the_original_key movement emitted state compatible sourceMatched
      coordinates.1 coordinates.2.1 coordinates.2.2.1 coordinates.2.2.2
  case issue => simp only [RetainsClaims, operation] at retained
  case assign => simp only [RetainsClaims, operation] at retained
  all_goals
    have noIssue := issue_readout_nonissue input origin row decoded (by intro i d h q; simp [operation])
    have noMovement := movement_readout_nonmovement input origin row decoded
      (by intro i d h q; simp [operation]) (by intro i d s h q; simp [operation])
    simpa only [consume, Finance.sources, noIssue, noMovement, InstructionResult.next, owed,
      RawLaw.step, if_pos paid, RawLaw.paidStep, RawLaw.nextClaims, operation] using matched

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery
