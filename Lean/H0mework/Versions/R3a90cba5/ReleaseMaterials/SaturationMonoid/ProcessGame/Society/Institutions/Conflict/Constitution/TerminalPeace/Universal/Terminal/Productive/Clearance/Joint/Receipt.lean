import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Payment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open Reparation (Key)
open Reparation.Actual
open Reparation.Actual.Allocation (Position)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

variable (loss : Reparation.Actual.Occurrence seed community) (answers : ReceiptAnswers seed) (reserve : Party → Good → ℚ)
  (front : Reparation.Actual.Script Party Good Port Technology Instrument)
  (purpose : Port) (key : Key Party Good) (quantity : ℚ)


/-- A single payment may use the surplus already delivered at this cut.
The independent answers authorize only this literal material position. -/
structure CanInstallment : Prop where
  positive : 0 < quantity
  owing : quantity ≤ (dueFor key (prefixRows loss answers front))
  stock : (reserve key.2.1 key.2.2) + quantity ≤ ((prefixRaw loss front).stock key.2.1 key.2.2)
  channel : IndependentReceiptChannel seed answers (Occurrence.history loss ++ front) purpose key quantity

inductive InstallmentIssue where
  | nonpositive (quantityNotPositive : quantity ≤ 0)
  | exceedsDue (remaining : (dueFor key (prefixRows loss answers front)) < quantity)
  | shortage (short : ((prefixRaw loss front).stock key.2.1 key.2.2) < (reserve key.2.1 key.2.2) + quantity)
  | sameParty (same : key.1 = key.2.1)
  | policy (refused : (endAt seed (Occurrence.history loss ++ front)).native.input.law.operationAllowed (endAt seed (Occurrence.history loss ++ front)).raw (paymentRequest purpose key quantity) = false)
  | stockPort (refused : (endAt seed (Occurrence.history loss ++ front)).native.input.law.allowed (endAt seed (Occurrence.history loss ++ front)).raw.technology
      ((endAt seed (Occurrence.history loss ++ front)).native.input.law.stockPort (endAt seed (Occurrence.history loss ++ front)).raw.technology key.2.1 key.2.2) key.2.1 = false)
  | payerRefused (position : Position seed (Occurrence.history loss ++ front) (payment purpose key quantity)) (first : position.val = 0)
      (refused : answers (Occurrence.history loss ++ front) (payment purpose key quantity) position key.2.1 = false)
  | victimRefused (position : Position seed (Occurrence.history loss ++ front) (payment purpose key quantity)) (first : position.val = 0)
      (refused : answers (Occurrence.history loss ++ front) (payment purpose key quantity) position key.1 = false)

variable {loss answers reserve front purpose key quantity}

theorem InstallmentIssue.refutes (issue : InstallmentIssue loss answers reserve front purpose key quantity) :
    ¬ CanInstallment loss answers reserve front purpose key quantity := by
  intro accepted
  cases issue with
  | nonpositive failed => exact (not_lt_of_ge failed) accepted.positive
  | exceedsDue failed => exact (not_lt_of_ge accepted.owing) failed
  | shortage failed => exact (not_lt_of_ge accepted.stock) failed
  | sameParty failed => exact accepted.channel.distinct failed
  | policy failed => simp [accepted.channel.policy] at failed
  | stockPort failed => simp [accepted.channel.port] at failed
  | payerRefused position _ failed => simp [accepted.channel.payer position] at failed
  | victimRefused position _ failed => simp [accepted.channel.victim position] at failed

variable (loss answers reserve front purpose key quantity)

private theorem valid_transfer_before_checking_replies (positive : 0 < quantity) (funded : quantity ≤ ((prefixRaw loss front).stock key.2.1 key.2.2))
    (policy : (endAt seed (Occurrence.history loss ++ front)).native.input.law.operationAllowed (endAt seed (Occurrence.history loss ++ front)).raw (paymentRequest purpose key quantity) = true)
    (port : (endAt seed (Occurrence.history loss ++ front)).native.input.law.allowed (endAt seed (Occurrence.history loss ++ front)).raw.technology
      ((endAt seed (Occurrence.history loss ++ front)).native.input.law.stockPort (endAt seed (Occurrence.history loss ++ front)).raw.technology key.2.1 key.2.2) key.2.1 = true) :
    (endAt seed (Occurrence.history loss ++ front)).native.input.law.Valid (endAt seed (Occurrence.history loss ++ front)).raw (paymentRequest purpose key quantity) := by
  unfold RawLaw.Valid
  refine ⟨⟨trivial, policy⟩, ?_, trivial, ?_, ?_, ?_⟩
  · intro gate listed
    change gate ∈ [(endAt seed (Occurrence.history loss ++ front)).native.input.law.stockPort (endAt seed (Occurrence.history loss ++ front)).raw.technology key.2.1 key.2.2] at listed
    exact Or.inl (List.mem_singleton.mp listed ▸ port)
  · intro entry listed
    change entry ∈ [((key.2.1, key.2.2), quantity)] at listed
    simpa only [List.mem_singleton.mp listed] using positive.le
  · intro entry listed
    change entry ∈ [((key.1, key.2.2), quantity)] at listed
    simpa only [List.mem_singleton.mp listed] using positive.le
  · intro entry listed
    change entry ∈ [((key.2.1, key.2.2), quantity)] at listed
    rcases List.mem_singleton.mp listed with rfl
    change flowAt (locate key.2.1 [(key.2.2, quantity)]) key.2.1 key.2.2 ≤ ((prefixRaw loss front).stock key.2.1 key.2.2)
    rwa [singleton_delivery_flow, if_pos rfl]

private theorem singleton_position_eq (items : (Boundary.Actual.items (endAt seed (Occurrence.history loss ++ front)) (payment purpose key quantity)).length = 1)
    (first second : Position seed (Occurrence.history loss ++ front) (payment purpose key quantity)) : first = second := by
  apply Fin.ext
  have firstWithin := first.isLt.trans_eq items
  have secondWithin := second.isLt.trans_eq items
  omega

/-- The check derives the actual item before asking either original party.
A refusal still identifies the actor and that item's original ordinal. -/
def inspectInstallment (ready : ReadyEntry loss front) (reserveOK : 0 ≤ (reserve key.2.1 key.2.2)) :
    InstallmentIssue loss answers reserve front purpose key quantity ⊕
      PLift (CanInstallment loss answers reserve front purpose key quantity) := by
  if positive : 0 < quantity then
    if owing : quantity ≤ (dueFor key (prefixRows loss answers front)) then
      if stocked : (reserve key.2.1 key.2.2) + quantity ≤ ((prefixRaw loss front).stock key.2.1 key.2.2) then
        if distinct : key.1 ≠ key.2.1 then
          if policy : (endAt seed (Occurrence.history loss ++ front)).native.input.law.operationAllowed (endAt seed (Occurrence.history loss ++ front)).raw (paymentRequest purpose key quantity) = true then
            if port : (endAt seed (Occurrence.history loss ++ front)).native.input.law.allowed (endAt seed (Occurrence.history loss ++ front)).raw.technology
                ((endAt seed (Occurrence.history loss ++ front)).native.input.law.stockPort (endAt seed (Occurrence.history loss ++ front)).raw.technology key.2.1 key.2.2) key.2.1 = true then
              have within := (le_add_of_nonneg_left reserveOK).trans stocked
              have legal := valid_transfer_before_checking_replies loss front purpose key quantity positive within policy port
              have items := congrArg List.length (the_delivery_writes_one_original_item ready.1 ready.2 legal)
              let first : Position seed (Occurrence.history loss ++ front) (payment purpose key quantity) :=
                ⟨0, by rw [items]; exact Nat.zero_lt_one⟩
              have only (other : Position seed (Occurrence.history loss ++ front) (payment purpose key quantity)) : other = first :=
                singleton_position_eq loss front purpose key quantity items other first
              if payer : answers (Occurrence.history loss ++ front) (payment purpose key quantity) first key.2.1 = true then
                if victim : answers (Occurrence.history loss ++ front) (payment purpose key quantity) first key.1 = true then
                  exact .inr ⟨⟨positive, owing, stocked, distinct, policy, port,
                    fun p => only p ▸ payer, fun p => only p ▸ victim⟩⟩
                else exact .inl (.victimRefused first rfl (Bool.eq_false_iff.mpr victim))
              else exact .inl (.payerRefused first rfl (Bool.eq_false_iff.mpr payer))
            else exact .inl (.stockPort (Bool.eq_false_iff.mpr port))
          else exact .inl (.policy (Bool.eq_false_iff.mpr policy))
        else exact .inl (.sameParty (not_not.mp distinct))
      else exact .inl (.shortage (lt_of_not_ge stocked))
    else exact .inl (.exceedsDue (lt_of_not_ge owing))
  else exact .inl (.nonpositive (le_of_not_gt positive))

theorem inspectInstallment_accepts_iff (ready : ReadyEntry loss front) (reserveOK : 0 ≤ (reserve key.2.1 key.2.2)) :
    (∃ checked, inspectInstallment loss answers reserve front purpose key quantity ready reserveOK = .inr checked) ↔
      CanInstallment loss answers reserve front purpose key quantity := by
  constructor
  · rintro ⟨checked, _⟩
    exact checked.down
  · intro accepted
    cases inspectInstallment loss answers reserve front purpose key quantity ready reserveOK with
    | inl failed => exact (failed.refutes accepted).elim
    | inr checked => exact ⟨checked, rfl⟩

structure PaidInstallment where
  delivery : DeliveryAt seed community answers (Occurrence.history loss ++ front) purpose key quantity
  eligible : Occurrence.Eligible answers loss (front ++ installment purpose key quantity)
  ready : ReadyEntry loss (front ++ installment purpose key quantity)
  raw : prefixRaw loss (front ++ installment purpose key quantity) = deliveredRaw (prefixRaw loss front) key quantity
  rows : (prefixRows loss answers (front ++ installment purpose key quantity)).map Prod.fst = (prefixRows loss answers front).map Prod.fst
  otherRows :
    (prefixRows loss answers (front ++ installment purpose key quantity)).filter (fun row => decide (row.1.key ≠ key)) =
      (prefixRows loss answers front).filter (fun row => decide (row.1.key ≠ key))
  debts : ∀ other, dueFor other (prefixRows loss answers (front ++ installment purpose key quantity)) =
    dueFor other (prefixRows loss answers front) - if other = key then quantity else 0
  keepsReserve : (∀ person good, reserve person good ≤ (prefixRaw loss front).stock person good) →
    ∀ person good, reserve person good ≤ (prefixRaw loss (front ++ installment purpose key quantity)).stock person good

/-- Post one actual transfer and consume its native accounting input.
The existing original allocator assigns its signed quantity exactly once. -/
def writeInstallment (safe : Occurrence.Eligible answers loss front) (ready : ReadyEntry loss front)
    (reserveOK : 0 ≤ (reserve key.2.1 key.2.2)) (checked : CanInstallment loss answers reserve front purpose key quantity) :
    PaidInstallment loss answers reserve front purpose key quantity := by
  let state := Occurrence.reached answers loss front
  have funded : quantity ≤ ((prefixRaw loss front).stock key.2.1 key.2.2) := (le_add_of_nonneg_left reserveOK).trans checked.stock
  let delivery : DeliveryAt seed community answers (Occurrence.history loss ++ front) purpose key quantity :=
    executeDelivery ready.1 ready.2 checked.positive funded checked.channel
  have full : Occurrence.history loss ++ (front ++ installment purpose key quantity) = (Occurrence.history loss ++ front) ++ installment purpose key quantity :=
    (List.append_assoc _ _ _).symm
  have raw : prefixRaw loss (front ++ installment purpose key quantity) = deliveredRaw (prefixRaw loss front) key quantity := by
    simpa only [prefixRaw, full] using delivery.raw
  have actualRows : prefixRows loss answers (front ++ installment purpose key quantity) = (Settlement.writeTick answers state (payment purpose key quantity)).stack.balances := by
    have drain : Boundary.Actual.items (endAt seed (Occurrence.history loss ++ (front ++ [(payment purpose key quantity)]))) none = [] := by
      simpa only [List.append_assoc] using delivery.accounting_empty
    have split : front ++ installment purpose key quantity = (front ++ [payment purpose key quantity]) ++ [none] :=
      (List.append_assoc front [payment purpose key quantity] [none]).symm
    change (Occurrence.writeAfter answers (Occurrence.originState loss) (front ++ installment purpose key quantity)).stack.balances = _
    rw [split, Occurrence.writeAfter_snoc_balances,
      a_material_free_tick_keeps_the_original_balances answers _ drain, Occurrence.writeAfter_snoc_balances]
    rfl
  have oneGood (good : Good) (other : good ≠ key.2.2) :
      Settlement.limitAt (Occurrence.history loss ++ front) (payment purpose key quantity) delivery.position good = 0 :=
    (delivery.limitAtExact good).trans (if_neg other)
  have posted := writeTick_pays_the_original_key_exactly answers state (payment purpose key quantity) delivery.position key delivery.receipt
    delivery.positions delivery.issued delivery.noDamage
    (fun row present _ => reached_rows_have_their_actual_birth_prefix answers loss front row present)
  have kept := writeTick_keeps_every_other_original_row_of_a_single_good_delivery answers state (payment purpose key quantity) delivery.position
    key delivery.receipt delivery.positions delivery.issued delivery.noDamage oneGood
  have stillSafe : Occurrence.Eligible answers loss (front ++ installment purpose key quantity) :=
    (eligible_append answers (Occurrence.history loss)).mpr ⟨safe, delivery.eligible _⟩
  have nextReady : ReadyEntry loss (front ++ installment purpose key quantity) := by
    unfold ReadyEntry
    rw [full]
    exact ⟨delivery.ready, delivery.review⟩
  refine ⟨delivery, stillSafe, nextReady, raw, ?_, ?_, ?_, ?_⟩
  · exact (congrArg (List.map Prod.fst) actualRows).trans posted.1
  · exact (congrArg _ actualRows).trans kept
  · intro other
    rw [actualRows]
    by_cases same : other = key
    · subst other
      rw [if_pos rfl, posted.2, delivery.limit, min_eq_left checked.owing]
    · have unchanged := writeTick_keeps_rows_without_receipt_or_delivery answers state (payment purpose key quantity) delivery.position
        delivery.positions delivery.noDamage (· = other)
        (fun read equal => Or.inl (delivery.onlyReceipt read (equal.symm ▸ same)))
      simp only [if_neg same, sub_zero, dueFor_is_the_sum_of_the_original_rows_of_the_key, unchanged]
      rfl
  · intro original person good
    rw [raw]
    change reserve person good ≤ (prefixRaw loss front).stock person good -
      (if (person, good) = payerCell key then quantity else 0) +
      (if (person, good) = (key.1, key.2.2) then quantity else 0)
    have incoming : 0 ≤ (if (person, good) = (key.1, key.2.2) then quantity else 0) := by
      split
      · exact checked.positive.le
      · exact le_rfl
    apply le_trans _ (le_add_of_nonneg_right incoming)
    by_cases payer : (person, good) = payerCell key
    · simp only [if_pos payer, payerCell]
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj payer
      linarith only [checked.stock]
    · simpa only [if_neg payer, sub_zero] using original person good

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint
