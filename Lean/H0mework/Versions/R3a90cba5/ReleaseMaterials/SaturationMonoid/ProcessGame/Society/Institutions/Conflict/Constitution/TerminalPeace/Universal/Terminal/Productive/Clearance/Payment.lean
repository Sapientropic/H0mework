import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Delivery
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Portfolio
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Rows

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open Reparation Reparation.Actual

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "Word" => Reparation.Actual.Script Party Good Port Technology Instrument
local notation "Loss" => Occurrence seed community
local notation "Raw" => RawCurrent Party Good Technology Instrument
local notation "ClaimKey" => Key Party Good

def originalKeys (loss : Loss) : List ClaimKey :=
  ((Occurrence.originState loss).stack.balances.map fun row => row.1.key).dedup

/-- Source-local payment permissions and separate personal answers to the
generated delivery. A channel reads the amount at its own actual cut. -/
structure IndependentReceiptChannels (loss : Loss) (answers : ReceiptAnswers seed) where
  purpose : ClaimKey → Port
  atDelivery : ∀ (front : Word) (key : ClaimKey),
    Occurrence.Eligible answers loss front → ReadyEntry loss front → key ∈ originalKeys loss →
    let amount := dueFor key (Occurrence.reached answers loss front).stack.balances
    0 < amount → amount ≤ (endAt seed (Occurrence.history loss ++ front)).raw.stock key.2.1 key.2.2 →
    IndependentReceiptChannel seed answers (Occurrence.history loss ++ front) (purpose key) key amount

variable (loss : Reparation.Actual.Occurrence seed community) (answers : ReceiptAnswers seed)

abbrev prefixRaw (front : Word) := (endAt seed (Occurrence.history loss ++ front)).raw
abbrev prefixRows (front : Word) := (Occurrence.reached answers loss front).stack.balances

theorem eligible_prefix_has_the_original_keys (front : Word) (safe : Occurrence.Eligible answers loss front) :
    ((prefixRows loss answers front).map fun row => row.1.key).dedup = originalKeys loss := by
  have same := Occurrence.reached_origins answers loss front
  rw [Occurrence.eligible_preserves_the_literal_original_loss_inventory community answers (Occurrence.history loss)
    (Occurrence.history loss) front safe, ← Occurrence.originState_origins] at same
  have keys := congrArg (List.map fun origin : Loss => origin.key) same
  simpa only [originalKeys, List.map_map, Function.comp_def] using congrArg List.dedup keys

/-- The remaining payments fit while the original productive inventory
is held in place. Credits to other accounts are actual incoming stock. -/
def CoversPortfolio (reserve : Party → Good → ℚ) (front : Word) : Prop :=
  ∀ person good, reserve person good + cellDue (prefixRows loss answers front) (person, good) ≤
    (prefixRaw loss front).stock person good

def payKeyWord (channels : IndependentReceiptChannels loss answers) (front : Word) (key : ClaimKey) : Word :=
  let amount := dueFor key (prefixRows loss answers front)
  (front ++ [payment (channels.purpose key) key amount]) ++ [none]

theorem paying_a_key_writes_its_original_settlement
    (channels : IndependentReceiptChannels loss answers) (reserve : Party → Good → ℚ)
    (front : Word) (key : ClaimKey) (listed : key ∈ originalKeys loss)
    (safe : Occurrence.Eligible answers loss front) (ready : ReadyEntry loss front)
    (funds : CoversPortfolio loss answers reserve front)
    (reserveOK : ∀ person good, 0 ≤ reserve person good)
    (positive : 0 < dueFor key (prefixRows loss answers front)) :
    let after := payKeyWord loss answers channels front key
    Occurrence.Eligible answers loss after ∧ ReadyEntry loss after ∧
    CoversPortfolio loss answers reserve after ∧
    (∀ other, dueFor other (prefixRows loss answers after) =
      if other = key then 0 else dueFor other (prefixRows loss answers front)) ∧
    prefixRaw loss after = deliveredRaw (prefixRaw loss front) key (dueFor key (prefixRows loss answers front)) := by
  classical
  let amount := dueFor key (prefixRows loss answers front)
  let body : Reparation.Actual.Input Party Good Port Technology Instrument := payment (channels.purpose key) key amount
  let past := Occurrence.history loss ++ front
  let state := Occurrence.reached answers loss front
  let after := payKeyWord loss answers channels front key
  have within : amount ≤ (prefixRaw loss front).stock key.2.1 key.2.2 := by
    have owed := dueFor_le_its_original_cell (prefixRows loss answers front) key
    exact owed.trans ((le_add_of_nonneg_left (reserveOK key.2.1 key.2.2)).trans (funds key.2.1 key.2.2))
  let delivery : DeliveryAt seed community answers past (channels.purpose key) key amount :=
    executeDelivery ready.1 ready.2 positive within (channels.atDelivery front key safe ready listed positive within)
  have samePast : Occurrence.history loss ++ after = past ++ installment (channels.purpose key) key amount := by
    simp only [after, past, payKeyWord, List.append_assoc, List.singleton_append]
    rfl
  have safeAfter : Occurrence.Eligible answers loss after := by
    have nextSafe := delivery.eligible (Occurrence.history loss)
    unfold after payKeyWord Occurrence.Eligible
    rw [List.append_assoc]
    exact (eligible_append answers (Occurrence.history loss)).mpr ⟨safe, nextSafe⟩
  have raw : prefixRaw loss after = deliveredRaw (prefixRaw loss front) key amount :=
    (congrArg (fun history : Word => (endAt seed history).raw) samePast).trans delivery.raw
  have actualRows : prefixRows loss answers after = (Settlement.writeTick answers state body).stack.balances := by
    have drain : Boundary.Actual.items (endAt seed (Occurrence.history loss ++ (front ++ [body]))) none = [] := by
      simpa only [past, List.append_assoc] using delivery.accounting_empty
    change (Occurrence.writeAfter answers (Occurrence.originState loss) ((front ++ [body]) ++ [none])).stack.balances = _
    rw [Occurrence.writeAfter_snoc_balances, a_material_free_tick_keeps_the_original_balances answers _ drain,
      Occurrence.writeAfter_snoc_balances]
    rfl
  have oneGood (good : Good) (other : good ≠ key.2.2) :
      Settlement.limitAt past body delivery.position good = 0 := by
    exact (delivery.limitAtExact good).trans (if_neg other)
  have exactPosting := writeTick_clears_key_and_preserves_all_other_due answers state body delivery.position
    key delivery.receipt delivery.positions delivery.issued delivery.noDamage
    (fun row present _ => reached_rows_have_their_actual_birth_prefix answers loss front row present)
    (le_of_eq delivery.limit.symm) oneGood
  have otherRows := writeTick_keeps_every_other_original_row_of_a_single_good_delivery answers state body
    delivery.position key delivery.receipt delivery.positions delivery.issued delivery.noDamage oneGood
  have debt (other : ClaimKey) : dueFor other (prefixRows loss answers after) =
      if other = key then 0 else dueFor other (prefixRows loss answers front) := by
    rw [actualRows]
    exact exactPosting.2 other
  have readyAfter : ReadyEntry loss after := by
    unfold ReadyEntry
    rw [samePast]
    exact ⟨delivery.ready, delivery.review⟩
  refine ⟨safeAfter, readyAfter, ?_, debt, raw⟩
  intro person good
  have paid : dueFor key (prefixRows loss answers after) = 0 := (debt key).trans (if_pos rfl)
  have preserved :
      (prefixRows loss answers after).filter (fun row => decide (row.1.key ≠ key)) =
      (prefixRows loss answers front).filter (fun row => decide (row.1.key ≠ key)) :=
    (congrArg _ actualRows).trans otherRows
  have pastDue := funds person good
  have credited : 0 ≤ (if (person, good) = (key.1, key.2.2) then amount else 0) := by
    split
    · exact positive.le
    · exact le_rfl
  rw [cellDue_after_clearing_one_key key (person, good) paid preserved, raw]
  change reserve person good + (cellDue (prefixRows loss answers front) (person, good) -
    (if payerCell key = (person, good) then amount else 0)) ≤
    (prefixRaw loss front).stock person good - (if (person, good) = payerCell key then amount else 0) +
    (if (person, good) = (key.1, key.2.2) then amount else 0)
  by_cases same : (person, good) = payerCell key
  · simp only [if_pos same, if_pos same.symm]
    linarith only [pastDue, credited]
  · simp only [if_neg same, if_neg (Ne.symm same), sub_zero]
    linarith only [pastDue, credited]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance
