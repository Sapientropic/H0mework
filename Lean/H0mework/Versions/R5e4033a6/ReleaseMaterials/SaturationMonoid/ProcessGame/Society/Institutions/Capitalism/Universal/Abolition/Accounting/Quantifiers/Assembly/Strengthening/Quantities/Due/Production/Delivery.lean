import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Residual
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Positions
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement.Profile
import Mathlib.Data.List.Nodup

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]


variable {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {past : List (Option (Compile.RawInput Party Good Port Technology Instrument))}
  {ordered : List TaskId} {task : TaskId → PublicTaskSpec Party Good}
  {reserved : Finset (Service.Ordinal source past)}

local notation "Rows" => Service.Need ordered.toFinset task

variable {receipt : Network.Certificate (Service.network source past ordered.toFinset task reserved)}
  {dueBy : ℚ}
  {sign : Service.Need ordered.toFinset task → Source.Program.Request Party Good Port Technology Instrument}
  {held : RawEvent Party Good Port Technology Instrument}

local notation "Now" => Execution.endAt source past
local notation "Suffix" => Execution.primitiveScript (residualWord receipt dueBy sign)
local notation "Paid" => PaymentAt Now (residualWord receipt dueBy sign) held
local notation "Supplies" => Service.Supply Now Suffix ordered.toFinset task

private theorem residual_word_length :
    (residualWord receipt dueBy sign).length = (residualRows receipt dueBy).length := by
  unfold residualWord
  exact List.length_map _

def suffixPositions (_payment : Paid) :
    Service.Ordinal Now Suffix ≃ Fin (residualRows receipt dueBy).length :=
  finCongr ((paid_word_length _payment.trace).trans (residual_word_length (sign := sign)))

def paidRow (_payment : Paid) (_ordinal : Service.Ordinal Now Suffix) : Rows :=
  (residualRows receipt dueBy).get (suffixPositions _payment _ordinal)

theorem paidRow_is_original (payment : Paid) (ordinal : Service.Ordinal Now Suffix) :
    paidRow payment ordinal ∈ residualRows receipt dueBy := List.get_mem _ _

theorem paidRow_is_injective (payment : Paid) : Function.Injective (paidRow payment) :=
  (List.Nodup.injective_get ((List.nodup_dedup _).filter _)).comp (suffixPositions payment).injective

theorem every_selected_row_gets_its_own_new_ordinal (payment : Paid) (line : Rows) :
    line ∈ residualRows receipt dueBy ↔ ∃ ordinal, paidRow payment ordinal = line := by
  constructor
  · intro listed
    obtain ⟨index, equal⟩ := List.mem_iff_get.mp listed
    refine ⟨(suffixPositions payment).symm index, ?_⟩
    unfold paidRow
    rw [Equiv.apply_symm_apply]
    exact equal
  · rintro ⟨ordinal, rfl⟩
    exact paidRow_is_original payment ordinal

/-- The physical debit appears at its actual ordinal with the original
bearer, material, purpose and remaining quantity. -/
theorem the_paid_residual_has_its_exact_native_receipt
    (payment : Paid) (ordinal : Service.Ordinal Now Suffix) :
    let line := paidRow payment ordinal
    let actual := Execution.timedAt Now Suffix ordinal
    actual.1.request = residualUse receipt line (sign line) ∧
      actual.1.before.clock = (Now).raw.clock ∧ actual.2 = (Now).raw.clock ∧
      (interpreter Now).Valid actual.1.before actual.1.request := by
  let word := residualWord receipt dueBy sign
  let position : Fin word.length := Fin.cast (paid_word_length payment.trace) ordinal
  have numbered : nativePosition payment.trace position = ordinal := Fin.ext rfl
  have actual := the_native_position_carries_the_exact_submitted_request payment.trace position
  change (Execution.timedAt Now Suffix (nativePosition payment.trace position)).1.request = word[position.val] ∧ _ at actual
  rw [numbered] at actual
  have exactUse : word[position.val] = residualUse receipt (paidRow payment ordinal) (sign (paidRow payment ordinal)) := by
    simp only [word, residualWord, List.getElem_map]
    rfl
  exact ⟨actual.1.trans exactUse, actual.2⟩

private theorem new_capacity_on_its_original_receipt
    (first : Network.Certificate (Service.network source past ordered.toFinset task reserved))
    (later : List (Option (Compile.RawInput Party Good Port Technology Instrument)))
    (item : Service.Supply Now later ordered.toFinset task) :
    (Service.carryNetwork first later ∅).capacity item =
      Service.paidAmount (interpreter Now) (Execution.timedAt Now later item.1).1 item.2.val :=
  if_neg (t := (0 : ℚ)) (Finset.notMem_empty item.1)

theorem paid_residual_is_eligible_for_its_original_window (payment : Paid)
    (timely : ∀ line ∈ residualRows receipt dueBy, InWindow (Now).raw.clock line)
    (ordinal : Service.Ordinal Now Suffix) :
    let line := paidRow payment ordinal
    let item : Supplies := (ordinal, Settlement.originalUnit line)
    Service.accepts Now Suffix ∅ line item ∧
      (Service.carryNetwork receipt Suffix ∅).capacity item = Service.remaining receipt line := by
  let line := paidRow payment ordinal
  let actual := Execution.timedAt Now Suffix ordinal
  let item : Supplies := (ordinal, Settlement.originalUnit line)
  have clock := timely line (paidRow_is_original payment ordinal)
  obtain ⟨command, started, committed, valid⟩ := the_paid_residual_has_its_exact_native_receipt payment ordinal
  have operation : actual.1.request.operation =
      .use line.1.spec.bearer [(line.2.val, Service.remaining receipt line)] line.1.spec.purpose :=
    congrArg Source.Program.Request.operation command
  have authorized : (interpreter Now).Valid actual.1.before actual.1.request := valid
  have material :
      Service.paidAmount (interpreter Now) actual.1 line.2.val = Service.remaining receipt line := by
    unfold Service.paidAmount
    rw [operation]
    unfold RawLaw.actualDebit
    rw [if_pos authorized, RawLaw.debit, operation]
    simp [locate, flowAt, amount]
  change Service.accepts Now Suffix ∅ line item ∧
    (Service.carryNetwork receipt Suffix ∅).capacity item = Service.remaining receipt line
  constructor
  · refine ⟨Finset.notMem_empty _, rfl, started ▸ clock.1, committed ▸ clock.2, valid, ?_⟩
    change Service.useFor actual.1 line.1.spec
    simp [Service.useFor, operation]
  · exact (new_capacity_on_its_original_receipt receipt Suffix item).trans material

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production
