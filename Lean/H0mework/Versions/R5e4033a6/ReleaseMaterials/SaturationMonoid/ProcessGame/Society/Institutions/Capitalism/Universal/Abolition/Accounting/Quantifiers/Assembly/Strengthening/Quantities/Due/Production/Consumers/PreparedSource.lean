import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Delivery
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Consumers.Coordinates

set_option autoImplicit false
set_option maxRecDepth 8192


namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Consumers.Prepared

open Source.Program Abolition.Root Abolition.Root.Registered Execution
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource lifeScript lifeTrace)
open Innovation.Contribution.Pricing.Consumers.Actual (lifeWord)
open Service.Consumers (liveClock wholeFee tasks firstNeed all_lines_are_original)

noncomputable section

abbrev OriginalLineAt (deadline : ℚ) := Service.Need ([()] : List Unit).toFinset (tasks deadline)
abbrev OriginalLine := OriginalLineAt liveClock

private def originalNeed : OriginalLine := firstNeed liveClock

private theorem every_line_is_original (line : OriginalLine) : line = originalNeed :=
  all_lines_are_original liveClock line

def beforePaymentAt (deadline : ℚ) :=
  Service.allocate lifeSource lifeScript ([()] : List Unit).toFinset (tasks deadline) ∅ [()] rfl

def beforePayment := beforePaymentAt liveClock

abbrev current := endAt lifeSource lifeScript

def compiled := residualWord beforePayment liveClock (fun _ => wholeFee)

private theorem old_life_debits_do_not_pay_the_original_external_row (deadline : ℚ) (line : OriginalLineAt deadline)
    (item : Service.Supply lifeSource lifeScript ([()] : List Unit).toFinset (tasks deadline)) :
    (Service.network lifeSource lifeScript ([()] : List Unit).toFinset (tasks deadline) ∅).allows line item = false := by
  cases outcome : (Service.network lifeSource lifeScript ([()] : List Unit).toFinset (tasks deadline) ∅).allows line item
  · rfl
  · have eligible := (Service.network_allows_iff lifeSource lifeScript _ _ ∅ line item).mp outcome
    have used := eligible.2.2.2.2.2
    let position : Fin lifeWord.length := Fin.cast (paid_word_length lifeTrace) item.1
    have same : nativePosition lifeTrace position = item.1 := Fin.ext rfl
    have original := (the_native_position_carries_the_exact_submitted_request lifeTrace position).1
    rw [same] at original
    change (timedAt lifeSource lifeScript item.1).1.request = _ at original
    have aligned : Service.useFor (timedAt lifeSource lifeScript item.1).1 line.1.spec := used
    unfold Service.useFor at aligned
    rw [original, all_lines_are_original deadline line] at aligned
    have present : lifeWord[position.val] ∈ lifeWord := List.getElem_mem _
    generalize lifeWord[position.val] = request at aligned present
    simp only [lifeWord, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;>
      change _ ∧ Use.necessity = Use.external at aligned <;> cases aligned.2

theorem the_external_row_keeps_its_exact_unpaid_unit_at (deadline : ℚ) (line : OriginalLineAt deadline) :
    Service.remaining (beforePaymentAt deadline) line = 1 := by
  have empty (item : Service.Supply lifeSource lifeScript ([()] : List Unit).toFinset (tasks deadline)) :
      (beforePaymentAt deadline).allocation line item = 0 :=
    ((beforePaymentAt deadline).admitted.1 line item).2
      (old_life_debits_do_not_pay_the_original_external_row deadline line item)
  have unpaid : Network.rowTotal (beforePaymentAt deadline).allocation line = 0 := by simp [Network.rowTotal, empty]
  unfold Service.remaining
  rw [unpaid, sub_zero, all_lines_are_original deadline line]
  change max (0 : ℚ) (amount Bool [(false, 1)] false) = 1
  norm_num [amount]

theorem the_external_row_keeps_its_exact_unpaid_unit (line : OriginalLine) :
    Service.remaining beforePayment line = 1 :=
  the_external_row_keeps_its_exact_unpaid_unit_at liveClock line

private theorem singleton_from_coverage {A : Type} (rows : List A) (original : A)
    (each : ∀ entry : A, entry = original) (present : original ∈ rows) (unique : rows.Nodup) :
    rows = [original] := by
  cases rows with
  | nil => cases present
  | cons first rest =>
    rw [each first]
    cases rest with
    | nil => rfl
    | cons second _ =>
      exact ((List.nodup_cons.mp unique).1
        (List.mem_cons.mpr (.inl ((each first).trans (each second).symm)))).elim

theorem original_ordered_rows (deadline : ℚ) :
    (Service.needList ([()] : List Unit).toFinset (tasks deadline) [()] rfl).dedup = [firstNeed deadline] :=
  singleton_from_coverage _ _ (all_lines_are_original deadline)
    (List.mem_dedup.mpr (Service.needList_covers _ _ _ rfl _)) (List.nodup_dedup _)

private theorem only_one_original_row_is_selected :
    residualRows beforePayment liveClock = [originalNeed] := by
  apply singleton_from_coverage _ originalNeed every_line_is_original
  · exact (original_due_and_unpaid_iff_listed beforePayment liveClock originalNeed).mpr
      ⟨le_rfl, by rw [the_external_row_keeps_its_exact_unpaid_unit]; decide⟩
  · exact (List.nodup_dedup _).filter _

theorem the_actual_prior_account_generates_one_original_service_use :
    compiled = [wholeFee] := by
  unfold compiled residualWord
  rw [only_one_original_row_is_selected]
  change [residualUse beforePayment originalNeed wholeFee] = _
  unfold residualUse
  rw [the_external_row_keeps_its_exact_unpaid_unit]
  rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Consumers.Prepared
