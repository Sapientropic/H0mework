import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Raw

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Raw.Reparation
open Source.Program
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (original : Occurrence Party Good Port Technology Instrument)

/-- One original matrix, not an independently spendable physical cursor per cell.
World continuations supply the single actual cursor used by each next attempt. -/
structure Account where
  private mk ::
  remaining : Party × Good → ℚ
  paid : Party × Good → ℚ
  nonnegative : ∀ key, 0 ≤ remaining key
  paid_nonnegative : ∀ key, 0 ≤ paid key
  balance : ∀ key, remaining key + paid key = quantity original key

def initial : Account original :=
  ⟨quantity original,fun _ => 0,fun _ => le_max_left _ _,fun _ => le_rfl,by simp⟩

structure Order (account : Account original) where
  private mk ::
  key : Party × Good
  originalCell : key ∈ positiveScope original
  unpaid : 0 < account.remaining key
  donor : Party
  originalController : donor ∈ cohort original
  different : donor ≠ key.1

def orders (account : Account original) : List (Order original account) :=
  (positiveScope original).attach.flatMap fun key =>
    if unpaid : 0 < account.remaining key.val then
      (cohort original).attach.filterMap fun donor =>
        if different : donor.val ≠ key.val.1 then
          some ⟨key.val,key.property,unpaid,donor.val,donor.property,different⟩
        else none
    else []

theorem every_unpaid_original_cell_and_distinct_controller_has_an_order
    (account : Account original) (key : Party × Good) (inside : key ∈ positiveScope original)
    (positive : 0 < account.remaining key) (donor : Party) (member : donor ∈ cohort original)
    (different : donor ≠ key.1) :
    ∃ order ∈ orders original account, order.key = key ∧ order.donor = donor := by
  refine ⟨⟨key,inside,positive,donor,member,different⟩,?_,rfl,rfl⟩
  unfold orders
  apply List.mem_flatMap.mpr
  refine ⟨⟨key,inside⟩,by simp,?_⟩
  rw [dif_pos positive]
  exact List.mem_filterMap.mpr ⟨⟨donor,member⟩,by simp,by simp [different]⟩

variable {original}
def Order.amount {account : Account original} (order : Order original account)
    (before : RawCurrent Party Good Technology Instrument) : ℚ :=
  if 0 < before.stock order.donor order.key.2 then
    min (account.remaining order.key) (before.stock order.donor order.key.2)
  else account.remaining order.key

def Order.request {account : Account original} (order : Order original account)
    (law : RawLaw Party Good Port Technology Instrument) (before : RawCurrent Party Good Technology Instrument) :
    Request Party Good Port Technology Instrument :=
  ⟨order.key.1,[],law.stockPort before.technology order.donor order.key.2,[],
    .transfer order.donor order.key.1 [(order.key.2,order.amount before)]⟩

theorem Order.amount_is_positive {account : Account original} (order : Order original account)
    (before : RawCurrent Party Good Technology Instrument) : 0 < order.amount before := by
  unfold Order.amount
  split
  · rename_i positive; exact lt_min order.unpaid positive
  · exact order.unpaid

variable (original)
def selected (account : Account original) := (orders original account).head?
def word (account : Account original) (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument) : RawEvent Party Good Port Technology Instrument :=
  match selected original account with
  | none => []
  | some order => [order.request law before]

/-- Only this source-selected, original-cell request earns an allocation.
Unrelated credits are not accepted as reparation inputs. -/
def material (account : Account original) (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument) (key : Party × Good) : ℚ :=
  match selected original account with
  | none => 0
  | some order => if key = order.key then
      max 0 ((law.next before (word original account law before)).stock key.1 key.2 - before.stock key.1 key.2)
    else 0

def applied (account : Account original) (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument) (key : Party × Good) :=
  min (account.remaining key) (material original account law before key)

theorem material_is_nonnegative (account : Account original) (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument) (key : Party × Good) :
    0 ≤ material original account law before key := by
  unfold material
  split
  · exact le_rfl
  · split
    · exact le_max_left _ _
    · exact le_rfl

theorem applied_is_real_and_bounded (account : Account original) (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument) (key : Party × Good) :
    0 ≤ applied original account law before key ∧
    applied original account law before key ≤ account.remaining key ∧
    applied original account law before key ≤ material original account law before key :=
  ⟨le_min (account.nonnegative key) (material_is_nonnegative original account law before key),min_le_left _ _,min_le_right _ _⟩

def advance (account : Account original) (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument) : Account original :=
  ⟨(fun key => account.remaining key - applied original account law before key),
    (fun key => account.paid key + applied original account law before key),
    (fun key => sub_nonneg.mpr (applied_is_real_and_bounded original account law before key).2.1),
    (fun key => add_nonneg (account.paid_nonnegative key) (applied_is_real_and_bounded original account law before key).1),
    (by intro key; simpa only [sub_add_add_cancel] using account.balance key)⟩

theorem every_advance_retains_the_original_quantity (account : Account original)
    (law : RawLaw Party Good Port Technology Instrument) (before : RawCurrent Party Good Technology Instrument)
    (key : Party × Good) :
    (advance original account law before).remaining key + (advance original account law before).paid key = quantity original key :=
  (advance original account law before).balance key

theorem no_original_cell_is_refilled (account : Account original)
    (law : RawLaw Party Good Port Technology Instrument) (before : RawCurrent Party Good Technology Instrument)
    (key : Party × Good) : (advance original account law before).remaining key ≤ account.remaining key :=
  sub_le_self _ (applied_is_real_and_bounded original account law before key).1

theorem the_request_is_self_signed_without_any_controllers_consent (account : Account original)
    (law : RawLaw Party Good Port Technology Instrument) (before : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (inside : request ∈ word original account law before) :
    ∃ order : Order original account, selected original account = some order ∧
      request = order.request law before ∧ request.signer = order.key.1 ∧ request.consents = [] ∧
      order.donor ∈ cohort original ∧ order.donor ≠ order.key.1 := by
  unfold word at inside
  split at inside
  · cases inside
  · rename_i order same
    have exactRequest := List.mem_singleton.mp inside
    exact ⟨order,same,exactRequest,by rw [exactRequest]; rfl,by rw [exactRequest]; rfl,
      order.originalController,order.different⟩

theorem a_refused_request_cannot_pay_any_cell (account : Account original)
    (law : RawLaw Party Good Port Technology Instrument) (before : RawCurrent Party Good Technology Instrument)
    (order : Order original account) (chosen : selected original account = some order)
    (refused : ¬ law.Valid before (order.request law before)) (key : Party × Good) :
    applied original account law before key = 0 ∧
      (advance original account law before).remaining key = account.remaining key := by
  have unchanged : (law.next before (word original account law before)).stock = before.stock := by
    simp only [word,chosen,RawLaw.next,RawLaw.execute,RawLaw.rejected_preserves_current _ _ _ refused]
  have zero : material original account law before key = 0 := by simp [material,chosen,unchanged]
  have applied : applied original account law before key = 0 := by
    simp only [Reparation.applied,zero,min_eq_right (account.nonnegative key)]
  exact ⟨applied,by simp [advance,applied]⟩

theorem a_positive_allocation_has_its_original_cell_controller_and_accepted_raw_item
    (account : Account original) (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument) (key : Party × Good)
    (positive : 0 < applied original account law before key) :
    ∃ order : Order original account, selected original account = some order ∧ key = order.key ∧
      law.Valid before (order.request law before) ∧
      ∃ item ∈ law.rawItems before (word original account law before),
        item.index = 0 ∧ item.before = before ∧ item.request = order.request law before := by
  have real := lt_of_lt_of_le positive (applied_is_real_and_bounded original account law before key).2.2
  cases chosen : selected original account with
  | none => simp only [material,chosen] at real; exact (lt_irrefl 0 real).elim
  | some order =>
    have same : key = order.key := by
      by_contra different
      simp only [material,chosen,if_neg different] at real
      exact lt_irrefl 0 real
    have valid : law.Valid before (order.request law before) := by
      by_contra refused
      have zero := (a_refused_request_cannot_pay_any_cell original account law before order chosen refused key).1
      rw [zero] at positive
      exact lt_irrefl 0 positive
    refine ⟨order,rfl,same,valid,⟨0,before,order.request law before⟩,?_,rfl,rfl,rfl⟩
    simp [word,chosen,RawLaw.rawItems,RawLaw.execute]

/-- A targeted transfer does not manufacture a new productive-loss claim. -/
theorem the_reparation_word_itself_has_no_new_productive_loss (account : Account original)
    (law : RawLaw Party Good Port Technology Instrument) (before : RawCurrent Party Good Technology Instrument)
    (party : Party) (good : Good) :
    Raw.loss (⟨law,before,word original account law before⟩ : Occurrence Party Good Port Technology Instrument) party good = 0 := by
  cases chosen : selected original account <;>
    simp [Raw.loss,Raw.items,Raw.openedItems,Raw.productiveNetFor,Raw.productiveAt,
      RawLaw.rawItems,RawLaw.execute,word,chosen,Order.request]

theorem a_lawful_targeted_transfer_has_its_exact_original_material_receipt
    (account : Account original) (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument) (order : Order original account)
    (chosen : selected original account = some order) (valid : law.Valid before (order.request law before)) :
    material original account law before order.key = order.amount before := by
  have debit : flowAt (law.actualDebit before (order.request law before)) order.key.1 order.key.2 = 0 := by
    rw [RawLaw.actualDebit,if_pos valid]
    have different : (order.donor,order.key.2) ≠ order.key := fun same => order.different (congrArg Prod.fst same)
    simp [RawLaw.debit,Order.request,locate,flowAt,Source.Program.amount,different]
  have credit : flowAt (law.actualCredit before (order.request law before)) order.key.1 order.key.2 = order.amount before := by
    rw [RawLaw.actualCredit,if_pos valid]
    simp [RawLaw.credit,Order.request,locate,flowAt,Source.Program.amount]
  have balance := law.material_step_balance before (order.request law before) order.key.1 order.key.2
  rw [debit,credit] at balance
  have net : (law.next before (word original account law before)).stock order.key.1 order.key.2 - before.stock order.key.1 order.key.2 = order.amount before := by
    have same : (law.next before (word original account law before)).stock = (law.step before (order.request law before)).stock := by
      simp only [word,chosen,RawLaw.next,RawLaw.execute]
    rw [same]
    linarith
  simp [material,chosen,net,max_eq_right (le_of_lt (order.amount_is_positive before))]

theorem a_lawful_attempt_pays_part_of_the_original_cell_or_is_an_actual_refusal
    (account : Account original) (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument) (order : Order original account)
    (chosen : selected original account = some order) :
    (law.Valid before (order.request law before) ∧ 0 < applied original account law before order.key) ∨
    (¬ law.Valid before (order.request law before) ∧ ∀ key,
      (advance original account law before).remaining key = account.remaining key) := by
  by_cases valid : law.Valid before (order.request law before)
  · refine Or.inl ⟨valid,?_⟩
    unfold applied
    rw [a_lawful_targeted_transfer_has_its_exact_original_material_receipt original account law before order chosen valid]
    exact lt_min order.unpaid (order.amount_is_positive before)
  · exact Or.inr ⟨valid,fun key => (a_refused_request_cannot_pay_any_cell original account law before order chosen valid key).2⟩

theorem every_positive_allocation_is_bounded_by_its_same_actual_transfer_credit
    (account : Account original) (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument) (key : Party × Good)
    (positive : 0 < applied original account law before key) :
    ∃ order : Order original account, selected original account = some order ∧ key = order.key ∧
      law.Valid before (order.request law before) ∧
      applied original account law before key ≤
        flowAt (law.actualCredit before (order.request law before)) key.1 key.2 := by
  obtain ⟨order,chosen,same,valid,_⟩ :=
    a_positive_allocation_has_its_original_cell_controller_and_accepted_raw_item original account law before key positive
  subst key
  refine ⟨order,chosen,rfl,valid,?_⟩
  have credit : flowAt (law.actualCredit before (order.request law before)) order.key.1 order.key.2 = order.amount before := by
    rw [RawLaw.actualCredit,if_pos valid]
    simp [RawLaw.credit,Order.request,locate,flowAt,Source.Program.amount]
  rw [credit]
  exact (applied_is_real_and_bounded original account law before order.key).2.2.trans_eq
    (a_lawful_targeted_transfer_has_its_exact_original_material_receipt original account law before order chosen valid)

theorem reparation_never_issues_assigns_or_retires_financial_claims (account : Account original)
    (law : RawLaw Party Good Port Technology Instrument) (before : RawCurrent Party Good Technology Instrument) :
    (law.next before (word original account law before)).claims = before.claims := by
  unfold word
  split
  · rfl
  · rename_i order chosen
    change (law.step before (order.request law before)).claims = before.claims
    by_cases valid : law.Valid before (order.request law before)
    · rw [RawLaw.step,if_pos valid]
      rfl
    · exact congrArg RawCurrent.claims (law.rejected_preserves_current _ _ valid)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Raw.Reparation
