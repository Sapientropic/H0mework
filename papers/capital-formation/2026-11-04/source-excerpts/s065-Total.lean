import SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Allocation.Bounds

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Allocation

open Source.Program Innovation

noncomputable section

attribute [local irreducible] actualLaw Responsibility.Family.positiveScope
  Responsibility.controllerCohort Entitlement.Duty.scope

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))

def grossAtRecipient (old : Party × Good → ℚ) (p g : Bool) (work : Working Party Good)
    (item : ExecutionItem Party Good Port Technology Instrument) (key : Party × Good) : ℚ :=
  match item.request.operation with
  | .transfer sender recipient _ =>
      if recipient = key.1 then grossTransfer seed old p g work item (recipient,sender,key.2) else 0
  | _ => 0

theorem gross_at_this_recipient_is_inside_this_actual_credit
    (old : Party × Good → ℚ) (p g : Bool) (work : Working Party Good)
    (item : ExecutionItem Party Good Port Technology Instrument) (key : Party × Good) :
    grossAtRecipient seed old p g work item key ≤ incoming seed item key := by
  cases operation : item.request.operation <;> simp only [grossAtRecipient,operation]
  all_goals try exact incoming_nonnegative seed item key
  rename_i sender recipient goods
  split
  · next same =>
      have bound := both_rows_share_only_the_one_original_transfer seed old p g work item (recipient,sender,key.2)
      have nonnegative := productive_transfer_nonnegative seed old p work item (recipient,key.2)
      rw [same] at bound nonnegative
      rw [same]
      linarith
  · exact incoming_nonnegative seed item key

theorem actual_productive_and_gross_credits_share_one_transfer
    (old : Party × Good → ℚ) (p g : Bool) (work : Working Party Good)
    (item : ExecutionItem Party Good Port Technology Instrument) (key : Party × Good) :
    productiveCredit seed old p g work item key + grossAtRecipient seed old p g work item key ≤
      incoming seed item key := by
  unfold productiveCredit Kernel.productiveCredit
  split
  · split <;> try simpa only [grossAtRecipient,‹_›,zero_add] using incoming_nonnegative seed item key
    next sender recipient goods operation =>
      split
      · next eligible =>
          simp only [grossAtRecipient,operation,if_pos eligible.2]
          have same := eligible.2
          rw [same]
          exact (sub_add_cancel _ _).le
      · simpa only [zero_add] using
          gross_at_this_recipient_is_inside_this_actual_credit seed old p g work item key
  · simpa only [zero_add] using
      gross_at_this_recipient_is_inside_this_actual_credit seed old p g work item key

def charged (old : Party × Good → ℚ) (p g : Bool) (key : Party × Good) :
    Working Party Good → List (ExecutionItem Party Good Port Technology Instrument) → ℚ
  | _, [] => 0
  | work, item :: tail =>
      productiveCredit seed old p g work item key + grossAtRecipient seed old p g work item key +
        charged old p g key (afterItem seed old p g work item) tail

theorem all_original_items_share_only_their_original_actual_credits
    (old : Party × Good → ℚ) (p g : Bool) (key : Party × Good)
    (work : Working Party Good) (items : List (ExecutionItem Party Good Port Technology Instrument)) :
    charged seed old p g key work items ≤ (items.map fun item => incoming seed item key).sum := by
  induction items generalizing work with
  | nil => exact le_rfl
  | cons item tail inherited =>
      exact add_le_add (actual_productive_and_gross_credits_share_one_transfer seed old p g work item key)
        (inherited (afterItem seed old p g work item))

theorem the_one_actual_word_never_spends_its_incoming_material_twice
    (old : Party × Good → ℚ) (p g : Bool) (work : Working Party Good)
    (before : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument)
    (key : Party × Good) :
    charged seed old p g key work ((actualLaw seed).rawItems before word) ≤
      (((actualLaw seed).rawItems before word).map fun item => incoming seed item key).sum :=
  all_original_items_share_only_their_original_actual_credits seed old p g key work _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Allocation
