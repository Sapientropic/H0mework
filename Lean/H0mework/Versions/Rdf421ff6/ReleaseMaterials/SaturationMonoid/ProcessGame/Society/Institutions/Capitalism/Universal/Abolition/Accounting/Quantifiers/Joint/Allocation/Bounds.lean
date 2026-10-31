import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Allocation.Evaluator

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

theorem productive_reservation_is_inside_this_actual_credit (old : Party × Good → ℚ) (p : Bool)
    (work : Working Party Good) (item : ExecutionItem Party Good Port Technology Instrument) (key : Party × Good) :
    productiveTransfer seed old p work item key ≤ incoming seed item key := by
  unfold productiveTransfer Kernel.reservation
  split
  · split <;> try exact incoming_nonnegative seed item key
    split
    · exact (min_le_right _ _).trans (max_eq_right (incoming_nonnegative seed item key)).le
    · exact incoming_nonnegative seed item key
  · exact incoming_nonnegative seed item key

theorem both_rows_share_only_the_one_original_transfer (old : Party × Good → ℚ) (p g : Bool)
    (work : Working Party Good) (item : ExecutionItem Party Good Port Technology Instrument)
    (key : Entitlement.Duty.Key (Party := Party) (Good := Good)) :
    productiveTransfer seed old p work item (key.1,key.2.2) + grossTransfer seed old p g work item key ≤
      incoming seed item (key.1,key.2.2) := by
  have pBound := productive_reservation_is_inside_this_actual_credit seed old p work item (key.1,key.2.2)
  unfold grossTransfer Kernel.gross
  split
  · split <;> try simpa only [add_zero] using pBound
    split
    · have restNonnegative : 0 ≤ incoming seed item (key.1,key.2.2) -
          productiveTransfer seed old p work item (key.1,key.2.2) := sub_nonneg.mpr pBound
      change productiveTransfer seed old p work item (key.1,key.2.2) +
        min (work.gross key) (max 0 (incoming seed item (key.1,key.2.2) -
          productiveTransfer seed old p work item (key.1,key.2.2))) ≤ incoming seed item (key.1,key.2.2)
      rw [max_eq_right restNonnegative]
      have gBound := min_le_right (work.gross key)
        (incoming seed item (key.1,key.2.2) - productiveTransfer seed old p work item (key.1,key.2.2))
      linarith
    · simpa only [add_zero] using pBound
  · simpa only [add_zero] using pBound

theorem each_actual_item_never_refills_gross (old : Party × Good → ℚ) (p g : Bool)
    (work : Working Party Good) (item : ExecutionItem Party Good Port Technology Instrument)
    (key : Entitlement.Duty.Key (Party := Party) (Good := Good)) :
    (afterItem seed old p g work item).gross key ≤ work.gross key :=
  max_le (work.gross_nonnegative key)
    (sub_le_self _ (gross_transfer_nonnegative seed old p g work item key))

theorem actual_source_run_never_refills_gross (old : Party × Good → ℚ) (p g : Bool)
    (gross : Entitlement.Duty.Key (Party := Party) (Good := Good) → ℚ) (nonnegative : ∀ key, 0 ≤ gross key)
    (before : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument)
    (key : Entitlement.Duty.Key (Party := Party) (Good := Good)) :
    (run seed old p g gross nonnegative before word).gross key ≤ gross key := by
  unfold run
  generalize (actualLaw seed).rawItems before word = items
  have all (initial : Working Party Good) :
      (items.foldl (afterItem seed old p g) initial).gross key ≤ initial.gross key := by
    induction items generalizing initial with
    | nil => exact le_rfl
    | cons item rest inherited =>
        exact (inherited (afterItem seed old p g initial item)).trans
          (each_actual_item_never_refills_gross seed old p g initial item key)
  exact all ⟨fun _ => 0,gross,nonnegative⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Allocation
