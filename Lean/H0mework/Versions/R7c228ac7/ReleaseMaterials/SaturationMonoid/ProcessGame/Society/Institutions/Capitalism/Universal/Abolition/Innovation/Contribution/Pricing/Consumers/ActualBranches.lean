import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.ActualQuote

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual

open Source.Program
open SaturationMonoid.ProcessGame.Society.PublicFunction

noncomputable section

abbrev law := PublicFunction.physicalLaw Abolition.Accounting.Quantifiers.Joint.Consumers.Compact.law

def priceSuffix : List R := [Settlement.issue law false true () false 4,Settlement.settle law false true () false 4]
def wholeWord (loss : ℚ) := mechanism.word (nature loss) ++ priceSuffix

theorem every_actual_quoted_branch_is_one_of_the_original_two
    (schedule : Root.ScheduleAt source mechanism) (event : schedule.programme.QuotedNature) :
    event.val = nature 2 ∨ event.val = nature 4 := by
  have original := event.property
  change Distributed.Event.adversary event.val ∈
    [Distributed.Event.adversary (nature 2),Distributed.Event.adversary (nature 4)] at original
  simpa only [List.mem_cons,List.not_mem_nil,or_false,Distributed.Event.adversary.injEq] using original

theorem every_actual_branch_has_its_paid_original_signal
    (schedule : Root.ScheduleAt source mechanism) (event : schedule.programme.QuotedNature) :
    schedule.programme.paidSignal event.val = some signal := by
  have changed := congrArg (fun programme : Trials.Mechanism Bool Bool Bool Unit Unit =>
    (programme.paidSignal (event.val : R)).map Fin.val)
    (every_actual_schedule_uses_the_original_unreloaded_programme schedule)
  have small : (mechanism.paidSignal event.val).map Fin.val = some 0 := by
    rcases every_actual_quoted_branch_is_one_of_the_original_two schedule event with first | second
    · rw [first]; decide +kernel
    · rw [second]; decide +kernel
  have numeric := changed.trans small
  cases observed : schedule.programme.paidSignal event.val with
  | none => rw [observed] at numeric; cases numeric
  | some actualSignal =>
      rw [observed] at numeric
      have sameSignal : actualSignal = signal := Fin.ext (Option.some.inj numeric)
      cases sameSignal
      rfl

theorem every_actual_branch_selects_the_original_computed_plan
    (schedule : Root.ScheduleAt source mechanism) (event : schedule.programme.QuotedNature) :
    ∃ plan : Source.Quote (schedule.rows signal), plan.transfer = 4 ∧
      schedule.select event.val = .priced signal event.property
        (every_actual_branch_has_its_paid_original_signal schedule event) plan := by
  obtain ⟨plan,selected,amount⟩ := every_actual_schedule_has_its_computed_four_plan schedule
  have original := (Source.original_nature_iff schedule.programme event.val).mpr event.property
  refine ⟨plan,amount,?_⟩
  have paid := every_actual_branch_has_its_paid_original_signal schedule event
  unfold Source.Schedule.select
  split
  · split
    · rename_i observed
      have impossible := observed.symm.trans paid
      cases impossible
    · rename_i actualSignal observed
      have sameSignal : actualSignal = signal := Option.some.inj (observed.symm.trans paid)
      subst actualSignal
      split
      · rename_i generatedPlan computed
        have samePlan := Source.QuoteOutcome.priced.inj (computed.symm.trans selected)
        subst generatedPlan
        rfl
      · rename_i issue computed
        cases computed.symm.trans selected
  · rename_i unsupported
    exact (unsupported original).elim

theorem the_actual_branch_requests_have_no_external_price_parameter
    (schedule : Root.ScheduleAt source mechanism) (event : schedule.programme.QuotedNature) :
    schedule.requests event.val false = mechanism.word event.val ++ priceSuffix := by
  obtain ⟨plan,amount,selected⟩ := every_actual_branch_selects_the_original_computed_plan schedule event
  simp only [Source.Schedule.requests,Source.Schedule.payment,selected]
  change schedule.programme.word event.val ++
    (Settlement.compile (Root.sourceInput source).law (schedule.programme.after event.val)
      false true () false plan.transfer).word = _
  have bodyEq := congrArg (fun programme : Trials.Mechanism Bool Bool Bool Unit Unit => programme.word (event.val : R))
    (every_actual_schedule_uses_the_original_unreloaded_programme schedule)
  have afterEq := congrArg (fun programme : Trials.Mechanism Bool Bool Bool Unit Unit => programme.after (event.val : R))
    (every_actual_schedule_uses_the_original_unreloaded_programme schedule)
  rw [bodyEq,afterEq,the_quote_uses_the_original_public_physical_law,amount]
  rcases every_actual_quoted_branch_is_one_of_the_original_two schedule event with first | second
  · rw [first]; decide +kernel
  · rw [second]; decide +kernel

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual
