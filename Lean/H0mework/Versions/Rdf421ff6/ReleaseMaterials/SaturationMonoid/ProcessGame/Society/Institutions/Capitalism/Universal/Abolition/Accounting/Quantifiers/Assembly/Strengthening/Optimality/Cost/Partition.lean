import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.Reading

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Abolition.Root Abolition.Root.Registered
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (item : ExecutionItem Party Good Port Technology Instrument) (party : Party) (good : Good)

omit [DecidableEq Instrument] in
/-- Every accepted original debit has exactly one resource channel, or is
an original transfer/settlement leg. Rejected debit remains exactly zero. -/
theorem every_actual_debit_is_in_the_complete_source_partition :
    flowAt (law.actualDebit item.before item.request) party good =
      (channels.map (fun channel => flowAt (actualPart law item.before item.request channel) party good)).sum +
        flowAt (movingDebit law item .transfer) party good + flowAt (movingDebit law item .settlement) party good := by
  by_cases accepted : law.Valid item.before item.request
  · cases operation : item.request.operation
    case use bearer goods purpose =>
      cases purpose <;> simp [channels,actualPart,part,movingDebit,movement?,RawLaw.actualDebit,RawLaw.debit,
        accepted,operation,locate,flowAt,amount]
    all_goals simp [channels,actualPart,part,movingDebit,movement?,RawLaw.actualDebit,RawLaw.debit,
      accepted,operation,locate,flowAt,amount,List.map_append,List.sum_append]
  · simp [channels,actualPart,movingDebit,RawLaw.actualDebit,accepted,flowAt,amount]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost
