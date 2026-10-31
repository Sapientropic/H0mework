import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Material.Flows

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Material

open Program ProgrammeFace

universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good]
  (law : RawLaw Party Good Port Technology Instrument)

theorem positive_credit_has_original_recipient (item : ExecutionItem Party Good Port Technology Instrument)
    (party : Party) (good : Good) (positive : 0 < Decoder.acquired law item party good) :
    party ∈ operationParties item.request.operation := by
  by_contra absent
  by_cases accepted : law.Valid item.before item.request
  · cases operation : item.request.operation <;>
      simp only [operation, operationParties, List.mem_cons, not_or] at absent <;>
      simp [Decoder.acquired, RawLaw.actualCredit, accepted, RawLaw.credit, operation,
        flowAt, locate, amount, List.map_map, Function.comp_def, Prod.mk.injEq, absent, Ne.symm] at positive
  · simp [Decoder.acquired, RawLaw.actualCredit, accepted, flowAt, amount] at positive

#print axioms positive_credit_has_original_recipient

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Material
