import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.InitialAdmission.Failure

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Capital

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root
open Registered Functions.Revision

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (origin : Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount)
  (failed : InitialObstructionAt origin)

theorem the_actual_obstruction_target_keeps_the_entire_original_ledger :
    HEq (InitialAdmission.Failure.generated origin failed).target.initialOpenLedger
      (Macro.Raw.Target.initialLedger origin.native origin.data origin.reader origin.germ) := HEq.rfl

theorem an_obstruction_cannot_erase_a_bearer_claim_or_unspent_budget
    (entry : OpenResponsibilityAt origin.native.N (origin.native.sourceSupport origin.visit.current)) :
    (((InitialAdmission.Failure.generated origin failed).target.initialOpenLedger).forward entry).1 = entry.1 ∧
      (((InitialAdmission.Failure.generated origin failed).target.initialOpenLedger).forward entry).claim = entry.claim ∧
      (((InitialAdmission.Failure.generated origin failed).target.initialOpenLedger).forward entry).progressBudget =
        entry.progressBudget :=
  ⟨Macro.Raw.Target.initial_ledger_preserves_responsibility origin.native origin.data origin.reader origin.germ entry,
    Macro.Raw.Target.initial_ledger_preserves_claim origin.native origin.data origin.reader origin.germ entry,
    Macro.Raw.Target.initial_ledger_preserves_budget origin.native origin.data origin.reader origin.germ entry⟩

#print axioms the_actual_obstruction_target_keeps_the_entire_original_ledger
#print axioms an_obstruction_cannot_erase_a_bearer_claim_or_unspent_budget

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Capital
