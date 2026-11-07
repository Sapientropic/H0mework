import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion.Dynamic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program Innovation
open Evolution.Ingress.Joint Evolution.Ingress.Joint.Material
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Joint.window seed))

structure CapitalQuantifiersClosedAt : Prop extends RootedQuantifierCoreAt seed claim where
  native_current : ∀ (enough : Joint.Planning.Enough seed claim (shared seed claim)),
    (Runtime.Resumption.nativeFrame seed claim enough).root = Runtime.Inquiry.root seed claim ∧
      (Runtime.Resumption.nativeFrame seed claim enough).V = Runtime.V seed claim ∧
      type_of% (Runtime.Resumption.the_returned_native_current_is_the_same_completed_original_account seed claim enough) ∧
      type_of% (Runtime.Resumption.the_next_source_context_reads_this_same_actual_raw seed claim enough) ∧
      type_of% (Runtime.Resumption.the_same_completed_root_still_owns_both_zero_budget_historical_rows seed claim enough)
  all_dynamic_source_inputs : ∀ (enough : Joint.Planning.Enough seed claim (shared seed claim))
    {sourceDepth sourceCount : Nat} {review : Option (ReviewPhase.ContextAt seed.input)}
    (origin : Abolition.Functions.Revision.Context (input := seed.input) (review := review)
      seed.depth seed.count 0 0 sourceDepth sourceCount)
    (reader : Macro.Raw.Reader seed.input seed.depth seed.count),
    DynamicDispositionAt seed claim enough origin reader (Abolition.Functions.Revision.InitialAdmission.select origin)
  available_source_plan_forces_continuation : ∀ (enough : Joint.Planning.Enough seed claim (shared seed claim))
    {sourceDepth sourceCount : Nat} {review : Option (ReviewPhase.ContextAt seed.input)}
    (origin : Abolition.Functions.Revision.Context (input := seed.input) (review := review)
      seed.depth seed.count 0 0 sourceDepth sourceCount)
    (reader : Macro.Raw.Reader seed.input seed.depth seed.count),
    type_of% (an_available_source_plan_forces_actual_dynamic_continuation seed claim enough origin reader)

theorem the_original_root_closes_all_capital_quantifiers_and_generates_its_dynamic_future :
    CapitalQuantifiersClosedAt seed claim where
  toRootedQuantifierCoreAt := the_same_actual_root_closes_its_joint_open_quantifier_core seed claim
  native_current := fun enough => ⟨rfl,rfl,
    Runtime.Resumption.the_returned_native_current_is_the_same_completed_original_account seed claim enough,
    Runtime.Resumption.the_next_source_context_reads_this_same_actual_raw seed claim enough,
    Runtime.Resumption.the_same_completed_root_still_owns_both_zero_budget_historical_rows seed claim enough⟩
  all_dynamic_source_inputs := fun enough {_ _} {_} origin reader =>
    the_original_source_generates_its_actual_dynamic_disposition seed claim enough origin reader
  available_source_plan_forces_continuation := fun enough {_ _} {_} origin reader =>
    an_available_source_plan_forces_actual_dynamic_continuation seed claim enough origin reader

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion
