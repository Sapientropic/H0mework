import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion.Natural
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion.Public

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program Innovation
open Evolution.Ingress.Joint Evolution.Ingress.Joint.Material

noncomputable section

attribute [local irreducible] Execution.Selected.items Joint.Planning.selected Joint.Planning.actualNext Joint.Current.advance

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Joint.window seed))

structure RootedQuantifierCoreAt : Prop where
  actual_execution : Runtime.RootedJointPaymentAt seed claim
  all_actual_capital_forms : ∀ n, Global.NoCapital (contextFace seed claim n).rootRead.1
  actual_sparse_next : type_of% (Continuation.actual_resumption_is_the_same_sparse_current seed claim
    (Runtime.temporalAt seed claim (Execution.Selected.items seed claim).length)
    (Runtime.authorityAt seed claim (Execution.Selected.items seed claim).length))
  funded_open_histories : ∀ (enough : Joint.Planning.Enough seed claim (shared seed claim))
    {target : Evolution.Sparse.Current (oldN := Continuation.base seed claim) seed.claim}
    (history : Evolution.Sparse.History.Actual seed.claim (futureSource seed claim) target) members good,
    type_of% (every_coalition_has_its_full_account_through_every_actual_open_mechanism_history
      seed claim enough history members good)
  whole_original_background : ∀ {target : Evolution.Sparse.Current (oldN := Continuation.base seed claim) seed.claim}
    (history : Evolution.Sparse.History.Actual seed.claim (futureSource seed claim) target),
    type_of% (every_open_mechanism_history_keeps_the_whole_actual_native_background seed claim history)
  whole_original_finance : ∀ {target : Evolution.Sparse.Current (oldN := Continuation.base seed claim) seed.claim}
    (history : Evolution.Sparse.History.Actual seed.claim (futureSource seed claim) target),
    type_of% (every_open_history_retains_the_exact_original_financial_account seed claim history)
  original_gross_paid : ∀ (enough : Joint.Planning.Enough seed claim (shared seed claim))
    {target : Evolution.Sparse.Current (oldN := Continuation.base seed claim) seed.claim}
    (history : Evolution.Sparse.History.Actual seed.claim (futureSource seed claim) target),
    type_of% (every_open_history_keeps_the_actual_paid_gross_responsibility seed claim enough history)
  every_natural_stage : ∀ (enough : Joint.Planning.Enough seed claim (shared seed claim)) submitted n members good,
    type_of% (every_stage_of_every_open_mechanism_sequence_keeps_capital_excluded_and_every_coalition_accounted
      seed claim enough submitted n members good)
  prefix_locality : ∀ left right n, (∀ i < n, left i = right i) →
    observedCurrent seed claim left n = observedCurrent seed claim right n
  every_registered_source : ∀ {N : WorldRelationNetwork}
    (source : Evolution.Factory.Context (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument) N),
    Evolution.Factory.Public.EnactedAt source ∧
      Global.NoCapital (Evolution.Factory.Context.readLaw (Evolution.Factory.Public.next source))

theorem the_same_actual_root_closes_its_joint_open_quantifier_core : RootedQuantifierCoreAt seed claim where
  actual_execution := Runtime.the_original_root_executes_its_joint_payment_and_complete_native_account seed claim
  all_actual_capital_forms := every_actual_native_root_excludes_all_capital seed claim
  actual_sparse_next := Continuation.actual_resumption_is_the_same_sparse_current seed claim _ _
  funded_open_histories := fun enough {target} history members good =>
    every_coalition_has_its_full_account_through_every_actual_open_mechanism_history
      seed claim enough (target := target) history members good
  whole_original_background := every_open_mechanism_history_keeps_the_whole_actual_native_background seed claim
  whole_original_finance := every_open_history_retains_the_exact_original_financial_account seed claim
  original_gross_paid := fun enough {target} history =>
    every_open_history_keeps_the_actual_paid_gross_responsibility seed claim enough (target := target) history
  every_natural_stage := every_stage_of_every_open_mechanism_sequence_keeps_capital_excluded_and_every_coalition_accounted seed claim
  prefix_locality := unsubmitted_future_inputs_do_not_change_the_actual_observed_current seed claim
  every_registered_source := every_registered_source_has_its_actual_capital_excluding_public_next

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion
