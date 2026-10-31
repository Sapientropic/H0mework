import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public.Account
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public.Binding

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type} {N : WorldRelationNetwork}
  (current : Context (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) N)

structure EnactedAt : Prop where
  compilation : (state current).compileInquiry PUnit.unit = .actualAction (enact current)
  actual_answer : (enact current).target.answer = Source.readAnswer current
  actual_next : (RootInquiryProcessNode.answered (presentation current) PUnit.unit).erase = Context.erase (next current)
  initial_no_fresh : type_of% (enact current).target.initialLedgerNoFresh
  complete_destination : type_of% (Sparse.Compiler.successor_destination (code (Source.native current)) false)
  complete_origin : type_of% (Sparse.Compiler.successor_origin (code (Source.native current)) false)
  all_old_queries : type_of% (every_old_query_is_retained (Source.native current))
  complete_original_entry : HEq (next current).row current.row
  original_key : (next current).row.1 = current.row.1
  original_claim : (next current).row.claim = current.row.claim
  original_budget : (next current).row.progressBudget = current.row.progressBudget
  original_world_support : Context.support (next current) = Context.support current
  original_raw : Context.readRaw (next current) = Context.readRaw current
  original_members : Context.readMembers (next current) = Context.readMembers current
  original_context_before_write : type_of% (the_context_before_the_actual_write_is_the_original_context current)
  enacted_context_after_write : Context.readContext (next current) = (law current,Context.readMembers current)
  active_interpreter : Context.readLaw (next current) = law current
  no_private_permission : ∀ technology port person,(Context.readLaw (next current)).allowed technology port person = true
  no_policy_veto : (Context.readLaw (next current)).policy = .unrestricted
  source_rules_retained : type_of% (the_change_retains_all_other_source_rules current)
  native_continuation_binding : ∀ bound : BoundContinuation (next current),bound.program.law = law current

/-- This enacts the active interpreter and keeps all original costs and
liabilities. It makes no claim that a material body or a Needs payment occurred. -/
theorem every_source_continuation_has_an_actual_public_context : EnactedAt current where
  compilation := the_source_installs_its_actual_public_context_action current
  actual_answer := the_actual_answer_is_the_source_preparation_face current
  actual_next := the_actual_process_resumes_at_its_public_current current
  initial_no_fresh := (enact current).target.initialLedgerNoFresh
  complete_destination := Sparse.Compiler.successor_destination (code (Source.native current)) false
  complete_origin := Sparse.Compiler.successor_origin (code (Source.native current)) false
  all_old_queries := every_old_query_is_retained (Source.native current)
  complete_original_entry := next_keeps_the_complete_original_entry current
  original_key := next_keeps_the_same_original_key current
  original_claim := next_keeps_the_same_original_claim current
  original_budget := next_keeps_the_same_original_budget current
  original_world_support := next_keeps_the_entire_old_world_support current
  original_raw := next_retains_the_actual_source_raw current
  original_members := next_keeps_the_original_roster current
  original_context_before_write := the_context_before_the_actual_write_is_the_original_context current
  enacted_context_after_write := the_context_after_the_actual_write_is_the_enacted_context current
  active_interpreter := next_reads_the_new_active_interpreter current
  no_private_permission := by intro technology port person; rw [next_reads_the_new_active_interpreter]; rfl
  no_policy_veto := by rw [next_reads_the_new_active_interpreter]; rfl
  source_rules_retained := the_change_retains_all_other_source_rules current
  native_continuation_binding := every_returned_continuation_uses_the_enacted_public_interpreter current

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public
