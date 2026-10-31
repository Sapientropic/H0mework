import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public.Installation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument : Type} {N : WorldRelationNetwork}
  (current : Context (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) N)

theorem nextBasic_keeps_the_complete_original_entry : HEq (nextBasic current).row current.row := by
  let step := Sparse.Compiler.successor (code current) false
  have canonical := Abolition.Accounting.Root.Compiler.canonical_destination_heq
    (targetRoot current).toAuthoritativeRoot.toLedgerRoot false step.targetCurrent step.next_eq step current.row
  have same := eq_of_heq (Sparse.Compiler.successor_destination (code current) false)
  have destination := congrArg (fun map => (map current.row).1) same
  exact canonical.trans (heq_of_eq destination)

theorem next_keeps_the_complete_original_entry : HEq (next current).row current.row :=
  nextBasic_keeps_the_complete_original_entry (Source.native current)

theorem next_keeps_the_same_original_key : (next current).row.1 = current.row.1 :=
  congrArg Sigma.fst (eq_of_heq (next_keeps_the_complete_original_entry current))

theorem next_keeps_the_same_original_claim : (next current).row.claim = current.row.claim :=
  congrArg OpenResponsibilityAt.claim (eq_of_heq (next_keeps_the_complete_original_entry current))

theorem next_keeps_the_same_original_budget : (next current).row.progressBudget = current.row.progressBudget :=
  congrArg OpenResponsibilityAt.progressBudget (eq_of_heq (next_keeps_the_complete_original_entry current))

theorem next_keeps_the_entire_old_world_support : Context.support (next current) = Context.support current := rfl

theorem next_keeps_the_original_roster : Context.readMembers (next current) = Context.readMembers current :=
  Context.readMembers_eq _

theorem the_context_before_the_actual_write_is_the_original_context :
    (activeFace (Source.native current) (Sparse.Compiler.initialVisit (code (Source.native current)))).rootRead =
      Context.readContext current := rfl

theorem the_context_after_the_actual_write_is_the_enacted_context :
    Context.readContext (next current) = (law current,Context.readMembers current) := Context.readContext_eq _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public
