import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Total.Cofinal.Disposition

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Total

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot UniversalRootGrammar
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)


structure ActualCofinalRegistrationClosedAt : Prop where
  original_event : type_of% (Boundary.Completion.Landing.actualVisit_raw_event root boundary)
  original_target : type_of% (Boundary.Completion.Landing.actualVisit_raw_target root boundary)
  original_path : ∀ cut, type_of% (Boundary.Completion.Landing.actualVisit_raw_path root boundary cut)
  original_finite_ledger : ∀ cut,
    type_of% (Boundary.Completion.Landing.the_new_finite_ledger_is_the_original_whole_ledger root boundary cut)
  no_future_preloading : ∀ cut point,
    type_of% (Boundary.Completion.Landing.no_completed_standing_is_active_at_a_finite_cut root boundary cut point)
  actual_first_whole_write :
    type_of% (Boundary.Completion.Landing.the_actual_first_whole_write_is_the_source_registration root boundary)
  retained_theory : type_of% (Boundary.Completion.Landing.the_completed_root_retains_the_original_theory root boundary)
  retained_observations : ∀ current,
    type_of% (Boundary.Completion.Landing.the_completed_root_retains_every_original_observation root boundary current)
  retained_queries : ∀ current projection,
    type_of% (Boundary.Completion.Landing.the_completed_root_retains_every_original_query root boundary current projection)
  source_disposition : ActualCofinalDispositionAt root boundary
  typed_refusal : ∀ recognition failure lawProgram,
    Nonempty (TypedRejectionVisibleResidualAt
      (Boundary.Completion.Landing.Refusal.legislation root boundary recognition failure lawProgram))

theorem the_original_cofinal_event_generates_its_whole_registration_or_exact_refusal :
    ActualCofinalRegistrationClosedAt root boundary where
  original_event := Boundary.Completion.Landing.actualVisit_raw_event root boundary
  original_target := Boundary.Completion.Landing.actualVisit_raw_target root boundary
  original_path := Boundary.Completion.Landing.actualVisit_raw_path root boundary
  original_finite_ledger := Boundary.Completion.Landing.the_new_finite_ledger_is_the_original_whole_ledger root boundary
  no_future_preloading := Boundary.Completion.Landing.no_completed_standing_is_active_at_a_finite_cut root boundary
  actual_first_whole_write := Boundary.Completion.Landing.the_actual_first_whole_write_is_the_source_registration root boundary
  retained_theory := Boundary.Completion.Landing.the_completed_root_retains_the_original_theory root boundary
  retained_observations := Boundary.Completion.Landing.the_completed_root_retains_every_original_observation root boundary
  retained_queries := Boundary.Completion.Landing.the_completed_root_retains_every_original_query root boundary
  source_disposition := the_actual_cofinal_factory_registers_or_rejects_at_the_same_root root boundary
  typed_refusal := fun recognition failure lawProgram =>
    ⟨Boundary.Completion.Landing.Refusal.rejectedAtTheOriginalRoot root boundary recognition failure lawProgram⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Total
