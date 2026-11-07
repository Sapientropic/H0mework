import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

def sourceSuccessor (current : Current) : SourceNativeLedgerGeneratedSuccessorAt
    (emitted root boundary current) ((ledgerRoot root boundary).generatedLedgerAt current) := by
  cases current <;> exact PUnit.unit

theorem sourceSuccessor_current (current : Current) :
    (sourceSuccessor root boundary current).targetCurrent = next current := by
  cases current <;> rfl

theorem the_actual_first_whole_write_is_the_source_registration :
    (sourceSuccessor root boundary (.inr 0)).ledgerEvolution = firstLedger root boundary :=
  eq_of_heq (patch_is_the_complete_source_evolution root boundary (.inr 0))

theorem the_actual_first_write_consumes_every_original_registration
    (point : Carrier root boundary) (same) :
    (sourceSuccessor root boundary (.inr 0)).ledgerEvolution.destination
      (landingRow root boundary point same) =
      ⟨landingRow root boundary point same,
        .transferred (.inr (registrationReceipt root boundary point)) rfl rfl (Nat.le_refl _)⟩ :=
  congrArg (fun whole => whole.destination (landingRow root boundary point same))
    (the_actual_first_whole_write_is_the_source_registration root boundary)

theorem the_actual_first_write_preserves_every_old_landing_row
    (old : OpenResponsibilityAt N (root.toAuthoritativeRoot.toRoot.supportAt boundary.current)) :
    (sourceSuccessor root boundary (.inr 0)).ledgerEvolution.destination
      (oldRow root boundary true old) = ⟨oldRow root boundary true old,.carried rfl (HEq.rfl)⟩ :=
  congrArg (fun whole => whole.destination (oldRow root boundary true old))
    (the_actual_first_whole_write_is_the_source_registration root boundary)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing
