import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Factory
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Refusal.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Total

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot UniversalRootGrammar
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)


/-- The postcondition is indexed by the branch the source factory actually
selects, including its exact original refusal payload. -/
def ActualCofinalDispositionAt : Prop :=
  match Boundary.Completion.Landing.registerFromActualEvent root boundary with
  | .inl admitted =>
      (∀ point, Nonempty (SourceNativeLivingTemporalCausalEntryAuthorityAt
        (Boundary.Completion.Landing.completedRoot root boundary)
        (.cofinal (Boundary.Completion.Landing.actualVisit root boundary)) (admitted.entry point)) ∧
        (admitted.answerAndNext point).nextCurrent =
          (Boundary.Completion.Landing.completedRoot root boundary).generatedNextCurrentAt
            (.cofinal (Boundary.Completion.Landing.actualVisit root boundary))) ∧
      (∀ cut original, (admitted.entry (Boundary.Completion.includeRow root boundary cut original)).claim =
        original.claim ∧ (admitted.entry (Boundary.Completion.includeRow root boundary cut original)).progressBudget ≤
          original.progressBudget)
  | .inr failure =>
      ∀ recognition : SourceNativeDependentFaceFamilyRecognitionAt (Boundary.Completion.recordedRoot root boundary),
        (Boundary.Completion.Landing.Refusal.compiled root boundary recognition failure).presentedEffect = failure ∧
        ¬ (Boundary.Completion.Landing.Refusal.compiled root boundary recognition failure).useDisposition.IsRooted ∧
        type_of% ((Boundary.Completion.Landing.Refusal.program root boundary recognition failure).generate.rootLedgerAndNext_factorize)

theorem the_actual_cofinal_factory_registers_or_rejects_at_the_same_root :
    ActualCofinalDispositionAt root boundary := by
  unfold ActualCofinalDispositionAt
  cases Boundary.Completion.Landing.registerFromActualEvent root boundary with
  | inl admitted =>
      exact ⟨fun point => ⟨⟨admitted.authority point⟩,admitted.answer_is_the_same_source_generated_next point⟩,
        fun cut original => admitted.every_original_claim_is_registered_without_refill cut original⟩
  | inr failure =>
      intro recognition
      exact ⟨rfl,Boundary.Completion.Landing.Refusal.the_rejected_registration_has_no_rooted_authority
        root boundary recognition failure,
        Boundary.Completion.Landing.Refusal.the_original_root_whole_ledger_and_next_are_retained
          root boundary recognition failure⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Total
