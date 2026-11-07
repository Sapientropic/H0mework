import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Compatibility
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Face
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Submission.SourceNativeObserverConsumerSubmissionCompiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Refusal

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open UniversalRootGrammar
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
  (recognition : SourceNativeDependentFaceFamilyRecognitionAt (recordedRoot root boundary))
  (failure : LineageFailure root boundary)

def attempt : SourceNativeObserverConsumerAttemptAt recognition (.cofinal boundary)
    recognition.law.vocabulary.actualScenario
    (ExactTemporalCausalRootEvent root.toAuthoritativeRoot.toLedgerRoot)
    (LineageFailure root boundary) (LineageFailure root boundary) where
  observer := ⟨id⟩
  readout := ⟨fun _ => failure⟩
  consumer := id

def program := uncertifiedAuthoritySubmissionProgramAt (attempt root boundary recognition failure)

def compiled := compileSourceNativeObserverConsumerSubmissionAt (program root boundary recognition failure).generate

def rejection : SourceNativeObserverConsumerRejectionAt (program root boundary recognition failure).generate :=
  .uncertified rfl

/-- The failure is selected from the same primitive source inspection,
then compiled into its own exact-root rejection program. -/
def fromActualSource : PLift (Compatible root boundary) ⊕
    (Sigma fun failure : LineageFailure root boundary =>
      SourceNativeObserverConsumerRejectionAt (program root boundary recognition failure).generate) :=
  match inspectCompatibility root boundary with
  | .inl accepted => .inl accepted
  | .inr failure => .inr ⟨failure,rejection root boundary recognition failure⟩

theorem the_original_source_rejects_the_incompatible_registration :
    (compiled root boundary recognition failure).useDisposition =
      .rejected (rejection root boundary recognition failure) := rfl

theorem the_refusal_retains_the_original_liability_and_actual_budget :
    (compiled root boundary recognition failure).presentedEffect = failure ∧
      (face root boundary).rootRead (includeRow root boundary failure.cut failure.original) =
        (failure.original.claim,minimumBudget root boundary failure.cut failure.original) := ⟨rfl,rfl⟩

theorem the_rejected_registration_has_no_rooted_authority :
    ¬ (compiled root boundary recognition failure).useDisposition.IsRooted := fun impossible => impossible

theorem the_original_root_whole_ledger_and_next_are_retained :
    type_of% ((program root boundary recognition failure).generate.rootLedgerAndNext_factorize) :=
  (program root boundary recognition failure).generate.rootLedgerAndNext_factorize

theorem the_original_failure_is_the_visible_residual_bearer :
    (SourceNativeObserverConsumerRejectionAt.residualBearer
      (generated := (program root boundary recognition failure).generate)).generated.presentedEffect = failure := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Refusal
