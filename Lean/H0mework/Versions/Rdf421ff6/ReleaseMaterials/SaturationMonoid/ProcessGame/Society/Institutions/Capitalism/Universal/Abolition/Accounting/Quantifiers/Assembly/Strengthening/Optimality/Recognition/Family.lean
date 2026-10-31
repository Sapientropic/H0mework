import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition.Submission
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource.Complete
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Completion.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.UniversalRootGrammar
open Countermodels.Nonattainment
noncomputable section

def familyProgram (n : Nat) (index : Fin 7) :=
  actualProgram (RootedSource.actualHistory n index).full.root (RootedSource.actualHistory n index).visit

/-- Actual execution pays the task; the complete authority readout
certifies its same-root occurrence. Neither substitutes for the other. -/
structure RootedCompleteAt (n : Nat) : Prop where
  executed : RootedSource.RootExecutedAt n
  sourceComplete : Completion.SourceAdmitted (programme n)
  classified : ∀ index : Fin 7,
    (compileSourceNativeObserverConsumerSubmissionAt (familyProgram n index).generate).useDisposition.IsRooted

theorem the_actual_complete_family_is_certified_on_its_original_roots (n : Nat) : RootedCompleteAt n where
  executed := RootedSource.every_original_source_candidate_is_actually_root_executed n
  sourceComplete := Completion.each_actual_family_member_passes_the_complete_original_source_test n
  classified := fun index => the_exact_actual_root_submission_is_rooted
    (RootedSource.actualHistory n index).full.root (RootedSource.actualHistory n index).visit

theorem every_completed_candidate_has_a_strictly_cheaper_rooted_complete_continuation
    (code : Code) (cleared : RawCleared code) :
    RootedCompleteAt (indexFor (Cost.value fullReading input before code - 1)) ∧
      Cost.value fullReading input genesis (initialHistory ++ improve code) <
        Cost.value fullReading input genesis (initialHistory ++ code) :=
  ⟨the_actual_complete_family_is_certified_on_its_original_roots _,
    (Completion.any_completed_raw_candidate_has_a_cheaper_fully_accounted_source_completion code cleared).2⟩

theorem no_completed_candidate_can_beat_all_source_generated_rooted_clearances :
    ¬ ∃ code : Code, RawCleared code ∧ ∀ n, RootedCompleteAt n →
      Cost.value fullReading input genesis (initialHistory ++ code) ≤
        Cost.value fullReading input genesis (initialHistory ++ programme n) := by
  rintro ⟨code,cleared,least⟩
  have better := every_completed_candidate_has_a_strictly_cheaper_rooted_complete_continuation code cleared
  exact (not_lt_of_ge (least _ better.1)) better.2

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition
