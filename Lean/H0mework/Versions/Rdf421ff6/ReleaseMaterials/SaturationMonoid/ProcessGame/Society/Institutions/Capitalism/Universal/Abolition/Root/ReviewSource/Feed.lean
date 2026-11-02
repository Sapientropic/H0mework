import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Declaration

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def sourceAlphabet (current : (ProgrammeSource.V input).Current) :=
  input.localAttempts (ProgrammeSource.rawCurrent input current) ++ ProgrammeSource.rawEvent input current

/-- Coverage is this occurrence's declared task. Earlier disclosures are
retained by `pastDisclosures`; this is not a claim that unknown tasks are empty. -/
inductive ReviewFeedAt (current : (ProgrammeSource.V input).Current) (bound : Nat) : Type
  | planning (task : PublicFunction.PublicTaskSpec Party Good)
      (original : taskOfPayload (originalPayload input current) = some task)
      (outcome : PublicFunction.PlanningOutcome input.law (ProgrammeSource.rawCurrent input current)
        task (sourceAlphabet input current) bound)
      (generated : PublicFunction.compile input.law (ProgrammeSource.rawCurrent input current)
        task (sourceAlphabet input current) bound = outcome)
  | disclosure (blocker : DisclosureBlockerAt input current)

/-- This finite calculation has no prescribed refusal, replacement input,
successful plan, empty-task default or future table. -/
def sourceReviewFeed (current : (ProgrammeSource.V input).Current) (bound : Nat) : ReviewFeedAt input current bound :=
  match discloseTask input current with
  | .declared task original => .planning task original
      (PublicFunction.compile input.law (ProgrammeSource.rawCurrent input current)
        task (sourceAlphabet input current) bound) rfl
  | .unresolved blocker => .disclosure blocker

/-- A dependent source face over the existing whole write. No root or
process is constructed or activated by this subordinate feed. -/
def reviewProjection (bound : Nat) : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} occurrence _ =>
    SourceNativeLedgerEvolutionAt (ProgrammeSource.source input) occurrence × ReviewFeedAt input current bound
  project := fun _ {current} occurrence _ =>
    ⟨(ProgrammeSource.ledgerCompiler input).compile occurrence, sourceReviewFeed input current bound⟩

theorem source_feed_keeps_the_literal_original_whole_write
    (bound : Nat) (current : (ProgrammeSource.V input).Current) :
    ((reviewProjection input bound).project () (ProgrammeSource.emitted input current) ()).1 =
      (ProgrammeSource.ledgerCompiler input).compile (ProgrammeSource.emitted input current) := rfl

theorem source_feed_does_not_reinterpret_the_physical_next (current : (ProgrammeSource.V input).Current) :
    ProgrammeSource.rawCurrent input (ProgrammeSource.next input current) =
      input.law.next (ProgrammeSource.rawCurrent input current) (ProgrammeSource.rawEvent input current) :=
  ProgrammeSource.actual_raw_next input current

theorem a_static_input_produces_a_disclosure_blocker_not_an_empty_task
    (fixed : input.emission? = none) (current : (ProgrammeSource.V input).Current) (bound : Nat) :
    ∃ blocker : DisclosureBlockerAt input current,
      sourceReviewFeed input current bound = .disclosure blocker ∧
      blocker.actualNextEntry input = ProgrammeSource.targetEntry input current .inherited := by
  have missing : taskOfPayload (originalPayload input current) = none := by
    cases current with
    | bootstrap => rfl
    | running current past =>
        change taskOfPayload (writtenPayload input current past
          (ProgrammeSource.sourceEntry input (.running current past) .inherited)) = none
        rw [every_original_row_writes_the_same_payload]
        simp only [ProgrammeSource.observation?, fixed, Option.map_none, taskOfPayload, Option.bind_none]
  cases result : discloseTask input current with
  | declared task original => cases missing.symm.trans original
  | unresolved blocker =>
      refine ⟨blocker, ?_, blocker.same_row_and_actual_next input⟩
      simp only [sourceReviewFeed, result]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.sourceReviewFeed

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.source_feed_keeps_the_literal_original_whole_write

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.a_static_input_produces_a_disclosure_blocker_not_an_empty_task
