import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Checks
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Planning

/-!
# The original occurrence supplies the review context

Review starts from the actual generated successor of the challenged event,
with that event's full original M0 cohort. Candidate words are source code
from its current local attempts and emitter, never chosen successful futures.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material

open Source.Program Source.ProgrammeFace
open Source.ProgrammeControl.Kernel.AssetAuthority
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)

def afterVisit (visit : RootFace.Visit input) : RootFace.Visit input := visit.next rfl

def reviewCurrent (visit : RootFace.Visit input) : RawCurrent Party Good Technology Instrument :=
  Root.ProgrammeSource.rawCurrent input (afterVisit input visit).current

def originalMembers (visit : RootFace.Visit input) : List Party :=
  ActualBirth.participants input visit

def availableRequests (visit : RootFace.Visit input) :
    List (Request Party Good Port Technology Instrument) :=
  input.localAttempts (reviewCurrent input visit) ++
    Root.ProgrammeSource.wordAt input (reviewCurrent input visit)

def candidateWords (visit : RootFace.Visit input) (budget : Nat) :=
  PublicFunction.words (availableRequests input visit) budget

omit [DecidableEq Port] in
theorem reviewCurrent_is_original_next (visit : RootFace.Visit input) :
    reviewCurrent input visit = input.law.next
      (Root.ProgrammeSource.rawCurrent input visit.current)
      (Root.ProgrammeSource.rawEvent input visit.current) :=
  Root.ProgrammeSource.actual_raw_next input visit.current

omit [DecidableEq Port] in
theorem original_members_not_deleted (visit : RootFace.Visit input)
    (person : Party) (present : person ∈ originalMembers input visit) :
    person ∈ ActualBirth.participants input (afterVisit input visit) :=
  ActualBirth.original_participant_is_retained input visit rfl person present

omit [DecidableEq Port] in
theorem candidateWords_complete (visit : RootFace.Visit input) (budget : Nat)
    (word : RawEvent Party Good Port Technology Instrument) :
    word ∈ candidateWords input visit budget ↔ word.length ≤ budget ∧
      ∀ request ∈ word, request ∈ availableRequests input visit :=
  PublicFunction.mem_words_iff (availableRequests input visit) budget word

/-- Every paid period retains a living obligation for each original member;
the participant list cannot be replaced by only the candidate's providers. -/
theorem checked_candidate_keeps_original_life (visit : RootFace.Visit input)
    (word : RawEvent Party Good Port Technology Instrument)
    (checked : PeriodChecks input (reviewCurrent input visit) (originalMembers input visit) word)
    (person : Party) (present : person ∈ originalMembers input visit) :
    Exit.Necessity.BundlePaid input.law (reviewCurrent input visit) word person
        (input.law.necessities (reviewCurrent input visit) person) .necessity ∧
      Exit.Necessity.BundlePaid input.law (reviewCurrent input visit) word person
        (input.law.mandatoryMaintenance (reviewCurrent input visit) person) .maintenance :=
  checked_period_original_member_needs input _ _ word checked person present

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.reviewCurrent_is_original_next
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.checked_candidate_keeps_original_life
