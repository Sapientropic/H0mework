import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholePartyExecution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholePartySource
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Repayment.Recovery (Good)
open WholePartyLift

def command? : Mandate.Command WholeCursorLaw.Party → Option (Mandate.Command OldParty)
  | .propose (.inl actor) => some (.propose actor)
  | .propose (.inr _) => none
  | .accept => some .accept | .renew => some .renew | .exit => some .exit
  | .revoke => some .revoke | .review => some .review

def project (whole : WholeCursorLaw.Current) : OldCurrent where
  stock := fun actor good => whole.stock (.inl actor) good
  claims := fun instrument debtor creditor => whole.claims instrument (.inl debtor) (.inl creditor)
  technology := ⟨whole.technology.technology,whole.technology.version,
    whole.technology.holder.bind WholeCursorLaw.party?,whole.technology.offered.bind WholeCursorLaw.party?,
    whole.technology.last.bind command?⟩
  clock := whole.clock
  round := whole.round

theorem project_current (old : OldCurrent) (outside : Good → ℚ) : project (current old outside) = old := by
  cases old with
  | mk stock claims tech clock round =>
    cases tech with
    | mk technology version holder offered last =>
      cases holder <;> cases offered <;> cases last with
      | none => rfl
      | some cmd => cases cmd <;> rfl

-- Planning certificates have a different carrier. Export their actual reported current and emitted word;
-- the original Machine report has exactly these two fields and is transported in full.
def reportedCurrent (report : ProgrammeSource.ProgrammeReport OldParty Good OldPort OldState Unit) : OldCurrent := by
  cases report with
  | original here _ => exact here
  | @planning _ _ _ _ here _ _ _ _ => exact here

-- Both emit and observe are invoked from the original source, rather than replaced by a word table.
def input (old : ProgrammeSource.Input OldParty Good OldPort OldState Unit) (outside : Good → ℚ) :
    ProgrammeSource.Input WholeCursorLaw.Party Good WholeCursorLaw.Port NewState Unit where
  law := newLaw
  initial := current old.initial outside
  instructions := old.instructions.map request
  emission? := old.emission?.map fun emit => fun whole => (emit (project whole)).map request
  localAttempts := fun whole => (old.localAttempts (project whole)).map request
  observedEmission? := old.observedEmission?.map fun observed =>
    { generate := fun whole =>
        let report := observed.generate (project whole)
        .original (current (reportedCurrent report) outside) ((observed.word report).map request)
      word := ProgrammeSource.ProgrammeReport.word }

theorem word (old : ProgrammeSource.Input OldParty Good OldPort OldState Unit) (outside : Good → ℚ)
    (here : OldCurrent) : ProgrammeSource.wordAt (input old outside) (current here outside) =
      (ProgrammeSource.wordAt old here).map request := by
  cases h : old.emission? <;> cases observed : old.observedEmission? <;>
    simp [input,ProgrammeSource.wordAt,h,observed,project_current,ProgrammeSource.ProgrammeReport.word]

theorem registration (old : ProgrammeSource.Input OldParty Good OldPort OldState Unit) (outside : Good → ℚ) :
    ProgrammeSource.registrationSize (input old outside) = ProgrammeSource.registrationSize old := by
  cases h : old.emission? <;> simp [input,ProgrammeSource.registrationSize,h]

theorem observed (old : ProgrammeSource.Input OldParty Good OldPort OldState Unit) (outside : Good → ℚ) :
    (input old outside).observedEmission?.isSome = old.observedEmission?.isSome := by
  simp [input]

theorem actual_machine_report (source : Distributed.Reaction.Machine OldParty Good OldPort OldState Unit)
    (outside : Good → ℚ) (here : OldCurrent) :
    ((input source.input outside).observedEmission?.get (by rfl)).generate (current here outside) =
      .original (current here outside) ((source.body here).map request) := by
  change ProgrammeSource.ProgrammeReport.original
    (current (reportedCurrent (source.report (project (current here outside)))) outside)
    ((source.report (project (current here outside))).word.map request) = _
  rw [project_current]
  rfl

def visit (outside : Good → ℚ) : ProgrammeSource.Current OldCurrent → ProgrammeSource.Current WholeCursorLaw.Current
  | .bootstrap => .bootstrap
  | .running here past => .running (current here outside) (past.map fun before => current before outside)

theorem rawCurrent (old : ProgrammeSource.Input OldParty Good OldPort OldState Unit) (outside : Good → ℚ)
    (here : ProgrammeSource.Current OldCurrent) :
    ProgrammeSource.rawCurrent (input old outside) (visit outside here) =
      current (ProgrammeSource.rawCurrent old here) outside := by cases here <;> rfl

theorem rawEvent (old : ProgrammeSource.Input OldParty Good OldPort OldState Unit) (outside : Good → ℚ)
    (here : ProgrammeSource.Current OldCurrent) :
    ProgrammeSource.rawEvent (input old outside) (visit outside here) =
      (ProgrammeSource.rawEvent old here).map request := by
  cases here with
  | bootstrap => rfl
  | running here past => exact word old outside here

theorem next (old : ProgrammeSource.Input OldParty Good OldPort OldState Unit) (same : old.law = oldLaw)
    (outside : Good → ℚ) (here : ProgrammeSource.Current OldCurrent) :
    ProgrammeSource.next (input old outside) (visit outside here) =
      visit outside (ProgrammeSource.next old here) := by
  cases here with
  | bootstrap =>
      change ProgrammeSource.Current.running (newLaw.next (current old.initial outside) ([].map request)) _ = _
      rw [WholePartyExecution.next]
      simp only [ProgrammeSource.next,visit,same,List.map_cons,List.map_nil]
      rfl
  | running here past =>
      change ProgrammeSource.Current.running (newLaw.next (current here outside)
        (ProgrammeSource.wordAt (input old outside) (current here outside))) _ = _
      rw [word,WholePartyExecution.next]
      simp only [ProgrammeSource.next,visit,same,List.map_append,List.map_singleton]

theorem every_original_root_visit_is_replayed (old : ProgrammeSource.Input OldParty Good OldPort OldState Unit)
    (same : old.law = oldLaw) (outside : Good → ℚ) (ordinal : Nat) :
    (ProgrammeHistory.visitAt (input old outside) ordinal).current =
      visit outside (ProgrammeHistory.visitAt old ordinal).current := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
      change ProgrammeSource.next (input old outside) _ = visit outside (ProgrammeSource.next old _)
      rw [ih,next old same]

theorem every_original_root_word_and_full_trace_are_replayed
    (old : ProgrammeSource.Input OldParty Good OldPort OldState Unit) (same : old.law = oldLaw)
    (outside : Good → ℚ) (ordinal : Nat) :
    let oldVisit := (ProgrammeHistory.visitAt old ordinal).current
    let newVisit := (ProgrammeHistory.visitAt (input old outside) ordinal).current
    ProgrammeSource.rawEvent (input old outside) newVisit = (ProgrammeSource.rawEvent old oldVisit).map request ∧
      newLaw.rawItems (ProgrammeSource.rawCurrent (input old outside) newVisit)
          (ProgrammeSource.rawEvent (input old outside) newVisit) =
        (oldLaw.rawItems (ProgrammeSource.rawCurrent old oldVisit) (ProgrammeSource.rawEvent old oldVisit)).map
          (WholePartyExecution.item outside) := by
  dsimp only
  rw [every_original_root_visit_is_replayed old same,rawEvent,rawCurrent]
  exact ⟨rfl,congrArg ExecutionResult.items (WholePartyExecution.execute _ outside 0 _)⟩

abbrev native (old : ProgrammeSource.Input OldParty Good OldPort OldState Unit) (outside : Good → ℚ) (ordinal : Nat) :=
  ProgrammeHistory.execution_face_shares_whole_ledger_and_next (input old outside) ordinal
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholePartySource
