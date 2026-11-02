import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.Source
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.GrantTransport

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.NativeTransport

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Authority.Trace

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port)}

private def transportCandidateGrant
    {first second : RawCurrent Party Good (Mandate.State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord)
    (grant : Mandate.Grant base scope first firstWord) : Mandate.Grant base scope second secondWord := by
  cases sameCurrent; cases sameWord; exact grant

private theorem transport_candidate_event
    {first second : RawCurrent Party Good (Mandate.State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord)
    (grant : Mandate.Grant base scope first firstWord) :
    (transportCandidateGrant sameCurrent sameWord grant).electionEvent = grant.electionEvent := by
  cases sameCurrent; cases sameWord; rfl

private theorem transport_candidate_items
    {first second : RawCurrent Party Good (Mandate.State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord)
    (grant : Mandate.Grant base scope first firstWord) :
    (transportCandidateGrant sameCurrent sameWord grant).proposal.item.val = grant.proposal.item.val ∧
      (transportCandidateGrant sameCurrent sameWord grant).acceptance.item.val = grant.acceptance.item.val := by
  cases sameCurrent; cases sameWord; exact ⟨rfl, rfl⟩

private theorem transport_candidate_initial
    {oldCurrent newCurrent : Nat → RawCurrent Party Good (Mandate.State Party Technology) Instrument}
    {oldWord newWord : Nat → RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    (birth : Nat) (sameCurrent : newCurrent birth = oldCurrent birth) (sameWord : newWord birth = oldWord birth)
    (grant : Mandate.Grant base scope (oldCurrent birth) (oldWord birth)) :
    Mandate.Lifecycle.Observed.initialState base scope newCurrent newWord birth
        (transportCandidateGrant sameCurrent sameWord grant) =
      Mandate.Lifecycle.Observed.initialState base scope oldCurrent oldWord birth grant := by
  change (Election.mandateAdmissionEdge Mandate.Grant.lineageCompiler
    (transportCandidateGrant sameCurrent sameWord grant).electionEvent).target = _
  rw [transport_candidate_event]
  rfl

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (input : Input model.source.code) (cut : Nat) (raw : List (Option model.source.code.Policy))
  (horizon : Nat) (party : Party) (good : Good)
  (floor : Gross.Floor model.source.code.law party good model.source.code.actions) (budget : ℚ)
  (rival : Opponent model.source.code)
  (paid : Source.Paid model.source input cut raw horizon party good budget rival)
  (active : model.source.feedback? = some input) (empty : model.source.continuation = [])

abbrev original : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) :=
  {model with source := Future.target model.source input cut rival raw}
abbrev normalized : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) :=
  {model with source := Source.target model.source input cut raw horizon party good floor budget rival}
abbrev finish := model.source.history.length+2+cut+horizon
abbrev last := finish model cut horizon - 2

include paid active empty in
theorem events (ordinal : Nat) (inside : ordinal < finish model cut horizon) :
    ProgrammeSource.rawEvent (normalized model input cut raw horizon party good floor budget rival).source.input
      (ProgrammeHistory.visitAt (original model input cut raw rival).source.input ordinal).current =
    ProgrammeSource.rawEvent (original model input cut raw rival).source.input
      (ProgrammeHistory.visitAt (original model input cut raw rival).source.input ordinal).current :=
  Source.every_original_source_event_is_transported model.source input cut raw horizon party good floor budget rival paid active empty ordinal inside

include paid active empty in
theorem current (visit : Nat) (inside : visit ≤ last model cut horizon) :
    Native.Authority.currentAt (normalized model input cut raw horizon party good floor budget rival) visit =
      Native.Authority.currentAt (original model input cut raw rival) visit :=
  Native.Coupling.History.raw_current (original model input cut raw rival).source.input
    (normalized model input cut raw horizon party good floor budget rival).source.input rfl rfl (finish model cut horizon)
    (events model input cut raw horizon party good floor budget rival paid active empty) (visit+1)
    (by dsimp only [last,finish] at *;omega)

include paid active empty in
theorem word (visit : Nat) (inside : visit ≤ last model cut horizon) :
    Native.Authority.wordAt (normalized model input cut raw horizon party good floor budget rival) visit =
      Native.Authority.wordAt (original model input cut raw rival) visit :=
  (Native.Coupling.History.occurrences (original model input cut raw rival).source.input
    (normalized model input cut raw horizon party good floor budget rival).source.input rfl rfl (finish model cut horizon)
    (events model input cut raw horizon party good floor budget rival paid active empty) (visit+1)
    (by dsimp only [last,finish] at *;omega)).2

include paid active empty in
theorem grant_image (birth : Nat) (inside : birth ≤ last model cut horizon)
    (grant : Mandate.Grant model.base model.scope
      (Native.Authority.currentAt (original model input cut raw rival) birth)
      (Native.Authority.wordAt (original model input cut raw rival) birth)) :
    grantImage (normalized model input cut raw horizon party good floor budget rival) birth
        (last model cut horizon) (Native.Authority.traceGrant _ _ _
          (transportCandidateGrant (current model input cut raw horizon party good floor budget rival paid active empty birth inside)
            (word model input cut raw horizon party good floor budget rival paid active empty birth inside) grant)) =
      grantImage (original model input cut raw rival) birth (last model cut horizon)
        (Native.Authority.traceGrant _ _ _ grant) := by
  have items := transport_candidate_items
    (current model input cut raw horizon party good floor budget rival paid active empty birth inside)
    (word model input cut raw horizon party good floor budget rival paid active empty birth inside) grant
  have initial := transport_candidate_initial birth
    (current model input cut raw horizon party good floor budget rival paid active empty birth inside)
    (word model input cut raw horizon party good floor budget rival paid active empty birth inside) grant
  have index := congrArg ExecutionItem.index items.2
  have state := Mandate.Lifecycle.Observed.through_state_congr (last model cut horizon) index initial
    (current model input cut raw horizon party good floor budget rival paid active empty) (word model input cut raw horizon party good floor budget rival paid active empty)
  have final := Mandate.Lifecycle.Observed.History.obligation_eq_of_state_eq _ _ state
  have history := grant_through_images_congr model.source.code (last model cut horizon) index initial
    (current model input cut raw horizon party good floor budget rival paid active empty) (word model input cut raw horizon party good floor budget rival paid active empty)
  have election := transport_candidate_event
    (current model input cut raw horizon party good floor budget rival paid active empty birth inside)
    (word model input cut raw horizon party good floor budget rival paid active empty birth inside) grant
  have original := congrArg (Election.mandateObligation (Mandate.Grant.lineageCompiler (Party := Party) (Port := Port))) election
  apply (GrantImage.mk.injEq ..).mpr
  exact ⟨rfl, congrArg (itemImage model.source.code) items.1, congrArg (itemImage model.source.code) items.2,
    congrArg grantObligationImage original, congrArg grantObligationImage final, history⟩

private theorem grantsAt_transport
    {first second : RawCurrent Party Good (Mandate.State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord) :
    Mandate.grantsAt base scope second secondWord =
      (Mandate.grantsAt base scope first firstWord).map (transportCandidateGrant sameCurrent sameWord) := by
  cases sameCurrent; cases sameWord
  exact (List.map_id _).symm

include paid active empty in
theorem complete_grant_census :
    (Native.Authority.recordsAt (normalized model input cut raw horizon party good floor budget rival) (last model cut horizon)).map
      (fun record => grantImage (normalized model input cut raw horizon party good floor budget rival) record.1.val _ record.2) =
    (Native.Authority.recordsAt (original model input cut raw rival) (last model cut horizon)).map
      (fun record => grantImage (original model input cut raw rival) record.1.val _ record.2) := by
  simp only [Native.Authority.recordsAt,List.map_flatMap,List.map_map,Function.comp_def]
  apply congrArg (List.flatMap · (List.finRange (last model cut horizon+1)))
  funext birth
  have inside : birth.val ≤ last model cut horizon := Nat.le_of_lt_succ birth.isLt
  rw [grantsAt_transport (current model input cut raw horizon party good floor budget rival paid active empty birth.val inside)
    (word model input cut raw horizon party good floor budget rival paid active empty birth.val inside)]
  simp only [List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro grant _
  exact grant_image model input cut raw horizon party good floor budget rival paid active empty birth.val inside grant

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.NativeTransport
