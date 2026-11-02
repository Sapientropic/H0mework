import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly.Disposition
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly.Control
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly.Disposition.Consumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial.Preference.Lookahead.Actual

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  {origin : Functions.Revision.Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount}
  {admission : Functions.Revision.InitialAdmissionAt origin}
  (frame : Macro.Public.Runtime.Frame origin admission)

private theorem restrict_period
    (source : ProgrammeSource.Input Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument) (members scope : List Party)
    (word : RawEvent Party Good Port Technology Instrument)
    (checked : Material.PeriodChecks source before scope word)
    (contained : ∀ person ∈ members, person ∈ scope) :
    Material.PeriodChecks source before members word :=
  ⟨checked.1, fun person present => checked.2.1 person (contained person present),
    checked.2.2.1, fun person present => checked.2.2.2.1 person (contained person present), checked.2.2.2.2⟩

private theorem replay_keeps_the_original_period
    (before : RawCurrent Party Good Technology Instrument) (members : List Party)
    (word : RawEvent Party Good Port Technology Instrument)
    (checked : Material.PeriodChecks input before members word) :
    Material.PeriodChecks (Macro.Public.Scope.checkInput input) before members
      (Functions.Replay.wordAt input.law before word) := by
  refine ⟨?_, ?_, open_guard _ _, ?_, ?_⟩
  · intro item present
    change item ∈ ((PublicFunction.physicalLaw input.law).execute before 0
      (Functions.Replay.wordAt input.law before word)).items at present
    rw [(Functions.Replay.replay_execution_has_the_same_actual_currents input.law before 0 word).2] at present
    obtain ⟨original, listed, rfl⟩ := List.mem_map.mp present
    have originalChecked := checked.1 original listed
    have raw : Functions.Replay.requestAt input.law original.before original.request =
        original.request.resign original.request.signer := if_pos originalChecked.1
    change (PublicFunction.physicalLaw input.law).Valid original.before
        (Functions.Replay.requestAt input.law original.before original.request) ∧
      (PublicFunction.physicalLaw input.law).Valid original.before
        (Material.withoutControllerConsents (Functions.Replay.requestAt input.law original.before original.request)) ∧ _
    rw [raw]
    have lawful := Functions.Replay.an_accepted_original_request_can_be_replayed_without_consents
      input.law original.before original.request originalChecked.1
    refine ⟨lawful, lawful, ?_⟩
    intro debit debited positive
    change debit ∈ (PublicFunction.physicalLaw input.law).debit original.before
      (Functions.Replay.requestAt input.law original.before original.request) at debited
    rw [raw] at debited
    change debit ∈ input.law.debit original.before original.request at debited
    change debit.1.1 = (Functions.Replay.requestAt input.law original.before original.request).signer
    rw [raw]
    exact originalChecked.2.2 debit debited positive
  · exact (Functions.Replay.every_original_livelihood_and_maintenance_requirement_is_preserved
      input.law before word members).mpr checked.2.1
  · intro person present
    change Material.TechniqueDominates (input.law.technique before.technology person)
      (input.law.technique ((PublicFunction.physicalLaw input.law).next before
        (Functions.Replay.wordAt input.law before word)).technology person)
    rw [Functions.Replay.replay_preserves_the_original_full_next]
    exact checked.2.2.2.1 person present
  · change True
    trivial

private theorem accepted_body
    (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
    (start : Physical.Cursor Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (selected : Physical.Public.wordAt (Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast start.past)
      start.incoming = some word)
    (lawful : ∀ item ∈ (Physical.Public.interpreter input).rawItems
      (Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast start.past).raw word,
      (Physical.Public.interpreter input).Valid item.before item.request)
    (generated : Physical.Public.resultAt input depth count prefixLimit renewalLimit oldPast start = .accepted word selected lawful) :
    Physical.Public.body input depth count prefixLimit renewalLimit oldPast start =
      ((Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast start.past).raw, word) := by
  simp only [Physical.Public.body, Physical.Public.execution, generated, Physical.Public.ResultAt.execution]
  rw [RawLaw.inventory_requests_exact]

/-- The initial material obligation is paid by the selected original body,
including the legacy source branch; it is never a caller success premise. -/
theorem every_actual_admission_keeps_the_complete_original_migration : MigrationChecks origin admission := by
  cases admission with
  | legacy ready =>
      let before := Physical.stateAt input depth count prefixLimit renewalLimit origin.germ.snapshot.past
      have legal := fun item present => (ready.scope.checked.2.2.1 item present).1
      obtain ⟨selected, lawful, produced⟩ :=
        Functions.Revision.Scope.the_source_renewal_is_actually_accepted_without_old_consents input
          before ready.scope.word ready.scope.phase legal
      have body := accepted_body origin.germ.snapshot.past
        (Functions.Revision.InitialAdmission.start (.legacy ready)) _ selected lawful produced
      unfold MigrationChecks Capital.firstBody
      rw [body]
      rw [← Functions.Revision.Scope.the_checked_source_word_is_its_direct_public_resign
        input.law before.raw ready.scope.word legal]
      apply replay_keeps_the_original_period
      apply restrict_period input before.raw (Capital.originalMembers origin) _ ready.scope.word ready.scope.checked.2.2
      intro person present
      exact List.mem_dedup.mpr (List.mem_append_left _ present)
  | publicPlan plan source =>
      have accepted := Functions.Revision.PublicPlan.the_actual_public_first_period_is_accepted plan
      change (Physical.Public.resultAt input depth count prefixLimit renewalLimit origin.germ.snapshot.past
        (Functions.Revision.InitialAdmission.start (.publicPlan plan source))).isAccepted = true at accepted
      cases produced : Physical.Public.resultAt input depth count prefixLimit renewalLimit origin.germ.snapshot.past
          (Functions.Revision.InitialAdmission.start (.publicPlan plan source)) with
      | accepted word selected lawful =>
          have same : word = Functions.Revision.PublicPlan.executable plan.rawWord := Option.some.inj selected.symm
          cases same
          unfold MigrationChecks Capital.firstBody
          rw [accepted_body _ _ _ selected lawful produced]
          apply restrict_period (Macro.Public.Scope.checkInput input) _ (Capital.originalMembers origin) _ _ plan.checked.2.2
          intro person present
          apply Functions.Revision.PublicPlan.every_actual_member_is_checked input depth count prefixLimit renewalLimit
            (Functions.Revision.InitialAdmission.sourceSnapshot origin) plan.rawWord person
          unfold Epoch.Interface.Actors.Census.parties
          rw [Physical.Prefix.past_readback]
          exact present
      | refused word selected item listed failed => rw [produced] at accepted; cases accepted
      | metadata absent => cases absent

abbrev CompleteInitialReplacementAvailable
    (source : Functions.Revision.Context (input := input) (review := review)
      depth count prefixLimit renewalLimit sourceDepth sourceCount) : Prop :=
  ∃ word ∈ Functions.Revision.PublicPlan.candidates input depth count prefixLimit renewalLimit
      (Functions.Revision.InitialAdmission.sourceSnapshot source),
    Dividend.Financial.Preference.Checks input depth count prefixLimit renewalLimit
        (Functions.Revision.InitialAdmission.sourceSnapshot source) word ∧
      Dividend.Financial.Preference.PostFeasible input depth count prefixLimit renewalLimit
        (Functions.Revision.InitialAdmission.sourceSnapshot source) word

section InitialSelection

variable {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  (package : Macro.Inquiry.Package (review := review) input depth count prefixLimit renewalLimit
    sourceDepth sourceCount start proposal sourcePosition)
  (visit : SourceNativeTemporalVisitAt package.frame.root.toAuthoritativeRoot.toLedgerRoot)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt package.frame.root visit
    (package.frame.entry visit.current))
  (germ : Macro.Raw.GermAt package.source package.sourceData package.reader visit.current)

local notation "source₀" => Functions.Revision.Enactment.Inquiry.contextAt package visit authority germ

theorem an_available_complete_initial_replacement_is_selected_with_its_actual_witness
    (available : CompleteInitialReplacementAvailable source₀) :
    ∃ plan, ∃ source : Functions.Revision.InitialAdmission.inspectPublic source₀ = .accepted plan,
      Functions.Revision.InitialAdmission.select source₀ = .admitted (.publicPlan plan source) ∧
      ∃ witness, abolitionDisposition
          (Macro.Public.Runtime.Frame.initial package visit authority germ (.publicPlan plan source)) = .abolished witness := by
  obtain ⟨plan, source, chosen, future⟩ :=
    Dividend.Financial.Preference.Lookahead.Runtime.initial_source_selection_has_a_future_at_its_actual_first_snapshot
      package visit authority germ available
  obtain ⟨selection, preferred, _future⟩ := Dividend.Financial.Preference.an_available_complete_replacement_is_selected
    input depth count prefixLimit renewalLimit (Functions.Revision.InitialAdmission.sourceSnapshot source₀) available
  obtain ⟨expected, produced, _word, strict⟩ :=
    Functions.Revision.PublicPlan.an_available_full_account_improvement_is_the_actual_public_plan
      input depth count prefixLimit renewalLimit (Functions.Revision.InitialAdmission.sourceSnapshot source₀) selection preferred
  have same : plan = expected := Functions.Revision.PublicPlan.Outcome.accepted.inj (source.symm.trans produced)
  cases same
  let actual := Macro.Public.Runtime.Frame.initial package visit authority germ (.publicPlan plan source)
  have financial : Dividend.Financial.Checks input depth count prefixLimit renewalLimit
      (source₀).germ.snapshot.past actual.snapshot := by
    rw [Macro.Public.Runtime.Frame.snapshot_is_the_literal_after]
    exact strict
  obtain ⟨word, generated, checked⟩ := future
  exact ⟨plan, source, chosen,
    the_actual_three_checks_cannot_be_hidden_in_a_residual actual financial
      (every_actual_admission_keeps_the_complete_original_migration (origin := source₀)
        (admission := .publicPlan plan source)) word generated checked⟩

end InitialSelection

def CompletePublicDisposition : Prop :=
  match abolitionDisposition frame with
  | .abolished witness =>
      type_of% witness.the_installed_read_is_the_literal_root_snapshot ∧
      type_of% witness.the_actual_migration_keeps_independence_life_capacity_and_no_new_control ∧
      type_of% witness.the_current_future_is_actually_executable_and_pays_every_member ∧
      type_of% witness.the_full_account_has_no_loser_and_has_strict_gain ∧
      ¬ FreshControlAt (Macro.Runtime.ActivatedFrame.enacted origin admission frame)
  | .residual failure =>
      type_of% failure.refutes_its_exact_original_check ∧ ¬ Nonempty (AbolitionWitness frame)

theorem the_same_actual_public_source_generates_a_complete_witness_or_its_exact_residual :
    CompletePublicDisposition frame := by
  unfold CompletePublicDisposition
  cases generated : abolitionDisposition frame with
  | abolished witness =>
      exact ⟨witness.the_installed_read_is_the_literal_root_snapshot,
        witness.the_actual_migration_keeps_independence_life_capacity_and_no_new_control,
        witness.the_current_future_is_actually_executable_and_pays_every_member,
        witness.the_full_account_has_no_loser_and_has_strict_gain,
        an_actual_public_body_has_no_fresh_title_surplus_or_historical_control _ rfl⟩
  | residual failure =>
      exact ⟨failure.refutes_its_exact_original_check, failure.excludes_a_success_witness⟩

local notation "F" => Macro.Runtime.ActivatedFrame (review := review)
  input depth count prefixLimit renewalLimit sourceDepth sourceCount

def CompleteInitialSourceChoice (state : F) : Prop := match state with
  | .original current => ∀ raw : Macro.Runtime.ActivatedFrame.OriginalBoundary current,
      CompleteInitialReplacementAvailable (current.controlOrigin raw.germ) →
      ∃ plan, ∃ source : Functions.Revision.InitialAdmission.inspectPublic (current.controlOrigin raw.germ) = .accepted plan,
        Functions.Revision.InitialAdmission.select (current.controlOrigin raw.germ) = .admitted (.publicPlan plan source) ∧
        state.next = .enacted (current.controlOrigin raw.germ) (.publicPlan plan source)
          (Macro.Public.Runtime.Frame.initial current.package (.finite current.visit) current.authority raw.germ
            (.publicPlan plan source)) ∧
        ∃ witness, abolitionDisposition
          (Macro.Public.Runtime.Frame.initial current.package (.finite current.visit) current.authority raw.germ
            (.publicPlan plan source)) = .abolished witness
  | .enacted .. => True

theorem every_original_boundary_selects_an_available_complete_replacement (state : F) :
    CompleteInitialSourceChoice state := by
  cases state with
  | enacted origin admission current => trivial
  | original current =>
      intro raw available
      obtain ⟨plan, source, chosen, witness⟩ :=
        an_available_complete_initial_replacement_is_selected_with_its_actual_witness
          current.package (.finite current.visit) current.authority raw.germ available
      refine ⟨plan, source, chosen, ?_, witness⟩
      dsimp only [Macro.Runtime.ActivatedFrame.next]
      rw [raw.selected]
      dsimp only
      rw [chosen]

def CompleteActualDisposition (state : F) : Prop := match state with
  | .original _ => Finite.ActualReviewObstruction state
  | .enacted _ _ current => CompletePublicDisposition current

private theorem a_public_state_has_its_complete_actual_disposition
    (state : F) (opened : state.isPublic = true) : CompleteActualDisposition state := by
  cases state with
  | original current => cases opened
  | enacted origin admission current =>
      exact the_same_actual_public_source_generates_a_complete_witness_or_its_exact_residual current

variable (input depth sourceDepth)
  (datum : Macro.Ingress.Datum input depth sourceDepth) (prefixLimit renewalLimit : Nat)
  (reader : Macro.Raw.Reader input depth (Macro.Ingress.cut input depth sourceDepth))
  (review : Option (ReviewPhase.ContextAt input) := none)

local notation "current" => Macro.Runtime.actualFrame (review := review)
  input depth sourceDepth datum prefixLimit renewalLimit reader

local notation "A" => Macro.Runtime.ActivatedFrame (review := review) input depth
  (Macro.Ingress.cut input depth sourceDepth) prefixLimit renewalLimit depth
  (Macro.Ingress.cut input depth sourceDepth)

theorem every_available_complete_renewal_is_executed_with_its_actual_witness
    {origin : Functions.Revision.Context (input := input) (review := review)
      depth (Macro.Ingress.cut input depth sourceDepth) prefixLimit renewalLimit
      depth (Macro.Ingress.cut input depth sourceDepth)}
    {admission : Functions.Revision.InitialAdmissionAt origin}
    (frame : Macro.Public.Runtime.Frame origin admission) (tick : Nat)
    (selected : current tick = .enacted origin admission frame)
    (complete : ¬ frame.HasWork) (automatic : Macro.Runtime.originalProposal frame = .advance)
    (available : ∃ word ∈ Functions.Revision.Adaptive.candidates input depth (Macro.Ingress.cut input depth sourceDepth)
        prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot,
      Dividend.Financial.Preference.Renewal.Checks input depth (Macro.Ingress.cut input depth sourceDepth)
          prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot word ∧
        Dividend.Financial.Preference.Renewal.PostFeasible input depth (Macro.Ingress.cut input depth sourceDepth)
          prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot word) :
    ∃ plan, Functions.Revision.Adaptive.compile input depth (Macro.Ingress.cut input depth sourceDepth)
        prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot = .accepted plan ∧
      frame.next.snapshot = Dividend.Financial.Preference.Renewal.successor frame.snapshot plan.rawWord ∧
      current (tick + 1) = .enacted origin admission frame.next ∧
      ∃ witness, abolitionDisposition frame.next = .abolished witness := by
  obtain ⟨plan, produced, next, future⟩ :=
    Dividend.Financial.Preference.Lookahead.Runtime.renewal_source_selection_has_a_future_at_its_actual_next_snapshot
      datum reader frame tick selected complete automatic available
  obtain ⟨selection, preferred, _future⟩ := Dividend.Financial.Preference.Renewal.an_available_complete_extension_is_selected
    input depth (Macro.Ingress.cut input depth sourceDepth) prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot available
  obtain ⟨expected, compiled, _word, strict⟩ :=
    Functions.Revision.Adaptive.an_available_full_account_extension_is_the_actual_renewal_plan
      input depth (Macro.Ingress.cut input depth sourceDepth) prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot
      selection preferred
  have same : plan = expected := Functions.Revision.Adaptive.Outcome.accepted.inj (produced.symm.trans compiled)
  cases same
  have financial : Dividend.Financial.Checks input depth (Macro.Ingress.cut input depth sourceDepth)
      prefixLimit renewalLimit origin.germ.snapshot.past frame.next.snapshot := by
    rw [next]
    exact strict
  obtain ⟨word, generated, checked⟩ := future
  refine ⟨plan, produced, next, ?_, ?_⟩
  · change (current tick).next = _
    rw [selected]
    rfl
  · exact the_actual_three_checks_cannot_be_hidden_in_a_residual frame.next financial
      (every_actual_admission_keeps_the_complete_original_migration (origin := origin) (admission := admission))
      word generated checked

theorem every_legal_actual_path_reaches_complete_abolition_or_a_visible_residual (tick : Nat) :
    ∃ steps ≤ (current tick).internalMass + 1,
      CompleteActualDisposition (current (tick + steps)) ∧
      ∀ path : Nat → A, path 0 = current tick → (∀ index, path (index + 1) = (path index).next) →
        path steps = current (tick + steps) := by
  obtain ⟨steps, within, outcome⟩ := Finite.the_actual_source_forces_a_finite_public_tail_or_its_exact_obstruction
    input depth sourceDepth datum prefixLimit renewalLimit reader review tick
  refine ⟨steps, within, ?_, ?_⟩
  · rcases outcome with ⟨opened, _tail⟩ | blocked
    · exact a_public_state_has_its_complete_actual_disposition _ opened
    · cases actual : current (tick + steps) with
      | original original =>
          rw [actual] at blocked
          exact blocked
      | enacted origin admission reached => rw [actual] at blocked; exact blocked.elim
  · intro path starts legal
    exact Finite.every_legal_continuation_is_the_original_actual_fold input depth sourceDepth datum
      prefixLimit renewalLimit reader review tick path starts legal steps

#print axioms the_same_actual_public_source_generates_a_complete_witness_or_its_exact_residual
#print axioms every_legal_actual_path_reaches_complete_abolition_or_a_visible_residual
#print axioms every_actual_admission_keeps_the_complete_original_migration
#print axioms an_available_complete_initial_replacement_is_selected_with_its_actual_witness
#print axioms every_original_boundary_selects_an_available_complete_replacement
#print axioms every_available_complete_renewal_is_executed_with_its_actual_witness

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly
