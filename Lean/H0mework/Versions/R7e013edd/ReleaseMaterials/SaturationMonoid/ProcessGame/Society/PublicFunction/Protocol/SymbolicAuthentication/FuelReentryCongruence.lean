import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelReentrySource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelReentryCongruence
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open FuelControlSource (code)
open FuelReentrySource

variable (left right : Cursor code) (same : EventStep.Matches left right)
abbrev supplied (cursor : Cursor code) := MaterialRoundSource.supplied (bound cursor) cursor.cut (incoming cursor)
abbrev afterInput (cursor : Cursor code) := MaterialRoundSource.afterInput (bound cursor) cursor.cut (incoming cursor)
abbrev recovery (cursor : Cursor code) := MaterialRoundSource.recovery (bound cursor) cursor.cut (incoming cursor)
abbrev prepared (cursor : Cursor code) := MaterialRoundSource.prepared (bound cursor) cursor.cut (incoming cursor)
abbrev archiveCode (cursor : Cursor code) := RoundArchive.code (supplied cursor).source (cursor.cut+1)
  (recovery cursor) MaterialRoundSource.payment MaterialRoundSource.fee
abbrev archiveHistory (cursor : Cursor code) := RoundArchive.history (supplied cursor).source (cursor.cut+1) (recovery cursor)

include same

theorem actual_preparation_currents_and_words_are_preserved :
    afterInput left = afterInput right ∧ recovery left = recovery right ∧ prepared left = prepared right := by
  have inputs := matched_actual_cursors_have_the_same_material_input left right same
  have one := MaterialRoundSource.the_incoming_and_recovery_are_literal_successive_actual_occurrences
    (bound left) left.cut (incoming left)
  have two := MaterialRoundSource.the_incoming_and_recovery_are_literal_successive_actual_occurrences
    (bound right) right.cut (incoming right)
  have afters : afterInput left = afterInput right := by
    change MaterialRoundSource.afterInput (bound left) left.cut (incoming left) = MaterialRoundSource.afterInput (bound right) right.cut (incoming right)
    rw [one.2.2.1,two.2.2.1]
    change code.law.next (before left) (incoming left) = code.law.next (before right) (incoming right)
    rw [inputs.1,inputs.2]
  have words : recovery left = recovery right := by
    unfold recovery MaterialRoundSource.recovery
    change (if RenewedQuorumMaterial.Inputs (afterInput left) then _ else _) = _
    rw [afters]
  refine ⟨afters,words,?_⟩
  change MaterialRoundSource.prepared (bound left) left.cut (incoming left) = MaterialRoundSource.prepared (bound right) right.cut (incoming right)
  rw [one.2.2.2.2.2,two.2.2.2.2.2]
  change code.law.next (afterInput left) (recovery left) = code.law.next (afterInput right) (recovery right)
  rw [afters,words]

theorem the_supplied_snapshot_is_the_same_entire_actual_past :
    RoundArchive.snapshot (supplied left).source (left.cut+1) =
      RoundArchive.snapshot (supplied right).source (right.cut+1) := by
  change RoundArchive.snapshot (Machine.Continuation.extend left.source left.cut (incoming left)) (left.cut+1) = _
  rw [a_continuation_snapshot_is_the_actual_old_snapshot_and_its_new_word,
    a_continuation_snapshot_is_the_actual_old_snapshot_and_its_new_word,
    matched_actual_cursors_have_the_same_complete_raw_snapshot left right same,
    (matched_actual_cursors_have_the_same_material_input left right same).2]

theorem the_original_archive_suffix_is_preserved :
    RoundArchive.suffix (supplied left).source (left.cut+1) (recovery left) =
      RoundArchive.suffix (supplied right).source (right.cut+1) (recovery right) := by
  unfold RoundArchive.suffix
  rw [the_supplied_snapshot_is_the_same_entire_actual_past left right same,
    (actual_preparation_currents_and_words_are_preserved left right same).2.1]
  rfl

theorem archive_code_and_entire_history_are_preserved :
    archiveCode left = archiveCode right ∧ archiveHistory left = archiveHistory right := by
  have suffix := the_original_archive_suffix_is_preserved left right same
  constructor
  · unfold archiveCode RoundArchive.code
    rw [suffix]
    rfl
  · unfold archiveHistory RoundArchive.history
    rw [suffix]
    rfl

theorem the_original_admission_checks_are_preserved :
    RoundArchive.admissible (supplied left).source (left.cut+1) (recovery left)
      MaterialRoundSource.payment MaterialRoundSource.fee =
      RoundArchive.admissible (supplied right).source (right.cut+1) (recovery right)
        MaterialRoundSource.payment MaterialRoundSource.fee ∧
      MaterialRoundSource.phasesAdmitted (bound left) left.cut (incoming left) =
        MaterialRoundSource.phasesAdmitted (bound right) right.cut (incoming right) := by
  constructor
  · unfold RoundArchive.admissible
    change (archiveCode left).historyLegal ((archiveCode left).historyCurrent (archiveCode left).publicPrefix) _ =
      (archiveCode right).historyLegal ((archiveCode right).historyCurrent (archiveCode right).publicPrefix) _
    rw [(archive_code_and_entire_history_are_preserved left right same).1,
      the_original_archive_suffix_is_preserved left right same]
  · unfold MaterialRoundSource.phasesAdmitted
    exact congrArg (fun current => decide (code.law.Valid current MaterialRoundSource.payment ∧
      code.law.Valid (code.law.step current MaterialRoundSource.payment) MaterialRoundSource.fee ∧
      code.law.Valid (code.law.step (code.law.step current MaterialRoundSource.payment) MaterialRoundSource.fee) MaterialRoundSource.fee))
      (actual_preparation_currents_and_words_are_preserved left right same).2.2

theorem material_preparation_results_are_preserved :
    MaterialRoundSource.preparation (bound left) left.cut (incoming left) =
      MaterialRoundSource.preparation (bound right) right.cut (incoming right) := by
  have checks := the_original_admission_checks_are_preserved left right same
  by_cases first : RoundArchive.admissible (supplied left).source (left.cut+1) (recovery left) MaterialRoundSource.payment MaterialRoundSource.fee = true
  · have second : RoundArchive.admissible (supplied right).source (right.cut+1) (recovery right) MaterialRoundSource.payment MaterialRoundSource.fee = true := by rwa [← checks.1]
    simp only [MaterialRoundSource.preparation,MaterialRoundSource.archive,RoundArchive.inspect,dif_pos first,dif_pos second]
    rw [checks.2]
  · have second : ¬ RoundArchive.admissible (supplied right).source (right.cut+1) (recovery right) MaterialRoundSource.payment MaterialRoundSource.fee = true := by rwa [← checks.1]
    simp only [MaterialRoundSource.preparation,MaterialRoundSource.archive,RoundArchive.inspect,dif_neg first,dif_neg second]

theorem generated_entry_presence_is_preserved :
    (MaterialRoundSource.inspect (bound left) left.cut (incoming left)).isSome =
      (MaterialRoundSource.inspect (bound right) right.cut (incoming right)).isSome := by
  have checks := the_original_admission_checks_are_preserved left right same
  by_cases first : RoundArchive.admissible (supplied left).source (left.cut+1) (recovery left) MaterialRoundSource.payment MaterialRoundSource.fee = true
  · have second : RoundArchive.admissible (supplied right).source (right.cut+1) (recovery right) MaterialRoundSource.payment MaterialRoundSource.fee = true := by rwa [← checks.1]
    by_cases phase : MaterialRoundSource.phasesAdmitted (bound left) left.cut (incoming left) = true
    · have other : MaterialRoundSource.phasesAdmitted (bound right) right.cut (incoming right) = true := by rwa [← checks.2]
      simp only [MaterialRoundSource.inspect,MaterialRoundSource.archive,RoundArchive.inspect,dif_pos first,dif_pos second,dif_pos phase,dif_pos other,Option.isSome_some]
    · have other : ¬ MaterialRoundSource.phasesAdmitted (bound right) right.cut (incoming right) = true := by rwa [← checks.2]
      simp only [MaterialRoundSource.inspect,MaterialRoundSource.archive,RoundArchive.inspect,dif_pos first,dif_pos second,dif_neg phase,dif_neg other,Option.isSome_none]
  · have second : ¬ RoundArchive.admissible (supplied right).source (right.cut+1) (recovery right) MaterialRoundSource.payment MaterialRoundSource.fee = true := by rwa [← checks.1]
    simp only [MaterialRoundSource.inspect,MaterialRoundSource.archive,RoundArchive.inspect,dif_neg first,dif_neg second,Option.isSome_none]

-- The common carrier is the already-generated complete archive, not a candidate future.
private abbrev suffix (cursor : Cursor code) :=
  RoundArchive.suffix (supplied cursor).source (cursor.cut+1) (recovery cursor)
private abbrev shape (history : List (List RecycledQuorumMaterial.Action)) :=
  {archiveCode FuelControlSource.start with historyAlphabet := history,historyLimit := history.length}
private abbrev Legal (history : List (List RecycledQuorumMaterial.Action)) :=
  (shape history).historyLegal ((shape history).historyCurrent (shape history).publicPrefix) history = true
private abbrev birth (history : List (List RecycledQuorumMaterial.Action)) (legal : Legal history) :
    Machine Delegation.Funded.Party Repayment.Recovery.Good Delegation.Funded.Port
      (Mandate.State Delegation.Funded.Party Bool) Unit where
  code := shape history
  reference := fun _ _ => [MaterialRoundSource.payment]
  reference_generated := by
    apply (shape history).every_local_policy_is_enumerated
    intro key _
    exact (mem_words_iff _ _ _).mpr ⟨by simp,by simp⟩
  history := (shape history).publicPrefix ++ history
  original := by
    apply List.mem_map.mpr
    refine ⟨history,List.mem_filter.mpr ⟨?_,legal⟩,rfl⟩
    exact (mem_sequences_iff _ _ _).mpr ⟨Nat.le_refl _,fun _ member => member⟩
  opponent := fun _ _ _ => none
  side := .original
private def birthProtocol (history : List (List RecycledQuorumMaterial.Action)) (legal : Legal history) : Rule (shape history) :=
  ⟨⟨(birth history legal).reference,(birth history legal).reference_generated⟩,fun key _ =>
    if key.2 = 0 then ⟨some ⟨.activate 0,by simp [shape,archiveCode,RoundArchive.code]⟩,
      by simp [ownMoves,shape,archiveCode,RoundArchive.code];exact Subsingleton.elim _ _⟩
    else if key.2 = 1 then ⟨some ⟨.send 0 0,by simp [shape,archiveCode,RoundArchive.code]⟩,
      by simp [ownMoves,shape,archiveCode,RoundArchive.code];exact Subsingleton.elim _ _⟩
    else ⟨none,List.mem_cons_self⟩⟩
private abbrev birthSlot (history : List (List RecycledQuorumMaterial.Action)) (legal : Legal history) : Scope :=
  ⟨(birth history legal).code.initial.round+(birth history legal).history.length+2,0,0⟩
private abbrev birthVocabulary (history : List (List RecycledQuorumMaterial.Action)) (legal : Legal history) :
    OwnedAttestation.Vocabulary (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good)
      (Port := Delegation.Funded.Port) (Technology := Bool) (Instrument := Unit) :=
  ⟨fun port => if port = .reserve 1 then some (birthSlot history legal,true) else none,fun current => current.round,.service⟩
private def birthEncoding (history : List (List RecycledQuorumMaterial.Action)) (legal : Legal history) :
    AttestationTransport.Encoding (birth history legal) := fun signal =>
  if signal = 1 then some ⟨0,0,0,1,birthSlot history legal,true,1⟩ else none
private abbrev birthInput (history : List (List RecycledQuorumMaterial.Action)) : Input (shape history) := ⟨fun _ _ _ => none,6⟩
private abbrev birthReception (history : List (List RecycledQuorumMaterial.Action)) (legal : Legal history) :
    AttestationReception.ReceptionLaw (birth history legal) := ⟨fun _ _ => birthSlot history legal,1⟩
private def view {Subject : Type} : SubjectQuorum.ResultData Subject → MaterialRoundConsumer.Status
  | .blocked reason => .blocked reason
  | .decided value _ => .decided value

private def birthStatus (history : List (List RecycledQuorumMaterial.Action)) (legal : Legal history) : MaterialRoundConsumer.Status :=
  view (SubjectQuorum.produce (birth history legal) (birthInput history) 0 (birthProtocol history legal)
    (QueueScheduler.environment (birth history legal) (birthInput history) 0)
    (birthVocabulary history legal) (birthEncoding history legal) (birthReception history legal)
    0 6 6 (birthSlot history legal) 1)

omit same in
private theorem birth_status_congr (first second : List (List RecycledQuorumMaterial.Action))
    (equal : first = second) (one : Legal first) (two : Legal second) : birthStatus first one = birthStatus second two := by
  cases equal
  rfl


omit same in
private theorem same_producer_arguments_have_the_same_status
    (a b : Machine Delegation.Funded.Party Repayment.Recovery.Good Delegation.Funded.Port
      (Mandate.State Delegation.Funded.Party Bool) Unit)
    (ia : Input a.code) (ib : Input b.code) (pa : Rule a.code) (pb : Rule b.code)
    (ra : Opponent a.code) (rb : Opponent b.code)
    (va vb : OwnedAttestation.Vocabulary (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good)
      (Port := Delegation.Funded.Port) (Technology := Bool) (Instrument := Unit))
    (ea : AttestationTransport.Encoding a) (eb : AttestationTransport.Encoding b)
    (la : AttestationReception.ReceptionLaw a) (lb : AttestationReception.ReceptionLaw b)
    (receiverA : Fin a.code.sites) (receiverB : Fin b.code.sites) (sa sb : Scope)
    (sources : a = b) (inputs : HEq ia ib) (protocols : HEq pa pb) (rivals : HEq ra rb)
    (vocabularies : va = vb) (encodings : HEq ea eb) (receptions : HEq la lb)
    (receivers : HEq receiverA receiverB) (scopes : sa = sb) :
    view (SubjectQuorum.produce a ia 0 pa ra va ea la receiverA 6 6 sa 1) =
      view (SubjectQuorum.produce b ib 0 pb rb vb eb lb receiverB 6 6 sb 1) := by
  cases sources
  cases eq_of_heq inputs
  cases eq_of_heq protocols
  cases eq_of_heq rivals
  cases vocabularies
  cases eq_of_heq encodings
  cases eq_of_heq receptions
  cases eq_of_heq receivers
  cases scopes
  rfl

omit same in
private theorem actual_birth_status_is_the_status_of_its_entire_generated_archive
    (cursor : Cursor code) (entry : MaterialRoundSource.Ready (bound cursor) cursor.cut (incoming cursor)) :
    view (MaterialRoundSource.outcome (bound cursor) cursor.cut (incoming cursor) entry) =
      birthStatus (suffix cursor) entry.history.admitted := by
  exact same_producer_arguments_have_the_same_status
    (MaterialRoundSource.emitter (bound cursor) cursor.cut (incoming cursor) entry)
    (birth (suffix cursor) entry.history.admitted)
    (MaterialRoundSource.input (bound cursor) cursor.cut (incoming cursor) entry) (birthInput (suffix cursor))
    (MaterialRoundSource.protocol (bound cursor) cursor.cut (incoming cursor) entry) (birthProtocol (suffix cursor) entry.history.admitted)
    (MaterialRoundSource.environment (bound cursor) cursor.cut (incoming cursor) entry)
    (QueueScheduler.environment (birth (suffix cursor) entry.history.admitted) (birthInput (suffix cursor)) 0)
    (MaterialRoundSource.vocabulary (bound cursor) cursor.cut (incoming cursor) entry) (birthVocabulary (suffix cursor) entry.history.admitted)
    (MaterialRoundSource.encoding (bound cursor) cursor.cut (incoming cursor) entry) (birthEncoding (suffix cursor) entry.history.admitted)
    (MaterialRoundSource.reception (bound cursor) cursor.cut (incoming cursor) entry) (birthReception (suffix cursor) entry.history.admitted)
    0 0 (MaterialRoundSource.slot (bound cursor) cursor.cut (incoming cursor) entry) (birthSlot (suffix cursor) entry.history.admitted)
    rfl (by rfl) (by rfl) (by rfl) rfl (by rfl) (by rfl) (by rfl) rfl

theorem source_generated_next_round_status_is_preserved : status left = status right := by
  have presence := generated_entry_presence_is_preserved left right same
  cases first : MaterialRoundSource.inspect (bound left) left.cut (incoming left) with
  | none =>
    cases second : MaterialRoundSource.inspect (bound right) right.cut (incoming right) with
    | some entry => simp only [first,second,Option.isSome_none,Option.isSome_some] at presence;cases presence
    | none =>
      simp only [status,FuelMaterialSource.status,MaterialRoundConsumer.status,MaterialRoundConsumer.produce,first,second,Option.map_none]
      rw [material_preparation_results_are_preserved left right same]
  | some entry =>
    cases second : MaterialRoundSource.inspect (bound right) right.cut (incoming right) with
    | none => simp only [first,second,Option.isSome_none,Option.isSome_some] at presence;cases presence
    | some other =>
      have firstLegal : Legal (suffix left) := entry.history.admitted
      have secondLegal : Legal (suffix right) := other.history.admitted
      have firstRead := actual_birth_status_is_the_status_of_its_entire_generated_archive left entry
      have secondRead := actual_birth_status_is_the_status_of_its_entire_generated_archive right other
      simp only [status,FuelMaterialSource.status,MaterialRoundConsumer.status,MaterialRoundConsumer.produce,first,second,Option.map_some]
      have identical := firstRead.trans ((birth_status_congr _ _ (the_original_archive_suffix_is_preserved left right same) firstLegal secondLegal).trans secondRead.symm)
      generalize MaterialRoundSource.outcome (bound left) left.cut (incoming left) entry = a at identical ⊢
      generalize MaterialRoundSource.outcome (bound right) right.cut (incoming right) other = b at identical ⊢
      cases a <;> cases b <;> exact identical

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelReentryCongruence
