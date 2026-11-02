import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified.Publication.Execution

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified.Publication.Runtime
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code))
  (original : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
  (reference : Program model.source.code (horizon domain))
  (worker receiver : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

  (allocation : List Allocation) (announcements : List (Rule model.source.code)) (slots : Nat)

variable (point : View (code := model.source.code)) (rival : Opponent model.source.code) (send : Rule model.source.code) (ordinal : Nat)
variable (vocabulary : PublicFunction.Protocol.SymbolicAuthentication.OwnedAttestation.Vocabulary
    (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  (encoding : PublicFunction.Protocol.SymbolicAuthentication.StageTransport.Encoding (code := model.source.code))
  (law : PublicFunction.Protocol.SymbolicAuthentication.StageReception.Law model.source.code)
  (initial : List (View (code := model.source.code))) (rounds : Nat)

abbrev full := Execution.full model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds
abbrev source := (full model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).source
abbrev bound := Replanning.native model (full model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds)
abbrev Snapshot := Receipt.Outcome model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law × Option (Execution.Learning model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds)
abbrev snapshot : Snapshot model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds := (Execution.received model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law,Execution.learning model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds)

def available (visit : Nat) :=
  if arrival (full model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds) ≤ visit then
    some (snapshot model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds)
  else none

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (source model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (visit : Nat) →
    current = (ProgrammeHistory.visitAt (source model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).input visit).current →
      Option (Snapshot model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds)
  project := fun _ {_} _ _ visit _ =>
    available model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds visit

def root := (Native.AuthorityRuntime.root (bound model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds)).withProjectionCoface
  (projectionLaw model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds)

theorem original_programme_root_is_preserved :
    (root model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (source model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).input).toAuthoritativeRoot.toRoot := rfl

def stateAt (visit : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (source model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).input) :=
  ⟨ProgrammeSource.V (source model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).input,root model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds,
    ProgrammeHistory.temporalVisit (source model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).input visit⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (source model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).input) where
  State := Nat
  stateAt := stateAt model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (source model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).input) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    exact ProgrammeHistory.visit_current_injective _ (eq_of_heq (Sigma.mk.inj labels).2)
  initial := 0
  successorAt := fun visit => ⟨visit+1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : Native.AuthorityRuntime.Face)
  | learning

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (source model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).input) where
  process := process model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Native.AuthorityRuntime.facade (bound model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds)).componentAt
        (Native.AuthorityRuntime.facade (bound model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds)).seed previous
    | .learning => projectionLaw model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
        exact ((Native.AuthorityRuntime.facade (bound model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds)).installationAt
          (Native.AuthorityRuntime.facade (bound model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds)).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (Native.AuthorityRuntime.root (bound model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds)).toAuthoritativeRoot.source
            (projectionLaw model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds))
    | learning =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (Native.AuthorityRuntime.root (bound model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds)).toAuthoritativeRoot.source
          (projectionLaw model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds)
  projectionAt := fun _ face => match face with
    | .previous previous => (Native.AuthorityRuntime.facade (bound model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds)).projectionAt
        (Native.AuthorityRuntime.facade (bound model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds)).seed previous
    | .learning => ()

abbrev cutPoint (count : Nat) := Execution.cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count
abbrev activated (count : Nat) := (facade model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).seed.advance
  (arrival (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count))

theorem activated_state (count : Nat) :
    (activated model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count).state =
      arrival (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count) := by
  have state (n : Nat) : ((facade model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).seed.advance n).state = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  exact state _

def read (count : Nat) : Option (Snapshot model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds) :=
  match (facade model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).readoutAt
    (activated model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count) .learning with
  | .inl actual => actual.2 (arrival (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count)) (by
      change (ProgrammeHistory.visitAt (source model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).input
        (activated model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count).state).current = _
      rw [activated_state])
  | .inr impossible => nomatch impossible

theorem the_final_named_read_releases_the_actual_receipt_and_generated_learning :
    read model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds (Deployment.actualHorizon model point) = some (snapshot model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds) := by
  change available model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds (arrival (full model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds)) = _
  exact if_pos (Nat.le_refl _)

theorem no_learning_answer_precedes_the_actual_generated_source (visit : Nat)
    (early : visit < arrival (full model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds)) :
    available model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds visit = none :=
  if_neg (Nat.not_le.mpr early)

theorem each_actual_prefix_extends_to_the_same_fixed_source (count : Nat) :
    full model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds =
      Splice.install (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count) rival
        ((Execution.future model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).drop count) := by
  change Splice.install _ rival ((Execution.future model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).take _) = _
  rw [List.take_of_length_le (Execution.future_fits_the_original_window model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds)]
  change List.foldl _ _ _ = List.foldl _ (List.foldl _ _ _) _
  rw [←List.foldl_append,List.take_append_drop]

theorem each_actual_cut_is_the_same_visit_in_the_fixed_source (count : Nat) :
    (ProgrammeHistory.visitAt (source model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).input
      (arrival (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count))).current =
    (ProgrammeHistory.visitAt (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count).source.input
      (arrival (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count))).current := by
  change (ProgrammeHistory.visitAt (full model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).source.input _).current = _
  rw [each_actual_prefix_extends_to_the_same_fixed_source model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count]
  exact Machine.actual_prefix_from_events (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count).source.input
    (Splice.install (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count) rival
      ((Execution.future model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).drop count)).source.input rfl rfl
    (arrival (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count))
    (Installation.Chain.fold_keeps_every_prior_raw_event (model := model) _ rival _) _ (Nat.le_refl _)

theorem each_actual_prefix_preserves_its_entire_native_financial_account (count visit : Nat)
    (earlier : visit ≤ arrival (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count)) :
    Native.Coupling.Match model.source.code (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count).source.input
      (source model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).input
      (Financial.accountAt (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count).source.input visit)
      (Financial.accountAt (source model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).input visit) := by
  change Native.Coupling.Match _ _ (full model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).source.input _
    (Financial.accountAt (full model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).source.input visit)
  rw [each_actual_prefix_extends_to_the_same_fixed_source model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count]
  exact Installation.Chain.fold_keeps_the_complete_native_financial_prefix (model := model) _ rival _ visit earlier

theorem each_live_stage_is_the_next_actual_cut (count : Nat)
    (inside : count < (Execution.future model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).length) :
    arrival (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds (count+1)) =
      arrival (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count)+1 := by
  change arrival (Splice.install _ rival ((Execution.future model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).take (count+1))) = _
  rw [List.take_succ_eq_append_getElem inside]
  unfold Splice.install
  rw [List.foldl_append]
  rfl

theorem the_same_root_consumes_each_actual_cut_full_account_and_literal_next (count : Nat) :
    let current := activated model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count
    (ProgrammeHistory.visitAt (source model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).input
      (arrival (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count))).current =
      (ProgrammeHistory.visitAt (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count).source.input
        (arrival (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count))).current ∧
    Native.Coupling.Match model.source.code (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count).source.input
      (source model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).input
      (Financial.accountAt (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count).source.input
        (arrival (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count)))
      (Financial.accountAt (source model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).input
        (arrival (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count))) ∧
    HEq ((facade model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).readoutAt current .learning)
      (current.tick.generated.projectionOutcome (.component ())) ∧
    HEq current.tick.generated.wholeLedgerWriteBack
      (current.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current.current.visit.current) ∧
    ((count < (Execution.future model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).length) →
      current.tick.nextCurrent = (activated model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds (count+1)).current) := by
  have rooted := (facade model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).readoutAt_factorizes
    (activated model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count) .learning
  refine ⟨each_actual_cut_is_the_same_visit_in_the_fixed_source model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count,
    each_actual_prefix_preserves_its_entire_native_financial_account model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count _ (Nat.le_refl _),
    rooted.2.2.2.1,rooted.2.2.1,?_⟩
  intro inside
  apply rooted.2.2.2.2.trans
  change (facade model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).process.stateAt
    (Nat.succ ((facade model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).seed.advance
      (arrival (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count))).state) = _
  have state (n : Nat) : ((facade model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).seed.advance n).state = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  change (facade model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).process.stateAt
    (Nat.succ ((facade model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).seed.advance
      (arrival (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count))).state) =
    (facade model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).process.stateAt
      (((facade model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).seed.advance
        (arrival (cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds (count+1)))).state)
  rw [state,state,each_live_stage_is_the_next_actual_cut model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds count inside]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified.Publication.Runtime
