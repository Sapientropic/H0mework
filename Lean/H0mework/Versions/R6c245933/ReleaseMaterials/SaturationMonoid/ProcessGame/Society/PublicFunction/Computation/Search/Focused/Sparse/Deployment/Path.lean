import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse.Deployment

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse.Deployment.Path
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
  (worker : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

  (quotas : List Nat)

variable (point : View (code := model.source.code)) (rival : Opponent model.source.code) (ordinal : Nat)
abbrev full := Deployment.full model domain original reference worker quote quotas point rival ordinal
abbrev source := (full model domain original reference worker quote quotas point rival ordinal).source
abbrev bound := Replanning.native model (full model domain original reference worker quote quotas point rival ordinal)
abbrev snapshot := Sparse.Runtime.read model domain original reference worker quote quotas point rival ordinal

def available (visit : Nat) :=
  if arrival (Deployment.paidFinal model domain original reference worker quote quotas point rival) ≤ visit then
    snapshot model domain original reference worker quote quotas point rival ordinal
  else none

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (source model domain original reference worker quote quotas point rival ordinal).input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (visit : Nat) →
    current = (ProgrammeHistory.visitAt (source model domain original reference worker quote quotas point rival ordinal).input visit).current →
      Option (Sparse.Runtime.Snapshot model domain original reference worker quote quotas point rival)
  project := fun _ {_} _ _ visit _ =>
    available model domain original reference worker quote quotas point rival ordinal visit

def root := (Native.AuthorityRuntime.root (bound model domain original reference worker quote quotas point rival ordinal)).withProjectionCoface
  (projectionLaw model domain original reference worker quote quotas point rival ordinal)

theorem original_programme_root_is_preserved :
    (root model domain original reference worker quote quotas point rival ordinal).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (source model domain original reference worker quote quotas point rival ordinal).input).toAuthoritativeRoot.toRoot := rfl

def stateAt (visit : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (source model domain original reference worker quote quotas point rival ordinal).input) :=
  ⟨ProgrammeSource.V (source model domain original reference worker quote quotas point rival ordinal).input,root model domain original reference worker quote quotas point rival ordinal,
    ProgrammeHistory.temporalVisit (source model domain original reference worker quote quotas point rival ordinal).input visit⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (source model domain original reference worker quote quotas point rival ordinal).input) where
  State := Nat
  stateAt := stateAt model domain original reference worker quote quotas point rival ordinal
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (source model domain original reference worker quote quotas point rival ordinal).input) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    exact ProgrammeHistory.visit_current_injective _ (eq_of_heq (Sigma.mk.inj labels).2)
  initial := 0
  successorAt := fun visit => ⟨visit+1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : Native.AuthorityRuntime.Face)
  | search

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (source model domain original reference worker quote quotas point rival ordinal).input) where
  process := process model domain original reference worker quote quotas point rival ordinal
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Native.AuthorityRuntime.facade (bound model domain original reference worker quote quotas point rival ordinal)).componentAt
        (Native.AuthorityRuntime.facade (bound model domain original reference worker quote quotas point rival ordinal)).seed previous
    | .search => projectionLaw model domain original reference worker quote quotas point rival ordinal
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
        exact ((Native.AuthorityRuntime.facade (bound model domain original reference worker quote quotas point rival ordinal)).installationAt
          (Native.AuthorityRuntime.facade (bound model domain original reference worker quote quotas point rival ordinal)).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (Native.AuthorityRuntime.root (bound model domain original reference worker quote quotas point rival ordinal)).toAuthoritativeRoot.source
            (projectionLaw model domain original reference worker quote quotas point rival ordinal))
    | search =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (Native.AuthorityRuntime.root (bound model domain original reference worker quote quotas point rival ordinal)).toAuthoritativeRoot.source
          (projectionLaw model domain original reference worker quote quotas point rival ordinal)
  projectionAt := fun _ face => match face with
    | .previous previous => (Native.AuthorityRuntime.facade (bound model domain original reference worker quote quotas point rival ordinal)).projectionAt
        (Native.AuthorityRuntime.facade (bound model domain original reference worker quote quotas point rival ordinal)).seed previous
    | .search => ()

abbrev cutPoint (count : Nat) := Deployment.cutPoint model domain original reference worker quote quotas point rival ordinal count
abbrev activated (count : Nat) := (facade model domain original reference worker quote quotas point rival ordinal).seed.advance
  (arrival (cutPoint model domain original reference worker quote quotas point rival ordinal count))

theorem activated_state (count : Nat) :
    (activated model domain original reference worker quote quotas point rival ordinal count).state =
      arrival (cutPoint model domain original reference worker quote quotas point rival ordinal count) := by
  have state (n : Nat) : ((facade model domain original reference worker quote quotas point rival ordinal).seed.advance n).state = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  exact state _

def read (count : Nat) : Option (Sparse.Runtime.Snapshot model domain original reference worker quote quotas point rival) :=
  match (facade model domain original reference worker quote quotas point rival ordinal).readoutAt
    (activated model domain original reference worker quote quotas point rival ordinal count) .search with
  | .inl actual => actual.2 (arrival (cutPoint model domain original reference worker quote quotas point rival ordinal count)) (by
      change (ProgrammeHistory.visitAt (source model domain original reference worker quote quotas point rival ordinal).input
        (activated model domain original reference worker quote quotas point rival ordinal count).state).current = _
      rw [activated_state])
  | .inr impossible => nomatch impossible

theorem no_snapshot_precedes_the_actual_paid_scan_visit (visit : Nat)
    (early : visit < arrival (Deployment.paidFinal model domain original reference worker quote quotas point rival)) :
    available model domain original reference worker quote quotas point rival ordinal visit = none :=
  if_neg (Nat.not_le.mpr early)

theorem each_actual_prefix_extends_to_the_same_fixed_source (count : Nat) :
    full model domain original reference worker quote quotas point rival ordinal =
      Splice.install (cutPoint model domain original reference worker quote quotas point rival ordinal count) rival
        ((Deployment.future model domain original reference worker quote quotas point rival ordinal).drop count) := by
  change Splice.install _ rival ((Deployment.future model domain original reference worker quote quotas point rival ordinal).take _) = _
  rw [List.take_of_length_le (Deployment.future_fits_the_original_remaining_window model domain original reference worker quote quotas point rival ordinal)]
  change List.foldl _ _ _ = List.foldl _ (List.foldl _ _ _) _
  rw [←List.foldl_append,List.take_append_drop]

theorem each_actual_cut_is_the_same_visit_in_the_fixed_source (count : Nat) :
    (ProgrammeHistory.visitAt (source model domain original reference worker quote quotas point rival ordinal).input
      (arrival (cutPoint model domain original reference worker quote quotas point rival ordinal count))).current =
    (ProgrammeHistory.visitAt (cutPoint model domain original reference worker quote quotas point rival ordinal count).source.input
      (arrival (cutPoint model domain original reference worker quote quotas point rival ordinal count))).current := by
  change (ProgrammeHistory.visitAt (full model domain original reference worker quote quotas point rival ordinal).source.input _).current = _
  rw [each_actual_prefix_extends_to_the_same_fixed_source model domain original reference worker quote quotas point rival ordinal count]
  exact Machine.actual_prefix_from_events (cutPoint model domain original reference worker quote quotas point rival ordinal count).source.input
    (Splice.install (cutPoint model domain original reference worker quote quotas point rival ordinal count) rival
      ((Deployment.future model domain original reference worker quote quotas point rival ordinal).drop count)).source.input rfl rfl
    (arrival (cutPoint model domain original reference worker quote quotas point rival ordinal count))
    (Installation.Chain.fold_keeps_every_prior_raw_event (model := model) _ rival _) _ (Nat.le_refl _)

theorem each_actual_prefix_preserves_its_entire_native_financial_account (count visit : Nat)
    (earlier : visit ≤ arrival (cutPoint model domain original reference worker quote quotas point rival ordinal count)) :
    Native.Coupling.Match model.source.code (cutPoint model domain original reference worker quote quotas point rival ordinal count).source.input
      (source model domain original reference worker quote quotas point rival ordinal).input
      (Financial.accountAt (cutPoint model domain original reference worker quote quotas point rival ordinal count).source.input visit)
      (Financial.accountAt (source model domain original reference worker quote quotas point rival ordinal).input visit) := by
  change Native.Coupling.Match _ _ (full model domain original reference worker quote quotas point rival ordinal).source.input _
    (Financial.accountAt (full model domain original reference worker quote quotas point rival ordinal).source.input visit)
  rw [each_actual_prefix_extends_to_the_same_fixed_source model domain original reference worker quote quotas point rival ordinal count]
  exact Installation.Chain.fold_keeps_the_complete_native_financial_prefix (model := model) _ rival _ visit earlier

theorem each_live_stage_is_the_next_actual_cut (count : Nat)
    (inside : count < (Deployment.future model domain original reference worker quote quotas point rival ordinal).length) :
    arrival (cutPoint model domain original reference worker quote quotas point rival ordinal (count+1)) =
      arrival (cutPoint model domain original reference worker quote quotas point rival ordinal count)+1 := by
  change arrival (Splice.install _ rival ((Deployment.future model domain original reference worker quote quotas point rival ordinal).take (count+1))) = _
  rw [List.take_succ_eq_append_getElem inside]
  unfold Splice.install
  rw [List.foldl_append]
  rfl

theorem the_same_root_consumes_each_actual_cut_full_account_and_literal_next (count : Nat) :
    let current := activated model domain original reference worker quote quotas point rival ordinal count
    (ProgrammeHistory.visitAt (source model domain original reference worker quote quotas point rival ordinal).input
      (arrival (cutPoint model domain original reference worker quote quotas point rival ordinal count))).current =
      (ProgrammeHistory.visitAt (cutPoint model domain original reference worker quote quotas point rival ordinal count).source.input
        (arrival (cutPoint model domain original reference worker quote quotas point rival ordinal count))).current ∧
    Native.Coupling.Match model.source.code (cutPoint model domain original reference worker quote quotas point rival ordinal count).source.input
      (source model domain original reference worker quote quotas point rival ordinal).input
      (Financial.accountAt (cutPoint model domain original reference worker quote quotas point rival ordinal count).source.input
        (arrival (cutPoint model domain original reference worker quote quotas point rival ordinal count)))
      (Financial.accountAt (source model domain original reference worker quote quotas point rival ordinal).input
        (arrival (cutPoint model domain original reference worker quote quotas point rival ordinal count))) ∧
    HEq ((facade model domain original reference worker quote quotas point rival ordinal).readoutAt current .search)
      (current.tick.generated.projectionOutcome (.component ())) ∧
    HEq current.tick.generated.wholeLedgerWriteBack
      (current.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current.current.visit.current) ∧
    ((count < (Deployment.future model domain original reference worker quote quotas point rival ordinal).length) →
      current.tick.nextCurrent = (activated model domain original reference worker quote quotas point rival ordinal (count+1)).current) := by
  have rooted := (facade model domain original reference worker quote quotas point rival ordinal).readoutAt_factorizes
    (activated model domain original reference worker quote quotas point rival ordinal count) .search
  refine ⟨each_actual_cut_is_the_same_visit_in_the_fixed_source model domain original reference worker quote quotas point rival ordinal count,
    each_actual_prefix_preserves_its_entire_native_financial_account model domain original reference worker quote quotas point rival ordinal count _ (Nat.le_refl _),
    rooted.2.2.2.1,rooted.2.2.1,?_⟩
  intro inside
  apply rooted.2.2.2.2.trans
  change (facade model domain original reference worker quote quotas point rival ordinal).process.stateAt
    (Nat.succ ((facade model domain original reference worker quote quotas point rival ordinal).seed.advance
      (arrival (cutPoint model domain original reference worker quote quotas point rival ordinal count))).state) = _
  have state (n : Nat) : ((facade model domain original reference worker quote quotas point rival ordinal).seed.advance n).state = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  change (facade model domain original reference worker quote quotas point rival ordinal).process.stateAt
    (Nat.succ ((facade model domain original reference worker quote quotas point rival ordinal).seed.advance
      (arrival (cutPoint model domain original reference worker quote quotas point rival ordinal count))).state) =
    (facade model domain original reference worker quote quotas point rival ordinal).process.stateAt
      (((facade model domain original reference worker quote quotas point rival ordinal).seed.advance
        (arrival (cutPoint model domain original reference worker quote quotas point rival ordinal (count+1)))).state)
  rw [state,state,each_live_stage_is_the_next_actual_cut model domain original reference worker quote quotas point rival ordinal count inside]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse.Deployment.Path
