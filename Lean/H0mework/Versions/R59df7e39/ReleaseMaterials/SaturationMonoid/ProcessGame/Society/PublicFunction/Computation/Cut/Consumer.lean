import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Cut
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Splice

set_option autoImplicit false
set_option maxRecDepth 32768
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Cut.Consumer
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {Party Good Port Technology Instrument Row : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (worker : Fin model.source.code.sites) (holds : Row → Prop) (rows : List Row)
  (tariff : Tariff (Party := Party) (Good := Good) (Port := Port)
    (Technology := Mandate.State Party Technology) (Instrument := Instrument) Row)
  (point : View (code := model.source.code)) (rival : Opponent model.source.code)
  (execution : Trace worker holds tariff rival point rows)

abbrev final := execution.final.point
abbrev source := (final model worker holds rows tariff point rival execution).source
abbrev endAt := arrival (final model worker holds rows tariff point rival execution)
abbrev bound := Replanning.native model (final model worker holds rows tariff point rival execution)

theorem the_final_source_is_generated_only_by_actual_cut_takeovers :
    final model worker holds rows tariff point rival execution =
      Splice.install point.point rival execution.rules :=
  execution.final_is_generated_only_by_its_actual_single_cut_rules

theorem all_actual_past_events_survive_the_complete_scan
    (ordinal : Nat) (earlier : ordinal < arrival point.point) :
    ProgrammeSource.rawEvent (source model worker holds rows tariff point rival execution).input
      (ProgrammeHistory.visitAt point.point.source.input ordinal).current =
    ProgrammeSource.rawEvent point.point.source.input (ProgrammeHistory.visitAt point.point.source.input ordinal).current := by
  change ProgrammeSource.rawEvent (final model worker holds rows tariff point rival execution).source.input _ = _
  rw [the_final_source_is_generated_only_by_actual_cut_takeovers]
  exact Installation.Chain.fold_keeps_every_prior_raw_event (model := model) point.point rival
    execution.rules ordinal earlier

theorem all_old_native_financial_responsibilities_survive_the_complete_scan
    (ordinal : Nat) (earlier : ordinal ≤ arrival point.point) :
    Native.Coupling.Match model.source.code point.point.source.input (source model worker holds rows tariff point rival execution).input
      (Financial.accountAt point.point.source.input ordinal)
      (Financial.accountAt (source model worker holds rows tariff point rival execution).input ordinal) := by
  exact Eq.mpr (congrArg (fun cursor : Cursor model.source.code =>
      Native.Coupling.Match model.source.code point.point.source.input cursor.source.input
        (Financial.accountAt point.point.source.input ordinal) (Financial.accountAt cursor.source.input ordinal))
    (the_final_source_is_generated_only_by_actual_cut_takeovers model worker holds rows tariff point rival execution))
    (Installation.Chain.fold_keeps_the_complete_native_financial_prefix (model := model) point.point rival
      execution.rules ordinal earlier)

def atPrefix (count : Nat) := Splice.install point.point rival (execution.rules.take count)

private theorem final_extends_each_actual_prefix (count : Nat) :
    final model worker holds rows tariff point rival execution = Splice.install (atPrefix model worker holds rows tariff point rival execution count) rival
      (execution.rules.drop count) := by
  rw [the_final_source_is_generated_only_by_actual_cut_takeovers]
  simp only [atPrefix,Splice.install]
  rw [← List.foldl_append,List.take_append_drop]

theorem every_actual_cut_prefix_keeps_its_full_financial_account
    (count ordinal : Nat) (earlier : ordinal ≤ arrival (atPrefix model worker holds rows tariff point rival execution count)) :
    Native.Coupling.Match model.source.code (atPrefix model worker holds rows tariff point rival execution count).source.input
      (source model worker holds rows tariff point rival execution).input
      (Financial.accountAt (atPrefix model worker holds rows tariff point rival execution count).source.input ordinal)
      (Financial.accountAt (source model worker holds rows tariff point rival execution).input ordinal) := by
  exact Eq.mpr (congrArg (fun cursor : Cursor model.source.code =>
      Native.Coupling.Match model.source.code (atPrefix model worker holds rows tariff point rival execution count).source.input cursor.source.input
        (Financial.accountAt (atPrefix model worker holds rows tariff point rival execution count).source.input ordinal)
        (Financial.accountAt cursor.source.input ordinal))
    (final_extends_each_actual_prefix model worker holds rows tariff point rival execution count))
    (Installation.Chain.fold_keeps_the_complete_native_financial_prefix (model := model)
      (atPrefix model worker holds rows tariff point rival execution count) rival
      (execution.rules.drop count) ordinal earlier)


theorem every_released_blocker_names_its_exact_actual_cut_prefix
    (stopped : Trace.Blocker (worker := worker) (rival := rival) rows)
    (found : execution.blocker = some stopped) :
    stopped.position ≤ execution.rules.length ∧
      stopped.point.point = atPrefix model worker holds rows tariff point rival execution stopped.position :=
  execution.every_blocker_is_located_at_its_actual_rule_prefix stopped found

def available (ordinal : Nat) : Option (Inspection holds rows) :=
  if endAt model worker holds rows tariff point rival execution ≤ ordinal then execution.result else none

def failure (ordinal : Nat) : Option (Trace.Blocker (worker := worker) (rival := rival) rows) :=
  if endAt model worker holds rows tariff point rival execution ≤ ordinal then execution.blocker else none

theorem no_result_precedes_its_actual_activation_and_payment_visits
    (ordinal : Nat) (early : ordinal < endAt model worker holds rows tariff point rival execution) :
    available model worker holds rows tariff point rival execution ordinal = none := if_neg (Nat.not_le.mpr early)

theorem every_released_row_inspection_has_actual_paid_activations
    (ordinal : Nat) (inspection : Inspection holds rows)
    (released : available model worker holds rows tariff point rival execution ordinal = some inspection) :
    endAt model worker holds rows tariff point rival execution ≤ ordinal ∧
      execution.allRowsActivatedAndPaid := by
  unfold available at released
  split at released
  · rename_i arrived
    exact ⟨arrived,execution.a_released_inspection_has_only_actual_paid_activations inspection released⟩
  · cases released

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (source model worker holds rows tariff point rival execution).input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (ordinal : Nat) →
    current = (ProgrammeHistory.visitAt (source model worker holds rows tariff point rival execution).input ordinal).current →
      Option (Inspection holds rows) × Option (Trace.Blocker (worker := worker) (rival := rival) rows)
  project := fun _ {_} _ _ ordinal _ =>
    (available model worker holds rows tariff point rival execution ordinal,failure model worker holds rows tariff point rival execution ordinal)

def root := (Native.AuthorityRuntime.root (bound model worker holds rows tariff point rival execution)).withProjectionCoface
  (projectionLaw model worker holds rows tariff point rival execution)

theorem original_programme_root_is_preserved :
    (root model worker holds rows tariff point rival execution).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (source model worker holds rows tariff point rival execution).input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (source model worker holds rows tariff point rival execution).input) :=
  ⟨ProgrammeSource.V (source model worker holds rows tariff point rival execution).input,root model worker holds rows tariff point rival execution,
    ProgrammeHistory.temporalVisit (source model worker holds rows tariff point rival execution).input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (source model worker holds rows tariff point rival execution).input) where
  State := Nat
  stateAt := stateAt model worker holds rows tariff point rival execution
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (source model worker holds rows tariff point rival execution).input) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    exact ProgrammeHistory.visit_current_injective _ (eq_of_heq (Sigma.mk.inj labels).2)
  initial := 0
  successorAt := fun ordinal => ⟨ordinal+1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : Native.AuthorityRuntime.Face)
  | inspection

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (source model worker holds rows tariff point rival execution).input) where
  process := process model worker holds rows tariff point rival execution
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Native.AuthorityRuntime.facade (bound model worker holds rows tariff point rival execution)).componentAt
        (Native.AuthorityRuntime.facade (bound model worker holds rows tariff point rival execution)).seed previous
    | .inspection => projectionLaw model worker holds rows tariff point rival execution
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
        exact ((Native.AuthorityRuntime.facade (bound model worker holds rows tariff point rival execution)).installationAt
          (Native.AuthorityRuntime.facade (bound model worker holds rows tariff point rival execution)).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (Native.AuthorityRuntime.root (bound model worker holds rows tariff point rival execution)).toAuthoritativeRoot.source
            (projectionLaw model worker holds rows tariff point rival execution))
    | inspection =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (Native.AuthorityRuntime.root (bound model worker holds rows tariff point rival execution)).toAuthoritativeRoot.source
          (projectionLaw model worker holds rows tariff point rival execution)
  projectionAt := fun _ face => match face with
    | .previous previous => (Native.AuthorityRuntime.facade (bound model worker holds rows tariff point rival execution)).projectionAt
        (Native.AuthorityRuntime.facade (bound model worker holds rows tariff point rival execution)).seed previous
    | .inspection => ()

abbrev activated (ordinal : Nat) := (facade model worker holds rows tariff point rival execution).seed.advance ordinal

theorem activated_state (ordinal : Nat) : (activated model worker holds rows tariff point rival execution ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => exact congrArg Nat.succ ih

def read (ordinal : Nat) : Option (Inspection holds rows) ×
    Option (Trace.Blocker (worker := worker) (rival := rival) rows) :=
  match (facade model worker holds rows tariff point rival execution).readoutAt (activated model worker holds rows tariff point rival execution ordinal) .inspection with
  | .inl actual => actual.2 ordinal (by
      change (ProgrammeHistory.visitAt (source model worker holds rows tariff point rival execution).input
        (activated model worker holds rows tariff point rival execution ordinal).state).current = _
      rw [activated_state])
  | .inr impossible => nomatch impossible

theorem read_is_the_arrived_source_generated_outcome (ordinal : Nat) :
    read model worker holds rows tariff point rival execution ordinal =
      (available model worker holds rows tariff point rival execution ordinal,failure model worker holds rows tariff point rival execution ordinal) := rfl

def nativeRead (depth : Nat) : Native.Authority.Disposition (bound model worker holds rows tariff point rival execution) depth :=
  match (facade model worker holds rows tariff point rival execution).readoutAt (activated model worker holds rows tariff point rival execution (depth+1))
      (.previous .responsibilities) with
  | .inl actual => actual.2 depth (by
      change (ProgrammeHistory.visitAt (source model worker holds rows tariff point rival execution).input
        (activated model worker holds rows tariff point rival execution (depth+1)).state).current = _
      rw [activated_state])
  | .inr impossible => nomatch impossible

theorem the_same_facade_reads_the_entire_native_financial_account (depth : Nat) :
    (nativeRead model worker holds rows tariff point rival execution depth).joint.finance =
      Financial.accountAt (source model worker holds rows tariff point rival execution).input (depth+2) := by
  rw [(nativeRead model worker holds rows tariff point rival execution depth).joint_exact]
  exact (Native.generate (source model worker holds rows tariff point rival execution) depth).finance_exact

theorem inspection_payment_and_next_factor_through_one_actual_root (ordinal : Nat) :
    let current := activated model worker holds rows tariff point rival execution ordinal
    HEq ((facade model worker holds rows tariff point rival execution).readoutAt current .inspection)
      (current.tick.generated.projectionOutcome (.component ())) ∧
    HEq current.tick.generated.wholeLedgerWriteBack
      (current.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current.current.visit.current) ∧
    current.tick.nextCurrent = (activated model worker holds rows tariff point rival execution (ordinal+1)).current := by
  have rooted := (facade model worker holds rows tariff point rival execution).readoutAt_factorizes
    (activated model worker holds rows tariff point rival execution ordinal) .inspection
  exact ⟨rooted.2.2.2.1,rooted.2.2.1,rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Cut.Consumer
