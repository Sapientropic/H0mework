import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Receipt

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Runtime
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

  (quotas : List Nat) (slots : Nat)

variable (point : View (code := model.source.code)) (rival : Opponent model.source.code) (ordinal : Nat)
variable (vocabulary : PublicFunction.Protocol.SymbolicAuthentication.OwnedAttestation.Vocabulary
    (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  (encoding : PublicFunction.Protocol.SymbolicAuthentication.StageTransport.Encoding (code := model.source.code))
  (law : PublicFunction.Protocol.SymbolicAuthentication.StageReception.Law model.source.code)
abbrev full := Plan.full model domain original reference worker receiver quote quotas slots point rival ordinal
abbrev source := (full model domain original reference worker receiver quote quotas slots point rival ordinal).source
abbrev bound := Replanning.native model (full model domain original reference worker receiver quote quotas slots point rival ordinal)
abbrev communicationCut := match Plan.select model domain original reference worker receiver quote quotas slots point rival ordinal with
  | none => Plan.cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal 0
  | some plan => Plan.cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal plan.announcements.length
abbrev snapshot := Receipt.generate model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law

def available (visit : Nat) :=
  if arrival (communicationCut model domain original reference worker receiver quote quotas slots point rival ordinal) ≤ visit then
    some (snapshot model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law)
  else none

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (source model domain original reference worker receiver quote quotas slots point rival ordinal).input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (visit : Nat) →
    current = (ProgrammeHistory.visitAt (source model domain original reference worker receiver quote quotas slots point rival ordinal).input visit).current →
      Option (Receipt.Outcome model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law)
  project := fun _ {_} _ _ visit _ =>
    available model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law visit

def root := (Native.AuthorityRuntime.root (bound model domain original reference worker receiver quote quotas slots point rival ordinal)).withProjectionCoface
  (projectionLaw model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law)

theorem original_programme_root_is_preserved :
    (root model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (source model domain original reference worker receiver quote quotas slots point rival ordinal).input).toAuthoritativeRoot.toRoot := rfl

def stateAt (visit : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (source model domain original reference worker receiver quote quotas slots point rival ordinal).input) :=
  ⟨ProgrammeSource.V (source model domain original reference worker receiver quote quotas slots point rival ordinal).input,root model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law,
    ProgrammeHistory.temporalVisit (source model domain original reference worker receiver quote quotas slots point rival ordinal).input visit⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (source model domain original reference worker receiver quote quotas slots point rival ordinal).input) where
  State := Nat
  stateAt := stateAt model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (source model domain original reference worker receiver quote quotas slots point rival ordinal).input) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    exact ProgrammeHistory.visit_current_injective _ (eq_of_heq (Sigma.mk.inj labels).2)
  initial := 0
  successorAt := fun visit => ⟨visit+1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : Native.AuthorityRuntime.Face)
  | publication

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (source model domain original reference worker receiver quote quotas slots point rival ordinal).input) where
  process := process model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Native.AuthorityRuntime.facade (bound model domain original reference worker receiver quote quotas slots point rival ordinal)).componentAt
        (Native.AuthorityRuntime.facade (bound model domain original reference worker receiver quote quotas slots point rival ordinal)).seed previous
    | .publication => projectionLaw model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
        exact ((Native.AuthorityRuntime.facade (bound model domain original reference worker receiver quote quotas slots point rival ordinal)).installationAt
          (Native.AuthorityRuntime.facade (bound model domain original reference worker receiver quote quotas slots point rival ordinal)).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (Native.AuthorityRuntime.root (bound model domain original reference worker receiver quote quotas slots point rival ordinal)).toAuthoritativeRoot.source
            (projectionLaw model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law))
    | publication =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (Native.AuthorityRuntime.root (bound model domain original reference worker receiver quote quotas slots point rival ordinal)).toAuthoritativeRoot.source
          (projectionLaw model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law)
  projectionAt := fun _ face => match face with
    | .previous previous => (Native.AuthorityRuntime.facade (bound model domain original reference worker receiver quote quotas slots point rival ordinal)).projectionAt
        (Native.AuthorityRuntime.facade (bound model domain original reference worker receiver quote quotas slots point rival ordinal)).seed previous
    | .publication => ()

abbrev cutPoint (count : Nat) := Plan.cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count
abbrev activated (count : Nat) := (facade model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law).seed.advance
  (arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count))

theorem activated_state (count : Nat) :
    (activated model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law count).state =
      arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count) := by
  have state (n : Nat) : ((facade model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law).seed.advance n).state = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  exact state _

def read (count : Nat) : Option (Receipt.Outcome model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law) :=
  match (facade model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law).readoutAt
    (activated model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law count) .publication with
  | .inl actual => actual.2 (arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count)) (by
      change (ProgrammeHistory.visitAt (source model domain original reference worker receiver quote quotas slots point rival ordinal).input
        (activated model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law count).state).current = _
      rw [activated_state])
  | .inr impossible => nomatch impossible


theorem read_is_the_actual_arrived_publication (count : Nat) :
    read model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law count =
      available model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law (arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count)) := rfl

def resolve (count : Nat) (incoming : PublicFunction.Protocol.SymbolicAuthentication.RequestReadback.Receipt (code := model.source.code)) :
    Option (Prefix.Choice model domain original (reserved model original worker quote quotas) reference) :=
  match read model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law count with
  | some (.published record) => if incoming = record.receipt then some record.plan.choice else none
  | _ => none

theorem the_live_resolver_requires_actual_arrival_and_the_received_same_source_choice
    (count : Nat) (incoming : PublicFunction.Protocol.SymbolicAuthentication.RequestReadback.Receipt (code := model.source.code))
    (choice : Prefix.Choice model domain original (reserved model original worker quote quotas) reference)
    (resolved : resolve model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law count incoming = some choice) :
    arrival (communicationCut model domain original reference worker receiver quote quotas slots point rival ordinal) ≤ arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count) ∧
    ∃ record : Receipt.Published model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law,
      Receipt.generate model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law = .published record ∧
      incoming = record.receipt ∧ choice = record.plan.choice ∧
      Prefix.Contract model domain original (reserved model original worker quote quotas) reference (.selected choice) := by
  unfold resolve at resolved
  rw [read_is_the_actual_arrived_publication] at resolved
  unfold available at resolved
  by_cases arrived : arrival (communicationCut model domain original reference worker receiver quote quotas slots point rival ordinal) ≤ arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count)
  · rw [if_pos arrived] at resolved
    refine ⟨arrived,?_⟩
    cases generated : Receipt.generate model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law with
    | noSelectedProgramme reason => simp only [snapshot,generated] at resolved;cases resolved
    | pending residual => simp only [snapshot,generated] at resolved;cases resolved
    | published record =>
      simp only [snapshot,generated] at resolved
      split at resolved
      · have same : choice = record.plan.choice := (Option.some.inj resolved).symm
        refine ⟨record,rfl,by assumption,same,?_⟩
        rw [same]
        exact Plan.selected_full_contract model domain original reference worker receiver quote quotas slots point rival ordinal record.plan
      · cases resolved
  · rw [if_neg arrived] at resolved
    cases resolved


theorem no_publication_precedes_its_actual_communication_visit (visit : Nat)
    (early : visit < arrival (communicationCut model domain original reference worker receiver quote quotas slots point rival ordinal)) :
    available model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law visit = none :=
  if_neg (Nat.not_le.mpr early)

theorem each_actual_prefix_extends_to_the_same_fixed_source (count : Nat) :
    full model domain original reference worker receiver quote quotas slots point rival ordinal =
      Splice.install (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count) rival
        ((Plan.future model domain original reference worker receiver quote quotas slots point rival ordinal).drop count) := by
  change Splice.install _ rival ((Plan.future model domain original reference worker receiver quote quotas slots point rival ordinal).take _) = _
  rw [List.take_of_length_le (Publication.Installation.future_fits model domain original reference worker receiver quote quotas slots point rival ordinal)]
  change List.foldl _ _ _ = List.foldl _ (List.foldl _ _ _) _
  rw [←List.foldl_append,List.take_append_drop]

theorem each_actual_cut_is_the_same_visit_in_the_fixed_source (count : Nat) :
    (ProgrammeHistory.visitAt (source model domain original reference worker receiver quote quotas slots point rival ordinal).input
      (arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count))).current =
    (ProgrammeHistory.visitAt (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count).source.input
      (arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count))).current := by
  change (ProgrammeHistory.visitAt (full model domain original reference worker receiver quote quotas slots point rival ordinal).source.input _).current = _
  rw [each_actual_prefix_extends_to_the_same_fixed_source model domain original reference worker receiver quote quotas slots point rival ordinal count]
  exact Machine.actual_prefix_from_events (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count).source.input
    (Splice.install (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count) rival
      ((Plan.future model domain original reference worker receiver quote quotas slots point rival ordinal).drop count)).source.input rfl rfl
    (arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count))
    (Installation.Chain.fold_keeps_every_prior_raw_event (model := model) _ rival _) _ (Nat.le_refl _)

theorem each_actual_prefix_preserves_its_entire_native_financial_account (count visit : Nat)
    (earlier : visit ≤ arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count)) :
    Native.Coupling.Match model.source.code (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count).source.input
      (source model domain original reference worker receiver quote quotas slots point rival ordinal).input
      (Financial.accountAt (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count).source.input visit)
      (Financial.accountAt (source model domain original reference worker receiver quote quotas slots point rival ordinal).input visit) := by
  change Native.Coupling.Match _ _ (full model domain original reference worker receiver quote quotas slots point rival ordinal).source.input _
    (Financial.accountAt (full model domain original reference worker receiver quote quotas slots point rival ordinal).source.input visit)
  rw [each_actual_prefix_extends_to_the_same_fixed_source model domain original reference worker receiver quote quotas slots point rival ordinal count]
  exact Installation.Chain.fold_keeps_the_complete_native_financial_prefix (model := model) _ rival _ visit earlier

theorem each_live_stage_is_the_next_actual_cut (count : Nat)
    (inside : count < (Plan.future model domain original reference worker receiver quote quotas slots point rival ordinal).length) :
    arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal (count+1)) =
      arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count)+1 := by
  change arrival (Splice.install _ rival ((Plan.future model domain original reference worker receiver quote quotas slots point rival ordinal).take (count+1))) = _
  rw [List.take_succ_eq_append_getElem inside]
  unfold Splice.install
  rw [List.foldl_append]
  rfl

theorem the_same_root_consumes_each_actual_cut_full_account_and_literal_next (count : Nat) :
    let current := activated model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law count
    (ProgrammeHistory.visitAt (source model domain original reference worker receiver quote quotas slots point rival ordinal).input
      (arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count))).current =
      (ProgrammeHistory.visitAt (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count).source.input
        (arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count))).current ∧
    Native.Coupling.Match model.source.code (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count).source.input
      (source model domain original reference worker receiver quote quotas slots point rival ordinal).input
      (Financial.accountAt (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count).source.input
        (arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count)))
      (Financial.accountAt (source model domain original reference worker receiver quote quotas slots point rival ordinal).input
        (arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count))) ∧
    HEq ((facade model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law).readoutAt current .publication)
      (current.tick.generated.projectionOutcome (.component ())) ∧
    HEq current.tick.generated.wholeLedgerWriteBack
      (current.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current.current.visit.current) ∧
    ((count < (Plan.future model domain original reference worker receiver quote quotas slots point rival ordinal).length) →
      current.tick.nextCurrent = (activated model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law (count+1)).current) := by
  have rooted := (facade model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law).readoutAt_factorizes
    (activated model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law count) .publication
  refine ⟨each_actual_cut_is_the_same_visit_in_the_fixed_source model domain original reference worker receiver quote quotas slots point rival ordinal count,
    each_actual_prefix_preserves_its_entire_native_financial_account model domain original reference worker receiver quote quotas slots point rival ordinal count _ (Nat.le_refl _),
    rooted.2.2.2.1,rooted.2.2.1,?_⟩
  intro inside
  apply rooted.2.2.2.2.trans
  change (facade model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law).process.stateAt
    (Nat.succ ((facade model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law).seed.advance
      (arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count))).state) = _
  have state (n : Nat) : ((facade model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law).seed.advance n).state = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  change (facade model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law).process.stateAt
    (Nat.succ ((facade model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law).seed.advance
      (arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count))).state) =
    (facade model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law).process.stateAt
      (((facade model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law).seed.advance
        (arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal (count+1)))).state)
  rw [state,state,each_live_stage_is_the_next_actual_cut model domain original reference worker receiver quote quotas slots point rival ordinal count inside]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Runtime
