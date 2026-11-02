import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Installation

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Runtime
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix

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

variable (initial : List (View (code := model.source.code)))

abbrev communicationCount := match Plan.select model domain original reference worker receiver quote quotas slots point rival ordinal with
  | none => 0
  | some plan => plan.announcements.length
abbrev parentRead := Publication.Runtime.read model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law (communicationCount model domain original reference worker receiver quote quotas slots point rival ordinal)

structure Activation where
  record : Publication.Receipt.Published model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law
  arrived : parentRead model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law = some (.published record)

def prepare : Option (Activation model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law) :=
  match actual : parentRead model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law with
  | some (.published record) => some ⟨record,actual⟩
  | _ => none

abbrev remainingWord := match prepare model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law with
  | some actual => Learning.Installation.future model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law actual.record initial
  | none => Plan.future model domain original reference worker receiver quote quotas slots point rival ordinal
def cutPoint (count : Nat) : Cursor model.source.code := match prepare model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law with
  | some actual => Learning.Installation.cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law actual.record initial count
  | none => Plan.cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal count
abbrev full := cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial (Deployment.actualHorizon model point)
abbrev source := (full model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).source
abbrev bound := Replanning.native model (full model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial)
abbrev Response := Sigma fun actual : Activation model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law =>
  Proposal.Decision model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law actual.record initial

def response : Option (Response model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial) :=
  (prepare model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law).map (fun actual => ⟨actual,Proposal.inspect model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law actual.record initial⟩)
abbrev Snapshot := Option (Publication.Receipt.Outcome model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law) × Option (Response model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial)
abbrev snapshot : Snapshot model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial := (parentRead model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law,response model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial)

def available (visit : Nat) :=
  if arrival (Plan.cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal (communicationCount model domain original reference worker receiver quote quotas slots point rival ordinal)) ≤ visit then some (snapshot model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial) else none

theorem no_learning_answer_precedes_actual_communication_even_when_recovery_is_pending
    (visit : Nat) (early : visit < arrival (Plan.cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal (communicationCount model domain original reference worker receiver quote quotas slots point rival ordinal))) :
    available model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial visit = none := if_neg (Nat.not_le.mpr early)

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (source model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (visit : Nat) →
    current = (ProgrammeHistory.visitAt (source model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).input visit).current →
      Option (Snapshot model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial)
  project := fun _ {_} _ _ visit _ =>
    available model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial visit

def root := (Native.AuthorityRuntime.root (bound model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial)).withProjectionCoface
  (projectionLaw model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial)

theorem original_programme_root_is_preserved :
    (root model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (source model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).input).toAuthoritativeRoot.toRoot := rfl

def stateAt (visit : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (source model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).input) :=
  ⟨ProgrammeSource.V (source model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).input,root model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial,
    ProgrammeHistory.temporalVisit (source model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).input visit⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (source model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).input) where
  State := Nat
  stateAt := stateAt model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (source model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).input) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    exact ProgrammeHistory.visit_current_injective _ (eq_of_heq (Sigma.mk.inj labels).2)
  initial := 0
  successorAt := fun visit => ⟨visit+1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : Native.AuthorityRuntime.Face)
  | learning

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (source model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).input) where
  process := process model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Native.AuthorityRuntime.facade (bound model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial)).componentAt
        (Native.AuthorityRuntime.facade (bound model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial)).seed previous
    | .learning => projectionLaw model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
        exact ((Native.AuthorityRuntime.facade (bound model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial)).installationAt
          (Native.AuthorityRuntime.facade (bound model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial)).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (Native.AuthorityRuntime.root (bound model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial)).toAuthoritativeRoot.source
            (projectionLaw model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial))
    | learning =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (Native.AuthorityRuntime.root (bound model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial)).toAuthoritativeRoot.source
          (projectionLaw model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial)
  projectionAt := fun _ face => match face with
    | .previous previous => (Native.AuthorityRuntime.facade (bound model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial)).projectionAt
        (Native.AuthorityRuntime.facade (bound model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial)).seed previous
    | .learning => ()

abbrev activated (count : Nat) := (facade model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).seed.advance (arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count))

theorem activated_state (count : Nat) :
    (activated model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count).state = arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count) := by
  have state (n : Nat) : ((facade model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).seed.advance n).state = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  exact state _

def read (count : Nat) : Option (Snapshot model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial) :=
  match (facade model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).readoutAt (activated model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count) .learning with
  | .inl actual => actual.2 (arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count)) (by
      change (ProgrammeHistory.visitAt (source model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).input (activated model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count).state).current = _
      rw [activated_state])
  | .inr impossible => nomatch impossible

theorem read_is_the_arrived_same_root_learning_answer (count : Nat) :
    read model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count = available model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial (arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count)) := rfl

theorem each_actual_cut_extends_to_the_same_fixed_source (count : Nat) :
    ∃ suffix, full model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial = Splice.install (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count) rival suffix := by
  cases generated : prepare model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law with
  | none =>
      refine ⟨(Plan.future model domain original reference worker receiver quote quotas slots point rival ordinal).drop count,?_⟩
      simp only [full,cutPoint,generated]
      exact Publication.Installation.each_actual_prefix_extends_to_the_same_source model domain original reference worker receiver quote quotas slots point rival ordinal count
  | some actual =>
      refine ⟨(Learning.Installation.future model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law actual.record initial).drop count,?_⟩
      simp only [full,cutPoint,generated]
      exact Learning.Installation.every_actual_prefix_extends_to_the_same_new_source model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law actual.record initial count

theorem every_actual_cut_is_the_same_current_in_the_final_source (count : Nat) :
    (ProgrammeHistory.visitAt (source model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).input (arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count))).current =
      (ProgrammeHistory.visitAt (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count).source.input (arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count))).current := by
  obtain ⟨suffix,same⟩ := each_actual_cut_extends_to_the_same_fixed_source model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count
  change (ProgrammeHistory.visitAt (full model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).source.input _).current = _
  rw [same]
  exact Machine.actual_prefix_from_events (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count).source.input
    (Splice.install (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count) rival suffix).source.input rfl rfl (arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count))
    (Distributed.Recall.Information.Agency.Protocol.Continuation.Installation.Chain.fold_keeps_every_prior_raw_event
      (model := model) _ rival _) _ (Nat.le_refl _)

theorem every_actual_cut_keeps_its_complete_native_financial_prefix (count visit : Nat)
    (earlier : visit ≤ arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count)) :
    Native.Coupling.Match model.source.code (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count).source.input (source model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).input
      (Financial.accountAt (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count).source.input visit) (Financial.accountAt (source model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).input visit) := by
  obtain ⟨suffix,same⟩ := each_actual_cut_extends_to_the_same_fixed_source model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count
  change Native.Coupling.Match _ _ (full model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).source.input _ (Financial.accountAt (full model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).source.input visit)
  rw [same]
  exact Distributed.Recall.Information.Agency.Protocol.Continuation.Installation.Chain.fold_keeps_the_complete_native_financial_prefix
    (model := model) _ rival suffix visit earlier

theorem each_live_cut_is_the_next_actual_stage (count : Nat)
    (inside : count < (remainingWord model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).length) :
    arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial (count+1)) = arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count)+1 := by
  cases generated : prepare model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law with
  | none =>
      simp only [remainingWord,generated] at inside
      simp only [cutPoint,generated]
      exact Publication.Runtime.each_live_stage_is_the_next_actual_cut model domain original reference worker receiver quote quotas slots point rival ordinal count inside
  | some actual =>
      simp only [remainingWord,generated] at inside
      simp only [cutPoint,generated]
      change arrival (Splice.install _ rival ((Learning.Installation.future model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law actual.record initial).take (count+1))) = _
      rw [List.take_succ_eq_append_getElem inside]
      unfold Splice.install
      rw [List.foldl_append]
      rfl

theorem one_root_consumes_the_actual_learning_cut_entire_ledger_and_literal_next (count : Nat) :
    let current := activated model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count
    (ProgrammeHistory.visitAt (source model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).input (arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count))).current =
      (ProgrammeHistory.visitAt (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count).source.input (arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count))).current ∧
    (∀ visit ≤ arrival (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count),
      Native.Coupling.Match model.source.code (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count).source.input (source model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).input
        (Financial.accountAt (cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count).source.input visit) (Financial.accountAt (source model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).input visit)) ∧
    HEq ((facade model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).readoutAt current .learning) (current.tick.generated.projectionOutcome (.component ())) ∧
    HEq current.tick.generated.wholeLedgerWriteBack
      (current.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current.current.visit.current) ∧
    ((count < (remainingWord model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).length) → current.tick.nextCurrent = (activated model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial (count+1)).current) := by
  have rooted := (facade model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).readoutAt_factorizes (activated model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count) .learning
  refine ⟨every_actual_cut_is_the_same_current_in_the_final_source model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count,
    every_actual_cut_keeps_its_complete_native_financial_prefix model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count,rooted.2.2.2.1,rooted.2.2.1,?_⟩
  intro inside
  apply rooted.2.2.2.2.trans
  change (facade model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).process.stateAt (Nat.succ (activated model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count).state) =
    (facade model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial).process.stateAt (activated model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial (count+1)).state
  congr 1
  rw [activated_state,activated_state,each_live_cut_is_the_next_actual_stage model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law initial count inside]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Runtime
