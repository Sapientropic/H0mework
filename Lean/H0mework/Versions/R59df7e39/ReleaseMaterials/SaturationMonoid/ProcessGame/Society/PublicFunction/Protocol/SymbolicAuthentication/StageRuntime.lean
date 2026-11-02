import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageBudget

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageRuntime

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor bound.source.code) (stages : List (EventHistory.Stage (code := bound.source.code)))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

abbrev final := EventHistory.execute start stages
abbrev actualBound := LocalContentRuntime.native bound (final bound start stages)
abbrev actualInput := (final bound start stages).entry
abbrev ordinal := EventStep.boundary (final bound start stages)

structure Census where
  private mk ::
  rows : List (StageTrace.Record (code := bound.source.code))
  rows_exact : rows = StageTrace.records start stages
  requests : List (List (ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument × Bool))
  requests_exact : requests = rows.map StageTrace.audit
  capacity : Finset (Fin bound.source.code.sites)
  capacity_exact : capacity = StageBudget.capacityKeys vocabulary start stages
  evidence : Finset (Fin bound.source.code.sites)
  evidence_exact : evidence = StageBudget.evidenceKeys vocabulary start stages

def generate : Census bound start stages vocabulary :=
  ⟨StageTrace.records start stages, rfl, (StageTrace.records start stages).map StageTrace.audit, rfl,
    StageBudget.capacityKeys vocabulary start stages, rfl, StageBudget.evidenceKeys vocabulary start stages, rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (actualBound bound start stages).source.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (actualBound bound start stages).source.input (ordinal bound start stages)).current →
      Census bound start stages vocabulary
  project := fun _ {_} _ _ _own => generate bound start stages vocabulary

def root := (Feedback.Authority.Runtime.root (actualBound bound start stages)
  (actualInput bound start stages) rfl rfl).withProjectionCoface
    (projectionLaw bound start stages vocabulary)

theorem original_emitter_root_is_preserved :
    (root bound start stages vocabulary).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (actualBound bound start stages).source.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt
    (ProgrammeSource.N (actualBound bound start stages).source.input) :=
  ⟨ProgrammeSource.V (actualBound bound start stages).source.input,
    root bound start stages vocabulary,
    ProgrammeHistory.temporalVisit (actualBound bound start stages).source.input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (actualBound bound start stages).source.input) where
  State := Nat
  stateAt := stateAt bound start stages vocabulary
  stateAt_injective := by
    intro first second same
    have labels := congrArg (fun state : SourceNativeLivingRootCurrentAt
        (ProgrammeSource.N (actualBound bound start stages).source.input) =>
      (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (actualBound bound start stages).source.input first).current =
        (ProgrammeHistory.visitAt (actualBound bound start stages).source.input second).current :=
      eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective _ currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : Feedback.Authority.Runtime.Face)
  | deviation

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (actualBound bound start stages).source.input) where
  process := process bound start stages vocabulary
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous =>
      (Feedback.Authority.Runtime.facade (actualBound bound start stages)
        (actualInput bound start stages) rfl rfl).componentAt
        (Feedback.Authority.Runtime.facade (actualBound bound start stages)
          (actualInput bound start stages) rfl rfl).seed previous
    | .deviation => projectionLaw bound start stages vocabulary
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((Feedback.Authority.Runtime.facade (actualBound bound start stages)
        (actualInput bound start stages) rfl rfl).installationAt
        (Feedback.Authority.Runtime.facade (actualBound bound start stages)
          (actualInput bound start stages) rfl rfl).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (Feedback.Authority.Runtime.root (actualBound bound start stages)
            (actualInput bound start stages) rfl rfl).toAuthoritativeRoot.source
          (projectionLaw bound start stages vocabulary))
    | deviation =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (Feedback.Authority.Runtime.root (actualBound bound start stages)
          (actualInput bound start stages) rfl rfl).toAuthoritativeRoot.source
        (projectionLaw bound start stages vocabulary)
  projectionAt := fun _ face => match face with
    | .previous previous => (Feedback.Authority.Runtime.facade (actualBound bound start stages)
        (actualInput bound start stages) rfl rfl).projectionAt
        (Feedback.Authority.Runtime.facade (actualBound bound start stages)
          (actualInput bound start stages) rfl rfl).seed previous
    | .deviation => ()

def activated (ordinal : Nat) : LivingRuntimeState (process bound start stages vocabulary) :=
  (facade bound start stages vocabulary).seed.advance ordinal

theorem activated_state_is_the_generated_ordinal (ordinal : Nat) :
    (activated bound start stages vocabulary ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
    change Nat.succ (activated bound start stages vocabulary ordinal).state = Nat.succ ordinal
    exact congrArg Nat.succ ih

def rooted : Census bound start stages vocabulary :=
  match (facade bound start stages vocabulary).readoutAt
      (activated bound start stages vocabulary (ordinal bound start stages)) .deviation with
  | .inl value => value.2 (by
      change (ProgrammeHistory.visitAt (actualBound bound start stages).source.input
        (activated bound start stages vocabulary (ordinal bound start stages)).state).current = _
      rw [activated_state_is_the_generated_ordinal])
  | .inr impossible => nomatch impossible

theorem rooted_eq_generated : rooted bound start stages vocabulary = generate bound start stages vocabulary := rfl

def authority : Feedback.Authority.Disposition (actualBound bound start stages) (actualInput bound start stages)
    (final bound start stages).cut rfl rfl :=
  match (facade bound start stages vocabulary).readoutAt
      (activated bound start stages vocabulary (ordinal bound start stages)) (.previous .responsibilities) with
  | .inl payload => payload.2 (final bound start stages).cut (by
      change (ProgrammeHistory.visitAt (actualBound bound start stages).source.input
        (activated bound start stages vocabulary (ordinal bound start stages)).state).current = _
      rw [activated_state_is_the_generated_ordinal])
  | .inr impossible => nomatch impossible

theorem the_final_root_consumes_actual_budget_native_responsibility_ledger_and_next :
    let runtime := activated bound start stages vocabulary (ordinal bound start stages)
    (rooted bound start stages vocabulary).evidence ⊆ (rooted bound start stages vocabulary).capacity ∧
      (authority bound start stages vocabulary).current = Native.Authority.fullGenerate (actualBound bound start stages)
        ((final bound start stages).source.history.length + 1 + (final bound start stages).cut) ∧
      HEq ((facade bound start stages vocabulary).readoutAt runtime .deviation)
        (runtime.tick.generated.projectionOutcome (.component ())) ∧
      HEq ((facade bound start stages vocabulary).readoutAt runtime (.previous .responsibilities))
        (runtime.tick.generated.projectionOutcome (.inherited (.component ()))) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (facade bound start stages vocabulary).process.stateAt
        ((facade bound start stages vocabulary).process.successor runtime.state) := by
  have installed := (facade bound start stages vocabulary).readoutAt_factorizes
    (activated bound start stages vocabulary (ordinal bound start stages)) .deviation
  have inherited := (facade bound start stages vocabulary).readoutAt_factorizes
    (activated bound start stages vocabulary (ordinal bound start stages)) (.previous .responsibilities)
  exact ⟨StageBudget.actual_evidence_keys_are_within_the_generated_capacity_budget vocabulary start stages,
    (authority bound start stages vocabulary).current_exact, installed.2.2.2.1, inherited.2.2.2.1,
    installed.2.2.1, installed.2.2.2.2⟩

theorem every_rooted_receipt_uses_the_final_sources_financial_inventory
    (row : StageTrace.Record (code := bound.source.code)) (inside : row ∈ (rooted bound start stages vocabulary).rows) :
    (Financial.inventoryAt (final bound start stages).source.input
      (ProgrammeHistory.visitAt (final bound start stages).source.input (EventStep.boundary row.cursor))).filterMap
      (Financial.InstructionOrigin.instruction? (final bound start stages).source.input) = StageTrace.items row := by
  rw [(rooted bound start stages vocabulary).rows_exact] at inside
  exact StageTrace.final_financial_inventory_is_the_original_record_items start stages row inside

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageRuntime
